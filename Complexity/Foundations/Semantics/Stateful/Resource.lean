/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Semantics.Stateful.Module

/-!
# Independent additive resource certificates

The same semantic realization admits multiple resource interpretations. Additive measures of
native evidence compose exactly; this does not model peak live space or cache replacement.
Module potentials may depend on hidden intermediate representations, which are retained as
existential witnesses rather than silently exposed to the client.

## Main definitions

* `total`: additive interpretation of a native trace.
* `Bound`: a per-operation resource certificate, separate from semantic realization.

## Main results

* `Bound.client`: resource bounds compose along an adaptive client.
* `Module.bound`: transport worst-case bounds through a semantic module.
* `Module.amortized_client`: telescope hidden-state potential through arbitrary executions.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 17][CLRS2009].
-/

@[expose] public section

namespace Cslib.Stateful

universe u v w x y

variable {D E : Spec.{u, v, w}} {C τ : Type x} {α β : Type y}

/-- An additive interpretation of recorded native executions. Only additive resources use this. -/
def total (weight : τ → Nat) : List τ → Nat
  | [] => 0
  | t :: ts => weight t + total weight ts

/-- A resource certificate is separate from the realization and can be supplied more than once. -/
def Bound {exec : Execution D C τ} (R : Realization D exec)
    (weight : τ → Nat) (charge : D.State → D.Op → Nat) : Prop :=
  ∀ {s c o a c' trace}, R.rep s c → D.valid s o → exec c o a c' trace →
    weight trace ≤ charge s o

/-- A constant charge `K` per operation totals `K` times the length of the history. -/
theorem spec_total_const (D : Spec.{u, v, w}) (K : Nat) (s : D.State) (os : List D.Op) :
    D.totalCost (fun _ _ => K) s os = os.length * K := by
  induction os generalizing s with
  | nil => simp [Spec.totalCost]
  | cons o os ih => simp [Spec.totalCost, ih, Nat.add_mul, Nat.add_comm]

/-- Under a resource certificate, every native execution of a client whose history is admissible,
from related states, has total weight at most the total charge of the specified history. -/
theorem Bound.client {exec : Execution D C τ} {R : Realization D exec}
    {weight : τ → Nat} {charge : D.State → D.Op → Nat} (B : Bound R weight charge)
    {p : D.Client α} {s : D.State} {c c' : C} {a : α} {traces : List τ}
    (hr : R.rep s c) (hv : D.ValidHistory s (D.runClient s p).2.2)
    (he : Executes exec p c a c' traces) :
    total weight traces ≤ D.totalCost charge s (D.runClient s p).2.2 := by
  induction he generalizing s with
  | pure a c => exact Nat.le_refl 0
  | call he hes ih =>
    obtain ⟨ha, hr'⟩ := R.correct hr hv.1 he
    have ht := B hr hv.1 he
    subst ha
    exact Nat.add_le_add ht (ih hr' hv.2)

/-- Existence and semantic correctness are inherited independently from the realization. -/
theorem Bound.run {exec : Execution D C τ} {R : Realization D exec}
    {weight : τ → Nat} {charge : D.State → D.Op → Nat} (B : Bound R weight charge)
    (p : D.Client α) {s : D.State} {c : C} (hr : R.rep s c)
    (hv : D.ValidHistory s (D.runClient s p).2.2) :
    ∃ c' traces, Executes exec p c (D.runClient s p).1 c' traces ∧
      R.rep (D.runClient s p).2.1 c' ∧
      total weight traces ≤ D.totalCost charge s (D.runClient s p).2.2 := by
  obtain ⟨c', traces, he, hr'⟩ := R.run p hr hv
  exact ⟨c', traces, he, hr', B.client hr hv he⟩

/-- Uniform constant per-operation bounds scale by the history length. -/
theorem Bound.client_const {exec : Execution D C τ} {R : Realization D exec}
    {weight : τ → Nat} {K : Nat} (B : Bound R weight (fun _ _ => K))
    {p : D.Client α} {s : D.State} {c c' : C} {a : α} {traces : List τ}
    (hr : R.rep s c) (hv : D.ValidHistory s (D.runClient s p).2.2)
    (he : Executes exec p c a c' traces) :
    total weight traces ≤ (D.runClient s p).2.2.length * K := by
  simpa only [spec_total_const] using B.client hr hv he

/-- Existence, correctness, and total cost for a uniform constant per-operation bound. -/
theorem Bound.run_const {exec : Execution D C τ} {R : Realization D exec}
    {weight : τ → Nat} {K : Nat} (B : Bound R weight (fun _ _ => K))
    (p : D.Client α) {s : D.State} {c : C} (hr : R.rep s c)
    (hv : D.ValidHistory s (D.runClient s p).2.2) :
    ∃ c' traces, Executes exec p c (D.runClient s p).1 c' traces ∧
      R.rep (D.runClient s p).2.1 c' ∧
      total weight traces ≤ (D.runClient s p).2.2.length * K := by
  obtain ⟨c', traces, he, hr'⟩ := R.run p hr hv
  exact ⟨c', traces, he, hr', B.client_const hr hv he⟩

namespace Module

variable (M : Module D E) {exec : Execution E C τ}

/-- A resource interpretation is transported afterwards, without changing semantic proofs. -/
theorem bound (R : Realization E exec) {weight : τ → Nat}
    {charge : E.State → E.Op → Nat} (B : Bound R weight charge)
    (budget : D.State → D.Op → Nat)
    (hbudget : ∀ {s e} o, M.rep s e → D.valid s o →
      E.totalCost charge e (E.runClient e (M.methods o)).2.2 ≤ budget s o) :
    Bound (M.realize R) (total weight) budget := by
  intro s c o a c' ts hr hv he
  obtain ⟨e, hM, hR⟩ := hr
  exact (B.client hR (M.valid o hM hv) he).trans (hbudget o hM hv)

/-- Hidden representation credit telescopes along an arbitrary adaptive upper client.
The intermediate abstract state remains existentially hidden in the conclusion. -/
theorem amortized_client (R : Realization E exec) {weight : τ → Nat}
    {lowerCharge : E.State → E.Op → Nat} (B : Bound R weight lowerCharge)
    (potential : D.State → E.State → Nat) (charge : D.State → D.Op → Nat)
    (hstep : ∀ {s e} o, M.rep s e → D.valid s o →
      E.totalCost lowerCharge e (E.runClient e (M.methods o)).2.2 +
        potential (D.step s o).1 (E.runClient e (M.methods o)).2.1 ≤
          charge s o + potential s e)
    {p : D.Client α} {s : D.State} {e : E.State} {c c' : C} {a : α}
    {chunks : List (List τ)} (hM : M.rep s e) (hR : R.rep e c)
    (hv : D.ValidHistory s (D.runClient s p).2.2)
    (he : Executes (fun x o a y ts => Executes exec (M.methods o) x a y ts)
      p c a c' chunks) :
    ∃ e', M.rep (D.runClient s p).2.1 e' ∧ R.rep e' c' ∧
      total (total weight) chunks + potential (D.runClient s p).2.1 e' ≤
        D.totalCost charge s (D.runClient s p).2.2 + potential s e := by
  induction he generalizing s e with
  | pure a c => exact ⟨e, hM, hR, Nat.le_refl _⟩
  | call hm hk ih =>
    obtain ⟨ha, hr'⟩ := R.correct_client hR (M.valid _ hM hv.1) hm
    obtain ⟨ha', hM'⟩ := M.correct _ hM hv.1
    have ht := B.client hR (M.valid _ hM hv.1) hm
    have hp := hstep _ hM hv.1
    have heq := ha.trans ha'
    subst heq
    obtain ⟨e', hMf, hRf, hbound⟩ := ih hM' hr' hv.2
    exact ⟨e', hMf, hRf, by
      simp only [total, Spec.runClient, Spec.totalCost]
      omega⟩

end Module

/-- Unit weights total the length of the trace. -/
theorem total_one (ts : List τ) : total (fun _ => 1) ts = ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [total, ih, Nat.add_comm]

/-- A unit charge per operation totals the length of the history. -/
theorem spec_total_one (D : Spec.{u, v, w}) (s : D.State) (os : List D.Op) :
    D.totalCost (fun _ _ => 1) s os = os.length := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => simp [Spec.totalCost, ih, Nat.add_comm]

/-- The total of a concatenation is the sum of the totals. -/
theorem total_append (weight : τ → Nat) (xs ys : List τ) :
    total weight (xs ++ ys) = total weight xs + total weight ys := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih => simp [total, ih, Nat.add_assoc]

/-- The total of a flattened list of chunks is the sum of the totals of the chunks. -/
theorem total_flatten (weight : τ → Nat) (chunks : List (List τ)) :
    total weight chunks.flatten = total (total weight) chunks := by
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih => simp [List.flatten, total_append, ih, total]


end Cslib.Stateful
