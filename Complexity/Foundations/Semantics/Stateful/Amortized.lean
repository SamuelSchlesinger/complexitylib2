/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Semantics.Stateful.Resource

/-!
# Amortized resource certificates over native executions

Potential credit can depend on both the mathematical state and the hidden concrete state.
This layer attaches a potential inequality to an existing semantic realization; it does not
modify execution or assign a machine cost to pure Lean computation. Endpoint credit is retained
on the left of the bound, avoiding truncated subtraction.

## Main definitions

* `Amortized`: a separate native-resource potential certificate.

## Main results

* `Amortized.client`: every admissible adaptive execution satisfies the telescoping bound.
* `Amortized.exists_executes`: existence, correctness and the potential bound for an admissible
  client.
* `Amortized.client_const`, `Amortized.exists_executes_const`: specialization to uniform constant
  amortized charges.
* `Amortized.of_bound`, `Amortized.of_worstCase`: derive potential certificates from independent
  worst-case bounds.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 17][CLRS2009].
-/

@[expose] public section

namespace Cslib.Stateful

universe u v w x y

variable {D : Spec.{u, v, w}} {C Trace : Type x} {α : Type y}
  {exec : Execution D C Trace}

/-- Potential inequalities concern actual native evidence and may retain hidden-state credit. -/
structure Amortized (R : Realization D exec) (weight : Trace → Nat)
    (potential : D.State → C → Nat) (charge : D.State → D.Op → Nat) : Prop where
  step : ∀ {s c o a c' trace}, R.rep s c → D.valid s o → exec c o a c' trace →
    weight trace + potential (D.step s o).1 c' ≤ charge s o + potential s c

namespace Amortized

variable {R : Realization D exec} {weight : Trace → Nat} {potential : D.State → C → Nat}
  {charge : D.State → D.Op → Nat} (A : Amortized R weight potential charge)

include A in
/-- Adaptive clients retain both initial and final representation credit. -/
theorem client {p : D.Client α} {s : D.State} {c c' : C} {a : α} {traces : List Trace}
    (hr : R.rep s c) (hv : D.ValidHistory s (D.runClient s p).2.2)
    (he : Executes exec p c a c' traces) :
    total weight traces + potential (D.runClient s p).2.1 c' ≤
      D.totalCost charge s (D.runClient s p).2.2 + potential s c := by
  induction he generalizing s with
  | pure a c => exact Nat.le_refl _
  | call he hes ih =>
    obtain ⟨ha, hr'⟩ := R.correct hr hv.1 he
    have hs := A.step hr hv.1 he
    subst ha
    have ht := ih hr' hv.2
    simp only [total_cons, Spec.runClient_liftBind, Spec.totalCost_cons]
    omega

include A in
/-- Existence and semantic correctness are inherited independently from the realization. -/
theorem exists_executes (p : D.Client α) {s : D.State} {c : C} (hr : R.rep s c)
    (hv : D.ValidHistory s (D.runClient s p).2.2) :
    ∃ c' traces, Executes exec p c (D.runClient s p).1 c' traces ∧
      R.rep (D.runClient s p).2.1 c' ∧
      total weight traces + potential (D.runClient s p).2.1 c' ≤
        D.totalCost charge s (D.runClient s p).2.2 + potential s c := by
  obtain ⟨c', traces, he, hr'⟩ := R.exists_executes p hr hv
  exact ⟨c', traces, he, hr', A.client hr hv he⟩

/-- Adaptive client potential bound for a uniform constant per-operation amortized charge. -/
theorem client_const {K : Nat} (A : Amortized R weight potential (fun _ _ => K))
    {p : D.Client α} {s : D.State} {c c' : C} {a : α} {traces : List Trace}
    (hr : R.rep s c) (hv : D.ValidHistory s (D.runClient s p).2.2)
    (he : Executes exec p c a c' traces) :
    total weight traces + potential (D.runClient s p).2.1 c' ≤
      (D.runClient s p).2.2.length * K + potential s c := by
  simpa only [Spec.totalCost_const] using A.client hr hv he

/-- Existence, correctness, and potential bound for a uniform constant amortized charge. -/
theorem exists_executes_const {K : Nat} (A : Amortized R weight potential (fun _ _ => K))
    (p : D.Client α) {s : D.State} {c : C} (hr : R.rep s c)
    (hv : D.ValidHistory s (D.runClient s p).2.2) :
    ∃ c' traces, Executes exec p c (D.runClient s p).1 c' traces ∧
      R.rep (D.runClient s p).2.1 c' ∧
      total weight traces + potential (D.runClient s p).2.1 c' ≤
        (D.runClient s p).2.2.length * K + potential s c := by
  obtain ⟨c', traces, he, hr'⟩ := R.exists_executes p hr hv
  exact ⟨c', traces, he, hr', A.client_const hr hv he⟩

/-- Worst-case certificates give potential certificates whenever their charges satisfy the
abstract potential inequality. -/
theorem of_bound {cost : D.State → D.Op → Nat} (B : Bound R weight cost)
    (potential : D.State → Nat) (charge : D.State → D.Op → Nat)
    (h : ∀ s o, D.valid s o →
      cost s o + potential (D.step s o).1 ≤ charge s o + potential s) :
    Amortized R weight (fun s _ => potential s) charge where
  step hr hv he := (Nat.add_le_add_right (B hr hv he) _).trans (h _ _ hv)

/-- A worst-case bound is exactly a zero-potential certificate. -/
theorem of_worstCase (B : Bound R weight charge) :
    Amortized R weight (fun _ _ => 0) charge where
  step hr hv he := by simpa using B hr hv he

end Amortized
end Cslib.Stateful
