/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Semantics.Stateful.Hoare
public import Complexity.Foundations.Semantics.Stateful.Resource

/-!
# Resource contracts across stateful interfaces

A client contract combines admissibility, a postcondition and a bound on state-dependent
operation charges. Semantic modules transport these contracts using separate method budgets;
native realizations then interpret the charges as additive measures of execution evidence.
This supports proofs at several interface levels without choosing a backend in the client proof.

These are operation-cost contracts. Pure results and host-language continuations incur no charge
in this interpretation. A total machine-time theorem additionally needs certificates for the
controller, argument preparation and result decoding. Existence of native executions does not
assert that every execution of a nondeterministic backend terminates.

## Main definitions

* `Spec.CostHoare`: a semantic client contract with an initial-state-dependent budget.
* `Module.ChargeBound`: lower method costs are bounded by upper operation charges.

## Main results

* `Spec.CostHoare.bind`: compose contracts using an intermediate postcondition.
* `Module.ChargeBound.client`: transfer costs along an adaptive linked client.
* `Module.ChargeBound.comp`: compose resource certificates through hidden representations.
* `Spec.CostHoare.link`: transport a contract to a lower interface.
* `Spec.CostHoare.realize`, `Spec.CostHoare.run`: native correctness, bounds and existence.
-/

@[expose] public section

namespace Cslib.Stateful

universe u v w x y

variable {D E F : Spec.{u, v, w}} {α β : Type y}

/-- Admissibility and a postcondition, together with a bound on charged operations.
The budget is evaluated at the initial state; it does not charge pure Lean computation. -/
def Spec.CostHoare (charge : D.State → D.Op → Nat) (pre : D.State → Prop)
    (p : D.Client α) (post : α → D.State → Prop) (budget : D.State → Nat) : Prop :=
  D.Hoare pre p post ∧
    ∀ s, pre s → D.totalCost charge s (D.runClient s p).2.2 ≤ budget s

namespace Spec.CostHoare

variable {charge : D.State → D.Op → Nat} {pre : D.State → Prop}
  {post : α → D.State → Prop} {budget : D.State → Nat} {p : D.Client α}

/-- Forget the resource bound while retaining semantic correctness. -/
theorem hoare (h : CostHoare charge pre p post budget) : D.Hoare pre p post := h.1

/-- Returning a value has zero operation cost. -/
theorem pure (a : α) (h : ∀ s, pre s → post a s) :
    CostHoare charge pre (.pure a) post (fun _ => 0) :=
  ⟨Hoare.pure pre a post h, fun _ _ => Nat.le_refl 0⟩

/-- A call exposes its specified answer and charges the supplied operation budget. -/
theorem call (o : D.Op)
    {post : D.Result o → D.State → Prop}
    (h : ∀ s, pre s → D.valid s o ∧ post (D.step s o).2 (D.step s o).1) :
    CostHoare charge pre (.liftBind o fun a => .pure a) post (fun s => charge s o) :=
  ⟨Hoare.call pre o post h, fun _ _ => Nat.le_refl _⟩

/-- Compose budgets at the intermediate abstract state, retaining answer-dependent costs. -/
theorem bind {mid : α → D.State → Prop} {post : β → D.State → Prop}
    {k : α → D.Client β} {first : D.State → Nat} {next : α → D.State → Nat}
    (hp : CostHoare charge pre p mid first)
    (hk : ∀ a, CostHoare charge (mid a) (k a) post (next a))
    (hb : ∀ s, pre s → ∀ a s', mid a s' → first s + next a s' ≤ budget s) :
    CostHoare charge pre (p.bind k) post budget := by
  refine ⟨Hoare.bind hp.hoare (fun a => (hk a).hoare), ?_⟩
  intro s hs
  have hm := (hp.hoare s hs).2
  have hf := hp.2 s hs
  have hn := (hk _).2 _ hm
  rw [runClient_bind, totalCost_append, run_runClient]
  exact (Nat.add_le_add hf hn).trans (hb s hs _ _ hm)

/-- Strengthen the precondition and weaken the postcondition or budget. -/
theorem consequence {pre' : D.State → Prop} {post' : α → D.State → Prop}
    {budget' : D.State → Nat} (h : CostHoare charge pre p post budget)
    (hp : ∀ s, pre' s → pre s) (hq : ∀ a s, post a s → post' a s)
    (hb : ∀ s, pre' s → budget s ≤ budget' s) :
    CostHoare charge pre' p post' budget' :=
  ⟨h.hoare.consequence hp hq, fun s hs => (h.2 s (hp s hs)).trans (hb s hs)⟩

/-- Every supplied native execution satisfies the contract and its interpreted resource bound. -/
theorem realize {C τ : Type x} {exec : Execution D C τ} {R : Realization D exec}
    {weight : τ → Nat} (B : Bound R weight charge)
    (h : CostHoare charge pre p post budget) {s : D.State} {c c' : C}
    {a : α} {traces : List τ} (hs : pre s) (hr : R.rep s c)
    (he : Executes exec p c a c' traces) :
    (∃ s', R.rep s' c' ∧ post a s') ∧ total weight traces ≤ budget s :=
  ⟨h.hoare.realize R hs hr he, (B.client hr (h.hoare s hs).1 he).trans (h.2 s hs)⟩

/-- A represented initial state has a native execution meeting the contract and budget. -/
theorem run {C τ : Type x} {exec : Execution D C τ} {R : Realization D exec}
    {weight : τ → Nat} (B : Bound R weight charge)
    (h : CostHoare charge pre p post budget) {s : D.State} {c : C}
    (hs : pre s) (hr : R.rep s c) :
    ∃ a c' traces, Executes exec p c a c' traces ∧
      (∃ s', R.rep s' c' ∧ post a s') ∧ total weight traces ≤ budget s := by
  obtain ⟨c', traces, he, _⟩ := R.run p hr (h.hoare s hs).1
  exact ⟨_, c', traces, he, h.realize B hs hr he⟩

end Spec.CostHoare

namespace Module

/-- Per-method resource refinement, separate from the module's semantic certificate. -/
def ChargeBound (M : Module D E) (lower : E.State → E.Op → Nat)
    (upper : D.State → D.Op → Nat) : Prop :=
  ∀ {s e} o, M.rep s e → D.valid s o →
    E.totalCost lower e (E.runClient e (M.methods o)).2.2 ≤ upper s o

/-- Method budgets compose along the actual answer-dependent history of a client. -/
theorem ChargeBound.client {M : Module D E} {lower : E.State → E.Op → Nat}
    {upper : D.State → D.Op → Nat} (B : M.ChargeBound lower upper)
    {α : Type w} (p : D.Client α) {s : D.State} {e : E.State}
    (hr : M.rep s e) (hv : D.ValidHistory s (D.runClient s p).2.2) :
    E.totalCost lower e (E.runClient e (link M.methods p)).2.2 ≤
      D.totalCost upper s (D.runClient s p).2.2 := by
  induction p generalizing s e with
  | pure a => exact Nat.le_refl 0
  | liftBind o k ih =>
    obtain ⟨ha, hr'⟩ := M.correct o hr hv.1
    have hm := B o hr hv.1
    have hk := ih (D.step s o).2 hr' hv.2
    change E.totalCost lower e
      (E.runClient e ((M.methods o).bind fun a => link M.methods (k a))).2.2 ≤ _
    rw [Spec.runClient_bind, Spec.totalCost_append, Spec.run_runClient]
    simp only [ha]
    exact Nat.add_le_add hm hk

/-- Resource refinements compose while keeping the intermediate representation hidden. -/
theorem ChargeBound.comp {M : Module D E} {N : Module E F}
    {lower : F.State → F.Op → Nat} {middle : E.State → E.Op → Nat}
    {upper : D.State → D.Op → Nat} (B : M.ChargeBound middle upper)
    (C : N.ChargeBound lower middle) : (M.comp N).ChargeBound lower upper := by
  rintro s f o ⟨e, hm, hn⟩ hv
  exact (C.client (M.methods o) hn (M.valid o hm hv)).trans (B o hm hv)

/-- A method budget and a lower native certificate supply an upper native certificate. -/
theorem ChargeBound.realize {M : Module D E} {lower : E.State → E.Op → Nat}
    {upper : D.State → D.Op → Nat} (B : M.ChargeBound lower upper)
    {C τ : Type x} {exec : Execution E C τ} (R : Realization E exec)
    {weight : τ → Nat} (h : Bound R weight lower) :
    Bound (M.realize R) (total weight) upper := M.bound R h upper B

end Module

/-- Transport a client contract and its budget across an interface implementation. -/
theorem Spec.CostHoare.link {α : Type w} {M : Module D E}
    {lower : E.State → E.Op → Nat} {upper : D.State → D.Op → Nat}
    (B : M.ChargeBound lower upper)
    {pre : D.State → Prop} {post : α → D.State → Prop} {p : D.Client α}
    {budget : D.State → Nat} (h : D.CostHoare upper pre p post budget)
    (lowerBudget : E.State → Nat)
    (hb : ∀ s e, pre s → M.rep s e → budget s ≤ lowerBudget e) :
    E.CostHoare lower (fun e => ∃ s, pre s ∧ M.rep s e) (Stateful.link M.methods p)
      (fun a e => ∃ s, post a s ∧ M.rep s e) lowerBudget := by
  refine ⟨Spec.Hoare.link M h.hoare, ?_⟩
  rintro e ⟨s, hs, hr⟩
  exact (B.client p hr (h.hoare s hs).1).trans ((h.2 s hs).trans (hb s e hs hr))

end Cslib.Stateful
