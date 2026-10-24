/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Semantics.Stateful.Composition

/-!
# Compositional proof rules for stateful clients

These semantic Hoare rules generate admissibility and postcondition obligations for pure
results, calls, sequential composition and consequence. They apply before choosing a backend;
realization transports their results to native execution. Resource obligations are separate.

## Main definitions

* `Spec.Hoare`: an admissible terminating mathematical client with a postcondition.

## Main results

* `Spec.Hoare.pure`, `Spec.Hoare.call`, `Spec.Hoare.bind`, `Spec.Hoare.consequence`:
  compositional verification rules.
* `Spec.Hoare.realize`: a semantic client proof transports through any realization.
* `Spec.Hoare.link`: transport a semantic client contract across an interface implementation.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 17][CLRS2009].
-/

@[expose] public section

namespace Cslib.Stateful.Spec

universe u v w x y

variable {D : Spec.{u, v, w}} {α β : Type y}

/-- A semantic contract includes admissibility of the selected history and the postcondition. -/
def Hoare (pre : D.State → Prop) (p : D.Client α) (post : α → D.State → Prop) : Prop :=
  ∀ s, pre s → D.ValidHistory s (D.runClient s p).2.2 ∧
    post (D.runClient s p).1 (D.runClient s p).2.1

namespace Hoare

/-- Returning a value leaves the represented state unchanged. -/
theorem pure (pre : D.State → Prop) (a : α) (post : α → D.State → Prop)
    (h : ∀ s, pre s → post a s) : Hoare pre (.pure a) post :=
  fun s hs => ⟨trivial, h s hs⟩

/-- Calling an operation requires its precondition and exposes its mathematical result. -/
theorem call (pre : D.State → Prop) (o : D.Op) (post : D.Result o → D.State → Prop)
    (h : ∀ s, pre s → D.valid s o ∧ post (D.step s o).2 (D.step s o).1) :
    Hoare pre (.liftBind o fun a => .pure a) post := by
  intro s hs
  exact ⟨⟨(h s hs).1, trivial⟩, (h s hs).2⟩

/-- Sequencing exposes only the intermediate abstract postcondition to its continuation. -/
theorem bind {pre : D.State → Prop} {mid : α → D.State → Prop}
    {post : β → D.State → Prop} {p : D.Client α} {k : α → D.Client β}
    (hp : Hoare pre p mid) (hk : ∀ a, Hoare (mid a) (k a) post) :
    Hoare pre (p.bind k) post := by
  intro s hs
  obtain ⟨hv, hm⟩ := hp s hs
  obtain ⟨hv', ht⟩ := hk _ _ hm
  rw [runClient_bind]
  exact ⟨(validHistory_append _ _ _).mpr
    ⟨hv, by simpa only [run_runClient] using hv'⟩, ht⟩

/-- Strengthen preconditions and weaken postconditions without reopening a client proof. -/
theorem consequence {pre pre' : D.State → Prop} {post post' : α → D.State → Prop}
    {p : D.Client α} (h : Hoare pre p post) (hp : ∀ s, pre' s → pre s)
    (hq : ∀ a s, post a s → post' a s) : Hoare pre' p post' := by
  intro s hs
  obtain ⟨hv, ht⟩ := h s (hp s hs)
  exact ⟨hv, hq _ _ ht⟩

/-- Every native execution of a verified client satisfies its abstract postcondition. -/
theorem realize {C Trace : Type x} {exec : Execution D C Trace} (R : Realization D exec)
    {pre : D.State → Prop} {post : α → D.State → Prop} {p : D.Client α}
    (h : Hoare pre p post) {s : D.State} {c c' : C} {a : α} {traces : List Trace}
    (hp : pre s) (hr : R.rep s c) (he : Executes exec p c a c' traces) :
    ∃ s', R.rep s' c' ∧ post a s' := by
  obtain ⟨hv, ht⟩ := h s hp
  obtain ⟨ha, hr'⟩ := R.correct_client hr hv he
  exact ⟨_, hr', ha.symm ▸ ht⟩

/-- Linking preserves a client contract while existentially hiding the module representation. -/
theorem link {α : Type w} {E : Spec.{u, v, w}} (M : Module D E)
    {pre : D.State → Prop} {post : α → D.State → Prop} {p : D.Client α}
    (h : Hoare pre p post) :
    Hoare (fun e => ∃ s, pre s ∧ M.rep s e) (Stateful.link M.methods p)
      (fun a e => ∃ s, post a s ∧ M.rep s e) := by
  rintro e ⟨s, hp, hr⟩
  obtain ⟨hv, ht⟩ := h s hp
  obtain ⟨hv', ha, hr'⟩ := M.simulates_client p hr hv
  exact ⟨hv', _, ha.symm ▸ ht, hr'⟩

end Hoare
end Cslib.Stateful.Spec
