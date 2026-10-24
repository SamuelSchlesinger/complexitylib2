/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Semantics.Stateful.Module

/-!
# Composing verified interface implementations

Modules compose by substituting method bodies and composing representation relations. The
intermediate state remains hidden, so callers need not depend on either representation.
This construction shares the same semantics across all backend and resource interpretations.

## Main definitions

* `Module.id`: the identity implementation of an interface.
* `Module.comp`: composition of two verified interface implementations.

## Main results

* `Module.simulates_client`: semantic refinement lifts through an adaptive client.
* `link_comp`: composing methods agrees with consecutive linking.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 17][CLRS2009].
-/

@[expose] public section

namespace Cslib.Stateful

universe u v w

variable {D E F : Spec.{u, v, w}} {α : Type w}

namespace Module

/-- Per-operation semantic simulations lift to the whole answer-dependent client. -/
theorem simulates_client (M : Module D E) (p : D.Client α) {s : D.State} {e : E.State}
    (hr : M.rep s e) (hv : D.ValidHistory s (D.runClient s p).2.2) :
    E.ValidHistory e (E.runClient e (link M.methods p)).2.2 ∧
      (E.runClient e (link M.methods p)).1 = (D.runClient s p).1 ∧
      M.rep (D.runClient s p).2.1 (E.runClient e (link M.methods p)).2.1 := by
  induction p generalizing s e with
  | pure a => exact ⟨trivial, rfl, hr⟩
  | liftBind o k ih =>
    obtain ⟨ha, hr'⟩ := M.correct o hr hv.1
    have hm := M.valid o hr hv.1
    have ht := ih (D.step s o).2 hr' hv.2
    have heq : E.runClient e (link M.methods (.liftBind o k)) =
        E.runClient e ((M.methods o).bind fun a => link M.methods (k a)) := rfl
    rw [heq, Spec.runClient_bind]
    simp only [ha, Spec.validHistory_append, Spec.run_runClient]
    exact ⟨⟨hm, ht.1⟩, ht.2⟩

/-- Identity methods expose precisely one call and preserve the state representation. -/
def id (D : Spec.{u, v, w}) : Module D D where
  methods o := .liftBind o fun a => .pure a
  rep := Eq
  valid o hr hv := by subst hr; exact ⟨hv, trivial⟩
  correct o hr _ := by subst hr; exact ⟨rfl, rfl⟩

/-- Compose implementation proofs while hiding the intermediate representation. -/
def comp (M : Module D E) (N : Module E F) : Module D F where
  methods o := link N.methods (M.methods o)
  rep s f := ∃ e, M.rep s e ∧ N.rep e f
  valid o hr hv := by
    obtain ⟨e, hm, hn⟩ := hr
    exact (N.simulates_client (M.methods o) hn (M.valid o hm hv)).1
  correct o hr hv := by
    obtain ⟨e, hm, hn⟩ := hr
    obtain ⟨_, ha, hn'⟩ := N.simulates_client (M.methods o) hn (M.valid o hm hv)
    obtain ⟨ha', hm'⟩ := M.correct o hm hv
    exact ⟨ha.trans ha', ⟨_, hm', hn'⟩⟩

end Module

/-- Consecutive linking is the same program as linking the composed method table. -/
theorem link_comp (f : Methods D E) (g : Methods E F) (p : D.Client α) :
    link g (link f p) = link (fun o => link g (f o)) p :=
  PFunctor.FreeM.liftM_comp p f g

end Cslib.Stateful
