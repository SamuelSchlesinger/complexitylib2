/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Semantics.Stateful.Realization

/-!
# Compositional semantic implementations

A module implements one interface using operations of another. Linking uses the upstream
free-monad interpreter. Behavior proofs neither choose a computational model nor assign costs.
Realization composes representation relations and hides intermediate states existentially.
Linking uses the upstream interpreter's common universe for operation answers and client
results. Native execution itself permits an independent universe for client results.

## Main definitions

* `Methods`: operation bodies over a lower interface.
* `Module`: admissibility and representation simulation for those bodies.
* `link`: substitute lower method bodies into an adaptive client.

## Main results

* `Module.realize`: implement a module with any realization of its lower interface.
* `link_exec`, `link_exec_decompose`: exact correspondence of chunked and flattened executions.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 17][CLRS2009].
-/

@[expose] public section

namespace Cslib.Stateful

universe u v w x

variable {D E : Spec.{u, v, w}} {C τ : Type x} {α β : Type w}

/-- Interface methods are programs over another interface. -/
abbrev Methods (D E : Spec.{u, v, w}) := (o : D.Op) → E.Client (D.Result o)

/-- Substitution reuses upstream free-monad interpretation. -/
def link (methods : Methods D E) (p : D.Client α) : E.Client α := p.liftM methods

/-- Purely semantic module correctness; neither an execution model nor a cost appears. -/
structure Module (D E : Spec.{u, v, w}) where
  /-- Bodies implementing the upper interface using lower-interface calls. -/
  methods : Methods D E
  /-- The relation between upper and lower mathematical states. -/
  rep : D.State → E.State → Prop
  valid : ∀ {s e} o, rep s e → D.valid s o →
    E.ValidHistory e (E.runClient e (methods o)).2.2
  correct : ∀ {s e} o, rep s e → D.valid s o →
    (E.runClient e (methods o)).1 = (D.step s o).2 ∧
      rep (D.step s o).1 (E.runClient e (methods o)).2.1

namespace Module

variable (M : Module D E) {exec : Execution E C τ}

/-- Module realization hides the intermediate representation and composes at any backend. -/
def realize (R : Realization E exec) :
    Realization D (fun c o a c' ts => Executes exec (M.methods o) c a c' ts) where
  rep s c := ∃ e, M.rep s e ∧ R.rep e c
  total o hr hv := by
    obtain ⟨e, hM, hR⟩ := hr
    obtain ⟨c', traces, he, _⟩ := R.exists_executes (M.methods o) hR (M.valid o hM hv)
    exact ⟨_, c', traces, he⟩
  correct hr hv he := by
    obtain ⟨e, hM, hR⟩ := hr
    obtain ⟨ha, hr'⟩ := R.correct_client hR (M.valid _ hM hv) he
    obtain ⟨ha', hm'⟩ := M.correct _ hM hv
    exact ⟨ha.trans ha', ⟨_, hm', hr'⟩⟩

end Module

/-- Linking expands every module call and preserves the complete flattened backend trace. -/
theorem link_exec (methods : Methods D E) (exec : Execution E C τ)
    {p : D.Client α} {c c' : C} {a : α} {chunks : List (List τ)}
    (he : Executes (fun x o a y ts => Executes exec (methods o) x a y ts) p c a c' chunks) :
    Executes exec (link methods p) c a c' chunks.flatten := by
  induction he with
  | pure a c => exact .pure a c
  | call hm hk ih =>
    apply (executes_bind_iff exec _ _).mpr
    exact ⟨_, _, _, _, hm, ih, rfl⟩

/-- Every flattened execution also decomposes into executions of its individual method calls. -/
theorem link_exec_decompose (methods : Methods D E) (exec : Execution E C τ)
    {p : D.Client α} {c c' : C} {a : α} {ts : List τ}
    (he : Executes exec (link methods p) c a c' ts) :
    ∃ chunks,
      Executes (fun x o a y trace => Executes exec (methods o) x a y trace)
        p c a c' chunks ∧ ts = chunks.flatten := by
  induction p generalizing c ts with
  | pure b =>
    cases he
    exact ⟨[], .pure _ _, rfl⟩
  | liftBind o k ih =>
    obtain ⟨b, mid, front, back, hm, hk, ht⟩ := (executes_bind_iff exec _ _).mp he
    obtain ⟨chunks, hc, hts⟩ := ih b hk
    exact ⟨front :: chunks, .call hm hc, by simp [ht, hts]⟩

end Cslib.Stateful
