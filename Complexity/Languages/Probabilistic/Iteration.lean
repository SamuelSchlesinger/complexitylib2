/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Basic
public import Mathlib.Data.List.OfFn

/-!
# Bounded adaptive probabilistic iteration

`OracleComp.iterate count step initial` repeats a state-dependent program a bounded number of
times. Its invariant rule reasons only about supported transitions. A common finite seed
realizing each reachable step presents the complete loop as a deterministic fold over independent
uniform seeds. State types need not be finite. These are semantic laws; efficiency is separate.

## Main definitions

* `Cslib.OracleComp.iterate`: bounded iteration of a state-dependent program.

## Main results

* `Cslib.OracleComp.iterate_map`: a representation commuting with each step commutes with the loop.
* `Cslib.ProbComp.iterate_invariant`: supported transitions preserve the final invariant.
* `Cslib.ProbComp.eval_iterate_of_uniform`: exact evaluation from independent saved seeds.

## References

Adapted from `Languages/Probabilistic/Iteration.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the typed `PFunctor.FreeM` program interface.
-/

@[expose] public section

namespace Cslib

namespace OracleComp

universe u v

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {State : Type v}

/-- Repeat a state-dependent program a bounded number of times. -/
def iterate : ℕ → (State → OracleComp spec State) → State → OracleComp spec State
  | 0, _, initial => pure initial
  | count + 1, step, initial => iterate count step initial >>= step

@[simp] theorem iterate_zero (step : State → OracleComp spec State) (initial : State) :
    iterate 0 step initial = pure initial := rfl

theorem iterate_succ (count : ℕ) (step : State → OracleComp spec State) (initial : State) :
    iterate (count + 1) step initial = iterate count step initial >>= step := rfl

/-- A bounded loop may expose its first transition as well as its last. -/
theorem iterate_succ_bind (count : ℕ) (step : State → OracleComp spec State) (initial : State) :
    iterate (count + 1) step initial = step initial >>= iterate count step := by
  induction count generalizing initial with
  | zero => simp [iterate]
  | succ count ih => rw [iterate_succ, ih, bind_assoc]; rfl

/-- Repeating a step that leaves the initial state unchanged has no effects. -/
theorem iterate_eq_pure (count : ℕ) (step : State → OracleComp spec State) (initial : State)
    (h : step initial = pure initial) : iterate count step initial = pure initial := by
  induction count <;> simp_all [iterate]

/-- A state representation commuting with one step commutes with the complete loop. -/
theorem iterate_map {Other : Type v} (count : ℕ) (step : State → OracleComp spec State)
    (next : Other → OracleComp spec Other) (f : State → Other)
    (hstep : ∀ state, next (f state) = f <$> step state) (initial : State) :
    iterate count next (f initial) = f <$> iterate count step initial := by
  induction count with
  | zero => simp
  | succ count ih => simp only [iterate_succ, ih, bind_map_left, map_bind, hstep]

end OracleComp

namespace ProbComp

open Probability

variable {State Seed : Type}

/-- Every possible final state satisfies an invariant preserved by every supported transition. -/
theorem iterate_invariant (count : ℕ) (step : State → ProbComp State) (initial : State)
    (invariant : ℕ → State → Prop) (hinit : invariant 0 initial)
    (hpreserve : ∀ i < count, ∀ state, invariant i state →
      ∀ next ∈ (eval (step state)).support, invariant (i + 1) next) :
    ∀ state ∈ (eval (OracleComp.iterate count step initial)).support, invariant count state := by
  have htrace (i : ℕ) (hi : i ≤ count) :
      ∀ state ∈ (eval (OracleComp.iterate i step initial)).support, invariant i state := by
    induction i with
    | zero => simpa using hinit
    | succ i ih =>
      intro next hnext
      rw [OracleComp.iterate_succ, eval_bind, PMF.mem_support_bind_iff] at hnext
      obtain ⟨state, hstate, hnext⟩ := hnext
      exact hpreserve i (by lia) state (ih (by lia) state hstate) next hnext
  exact htrace count le_rfl

/-- Independent uniform seeds realize an adaptive loop when they realize each reachable step.
The invariant allows the realization law to be restricted to reachable states. -/
theorem eval_iterate_of_uniform [Fintype Seed] [Nonempty Seed]
    (count : ℕ) (step : State → ProbComp State) (initial : State) (evaluate : State → Seed → State)
    (invariant : ℕ → State → Prop) (hinit : invariant 0 initial)
    (hpreserve : ∀ i < count, ∀ state, invariant i state →
      ∀ next ∈ (eval (step state)).support, invariant (i + 1) next)
    (hlaw : ∀ i < count, ∀ state, invariant i state →
      eval (step state) = (PMF.uniformOfFintype Seed).map (evaluate state)) :
    eval (OracleComp.iterate count step initial) =
      (PMF.uniformOfFintype (Fin count → Seed)).map
        (fun seeds => (List.ofFn seeds).foldl evaluate initial) := by
  have htrace (i : ℕ) (hi : i ≤ count) : eval (OracleComp.iterate i step initial) =
      (PMF.uniformOfFintype (Fin i → Seed)).map
        (fun seeds => (List.ofFn seeds).foldl evaluate initial) := by
    induction i with
    | zero =>
      rw [OracleComp.iterate_zero, eval_pure]
      simp only [List.ofFn_zero, List.foldl_nil, Function.const_def, PMF.map_const]
    | succ i ih =>
      rw [OracleComp.iterate_succ, eval_bind]
      trans (eval (OracleComp.iterate i step initial)).bind
        (fun state => (PMF.uniformOfFintype Seed).map (evaluate state))
      · apply PMF.bind_congr_on_support
        intro state hstate
        exact hlaw i (by lia) state (iterate_invariant i step initial invariant hinit
          (fun j hj => hpreserve j (by lia)) state hstate)
      · rw [ih (by lia), ← PMF.uniformOfFintype_map_equiv
          ((Equiv.prodComm (Fin i → Seed) Seed).trans (Fin.snocEquiv (fun _ => Seed))),
          PMF.map_comp, ← PMF.uniformOfFintype_prod]
        simp only [PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def,
          Fin.snocEquiv, Equiv.prodComm, Equiv.trans_apply, Equiv.coe_fn_mk,
          List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, Prod.swap,
          List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact htrace count le_rfl

end ProbComp

end Cslib
