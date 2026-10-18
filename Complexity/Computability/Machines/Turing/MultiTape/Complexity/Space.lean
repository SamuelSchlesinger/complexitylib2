/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Space
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.ChoiceTable
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Testing the steps of views in polynomial time

The step relation of the views of a machine with finitely many states
(`Turing.MultiTapeNTM.ViewStep`) is decided by `Turing.MultiTapeNTM.viewStepB`: a halted view
steps only to itself, and a running view to the summarized result of one of the finitely many
actions its transition relation permits for its control and read symbols. The test is
polynomial-time in the encoded pair of views: it branches on the finite key of the first view,
and each branch compares the second view with the results of a fixed finite list of fixed actions.

## Main definitions

* `Turing.MultiTapeNTM.viewStepB`: the Boolean step test of views.

## Main results

* `Turing.MultiTapeNTM.viewStepB_iff`: the test decides `Turing.MultiTapeNTM.ViewStep`.
* `Turing.MultiTapeNTM.computableTidilyInPolyTime_viewStepB`: the test is polynomial-time.
-/

@[expose] public section

namespace Turing

open MultiTapeTM

namespace MultiTapeTM.ComputableTidilyInPolyTime

/-- The output summary is polynomial-time on raw words. -/
@[fun_prop]
theorem outputClass : ComputableTidilyInPolyTime Turing.outputClass encBits encBits := by
  have h : Turing.outputClass = fun word : List Bool =>
      if decide (word = []) then [] else if decide (word = [true]) then [true] else [false] := by
    funext word
    unfold Turing.outputClass
    split_ifs <;> simp_all
  rw [h]
  fun_prop

end MultiTapeTM.ComputableTidilyInPolyTime

namespace MultiTapeNTM

variable {k : ℕ} {State : Type} [Finite State] (ntm : MultiTapeNTM k Bool State)

open scoped Classical in
/-- **The step test of views.** -/
noncomputable def viewStepB (views : FiniteCfg k Bool State × FiniteCfg k Bool State) : Bool :=
  match views.1.state with
  | none => decide (views.2 = views.1)
  | some state => (ntm.actions state views.1.inputSymbol views.1.workTapeSymbols).any
      fun action => decide (views.2 = (views.1.step action).summary)

/-- The test decides the steps of views. -/
theorem viewStepB_iff {finite next : FiniteCfg k Bool State} :
    ntm.viewStepB (finite, next) = true ↔ ntm.ViewStep finite next := by
  unfold viewStepB ViewStep
  rcases finite.state with _ | state
  · simp
  · simp only [List.any_eq_true, decide_eq_true_eq, mem_actions]

/-- The summary of a view is polynomial-time. -/
theorem computableTidilyInPolyTime_summary :
    ComputableTidilyInPolyTime (FiniteCfg.summary (k := k) (State := State)) encFiniteCfg
      encFiniteCfg := by
  unfold FiniteCfg.summary
  fun_prop

/-- **The step test is polynomial-time** in the encoded pair of views. -/
theorem computableTidilyInPolyTime_viewStepB :
    ComputableTidilyInPolyTime ntm.viewStepB (encPair encFiniteCfg encFiniteCfg) encBool := by
  classical
  -- branch on the finite key of the first view
  let key (views : FiniteCfg k Bool State × FiniteCfg k Bool State) :
      Option State × Option Bool × (Fin k → Option Bool) :=
    (views.1.state, views.1.inputSymbol, views.1.workTapeSymbols)
  let branch (tag : Option State × Option Bool × (Fin k → Option Bool))
      (views : FiniteCfg k Bool State × FiniteCfg k Bool State) : Bool :=
    match tag.1 with
    | none => decide (views.2 = views.1)
    | some state => (ntm.actions state tag.2.1 tag.2.2).any
        fun action => decide (views.2 = (views.1.step action).summary)
  have heq : ntm.viewStepB = fun views => branch (key views) views := by
    funext views
    rfl
  have hfst := ComputableTidilyInPolyTime.fst (encFiniteCfg (k := k) (State := State))
    (encFiniteCfg (k := k) (State := State))
  have hsnd := ComputableTidilyInPolyTime.snd (encFiniteCfg (k := k) (State := State))
    (encFiniteCfg (k := k) (State := State))
  rw [heq]
  refine ComputableTidilyInPolyTime.finite_cases
    (tagEncoding := encPair (encFinite _) (encPair (encFinite _) (encFinite _))) ?_ fun tag => ?_
  · exact (ComputableTidilyInPolyTime.finiteCfg_state.comp hfst).prod
      ((ComputableTidilyInPolyTime.finiteCfg_inputSymbol.comp hfst).prod
        (ComputableTidilyInPolyTime.finiteCfg_workTapeSymbols.comp hfst))
  · rcases tag with ⟨_ | state, symbol, work⟩
    · exact ComputableTidilyInPolyTime.decide_eq' hsnd hfst
    · refine ComputableTidilyInPolyTime.anyConst _ fun action _ => ?_
      exact ComputableTidilyInPolyTime.decide_eq' hsnd
        ((computableTidilyInPolyTime_summary.comp
          (ComputableTidilyInPolyTime.finiteCfg_step action)).comp hfst)

end MultiTapeNTM

end Turing
