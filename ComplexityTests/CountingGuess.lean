/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Counting.Guess

/-! Clients for exact binary guessing, its clock, and its shared FreeM interpretation. -/

namespace ComplexityTests.CountingGuess

open Cslib Turing MultiTapeCTM GuessMachine

private def initial (input : List Bool) : Cfg 0 Bool Unit input :=
  Cfg.init guessMachine.initial input

-- An empty input has one singleton halt, no discarded binary choice and no zero-step halt.
example : guessMachine.branches 0 (initial []) = ∅ := by decide
example : guessMachine.branches 1 (initial []) = {[0]} := by decide
example : guessMachine.runBranch (initial []) [0, 0] = none := by decide
example : guessMachine.HaltsWithin 1 (initial []) := haltsWithin []

-- Both bit occurrences exist, with distinct outputs and no additional final coin.
example : guessMachine.branches 2 (initial [false]) = {[0, 0], [1, 0]} := by decide
example : guessMachine.branchCount (· == [false]) 2 (initial [true]) = 1 := by decide
example : guessMachine.branchCount (· == [true]) 2 (initial [true]) = 1 := by decide
example : guessMachine.branches 1 (initial [true]) = ∅ := by decide
example : guessMachine.runBranch (initial [true]) [2, 0] = none := by decide
example : guessMachine.runBranch (initial [true]) [1, 1] = none := by decide
example : guessMachine.runBranch (initial [true]) [1, 0, 0] = none := by decide

-- A longer mixed witness is written in chronological choice order.
example : (guessMachine.runBranch (initial [false, false, true]) [1, 0, 1, 0]).map
    Cfg.output = some [true, false, true] := by decide
example : (guessMachine.branches 4 (initial [false, false, true])).card = 8 := by decide
example : guessMachine.branchCount (fun word => word.headD false) 4
    (initial [false, false, true]) = 4 := by decide

example (input : List Bool) (fuel : ℕ) (h : input.length + 1 ≤ fuel)
    (verdict : List Bool → Bool) :
    guessMachine.branchCount verdict fuel (initial input) =
      (Finset.univ.filter fun word : BitString input.length => verdict (List.ofFn word)).card := by
  unfold initial
  rw [(haltsWithin input).branchCount_eq h verdict]
  exact GuessMachine.branchCount_eq input verdict

-- The List handler preserves duplicates, singleton instructions and an empty choice list.
example : OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n))
    (chooseOccurrence [true, true]) = [true, true] := interpret_chooseOccurrence _
example : OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n))
    (chooseOccurrence [false]) = [false] := interpret_chooseOccurrence _
example : OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n))
    (chooseOccurrence ([] : List Bool)) = [] := interpret_chooseOccurrence _

example (input word : List Bool) (h : word.length = input.length) :
    (OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n))
      (Cfg.output <$> guessMachine.runProgram (input.length + 1) (initial input))).count word =
      1 := by
  unfold initial
  rw [count_interpret_output, ite_eq_left h]

example : (OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n))
    (Cfg.output <$> guessMachine.runProgram 1 (initial []))).count [] = 1 := by
  simpa [initial] using count_interpret_output [] []

example : (OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n))
    (Cfg.output <$> guessMachine.runProgram 2 (initial [false]))).count [] = 0 := by
  simpa [initial] using count_interpret_output [false] []

/--
info: 'Turing.MultiTapeCTM.GuessMachine.haltsWithin' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeCTM.GuessMachine.haltsWithin
/--
info: 'Turing.MultiTapeCTM.GuessMachine.runBranch_halted_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeCTM.GuessMachine.runBranch_halted_iff
/--
info: 'Turing.MultiTapeCTM.GuessMachine.trace_bijOn' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeCTM.GuessMachine.trace_bijOn
/--
info: 'Turing.MultiTapeCTM.GuessMachine.branchCount_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeCTM.GuessMachine.branchCount_eq
/--
info: 'Turing.MultiTapeCTM.GuessMachine.count_interpret_output' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeCTM.GuessMachine.count_interpret_output
/--
info: 'Turing.MultiTapeCTM.interpret_chooseOccurrence' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeCTM.interpret_chooseOccurrence

end ComplexityTests.CountingGuess
