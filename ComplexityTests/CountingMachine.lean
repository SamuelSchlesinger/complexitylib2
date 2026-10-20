/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.SharpP.Machine
import Mathlib.Tactic.FinCases

/-! Actual binary-checker clients: variable branching, equal-action multiplicity, first halting,
invalid-code exclusion for both verdicts, and the forward #P/GapP endpoints. -/

namespace ComplexityTests.CountingMachine

open Cslib Turing MultiTapeCTM MultiTapeTM

private def stop (bit : Bool) : MultiTapeMachine.Action 0 Bool Bool Empty :=
  .step { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
    Empty.elim Empty.elim

private def advance : MultiTapeMachine.Action 0 Bool Bool Empty :=
  .step { inputTape := 0, workTapes := Fin.elim0, output := none, state := some true }
    Empty.elim Empty.elim

private def mixed : MultiTapeCTM 0 Bool Bool where
  initial := false
  tr state _ _ _ := if state then [stop false, stop true, stop true] else [stop true, advance]

private theorem mixed_bound (input : List Bool) (cfg : Cfg 0 Bool Bool input) :
    (mixed.actions cfg).length ≤ 2 ^ 2 := by
  cases hs : cfg.state with
  | none => simp [MultiTapeCTM.actions, hs]
  | some state => cases state <;> simp [MultiTapeCTM.actions, hs, mixed]

private theorem mixed_halts (input : List Bool) :
    mixed.HaltsWithin 2 (Cfg.init mixed.initial input) := by
  apply HaltsWithin.step (by exact List.cons_ne_nil _ _)
  intro index
  fin_cases index
  · exact HaltsWithin.halt rfl
  · apply HaltsWithin.step (by exact List.cons_ne_nil _ _)
    intro index
    fin_cases index <;> exact HaltsWithin.halt rfl

-- One early accepting branch, two equal-action accepting occurrences, and one rejecting branch.
example : Complexity.acceptCount (Checker.checkBinary mixed 2 true) [] 4 = 3 := by decide
example : Complexity.acceptCount (Checker.checkBinary mixed 2 false) [] 4 = 1 := by decide

-- Enlarging the clock adds only forced zero blocks; it introduces no new terminal copies.
example (count : ℕ) (hcount : 2 ≤ count) :
    Complexity.acceptCount (Checker.checkBinary mixed 2 true) [] (count * 2) = 3 := by
  rw [Checker.acceptCount_checkBinary mixed (by decide) [] (mixed_bound []) count true,
    (mixed_halts []).branchCount_eq hcount]
  decide

example (count : ℕ) (hcount : 2 ≤ count) :
    Complexity.acceptCount (Checker.checkBinary mixed 2 false) [] (count * 2) = 1 := by
  rw [Checker.acceptCount_checkBinary mixed (by decide) [] (mixed_bound []) count false,
    (mixed_halts []).branchCount_eq hcount]
  decide

-- Canonical padding succeeds; a nonzero terminal block is invalid for both verdicts.
example : Checker.checkBinary mixed 2 true ([], [false, false, false, false]) = true := by decide
example (verdict : Bool) :
    Checker.checkBinary mixed 2 verdict ([], [false, false, false, true]) = false := by
  cases verdict <;> decide

-- Unused binary codes at either branching degree are invalid, not rejecting computations.
example (verdict : Bool) :
    Checker.checkBinary mixed 2 verdict ([], [true, false, false, false]) = false := by
  cases verdict <;> decide
example (verdict : Bool) :
    Checker.checkBinary mixed 2 verdict ([], [false, true, true, true]) = false := by
  cases verdict <;> decide

-- A running endpoint, a leftover partial block, and the zero clock all fail both classifiers.
example (verdict : Bool) :
    Checker.checkBinary mixed 2 verdict ([], [false, true]) = false := by
  cases verdict <;> decide
example (verdict : Bool) :
    Checker.checkBinary mixed 2 verdict ([], [false, false, false]) = false := by
  cases verdict <;> decide
example (verdict : Bool) : Checker.checkBinary mixed 2 verdict ([], []) = false := by
  cases verdict <;> decide

-- The binary representation preserves an empty certificate and leading-zero blocks exactly.
example : binaryCertificate 2 ([] : List ℕ) = [] := rfl
example : binaryCertificate 2 [0, 1, 2] = [false, false, false, true, true, false] := by decide
example : binaryIndices 3 2 [false, false, false, true, true, false] = [0, 1, 2] := by decide

private def stuck : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ := []

example (verdict : Bool) : Checker.checkBinary stuck 1 verdict ([], [false]) = false := by
  cases verdict <;> decide
example : Complexity.acceptCount (Checker.checkBinary stuck 1 false) [] 1 = 0 := by decide

example : (fun input : List Bool => mixed.acceptCount 2 (Cfg.init mixed.initial input)) ∈
    Complexity.SharpP encBits := by
  simpa only [Polynomial.eval_C, encBits_apply] using
    mixed.acceptCount_mem_SharpP encBits (Polynomial.C 2)

example : (fun input : List Bool => mixed.rejectCount 2 (Cfg.init mixed.initial input)) ∈
    Complexity.SharpP encBits := by
  simpa only [Polynomial.eval_C, encBits_apply] using
    mixed.rejectCount_mem_SharpP encBits (Polynomial.C 2)

example : (fun input : List Bool => (mixed.acceptCount 2 (Cfg.init mixed.initial input) : ℤ) -
    mixed.rejectCount 2 (Cfg.init mixed.initial input)) ∈ Complexity.GapP encBits := by
  simpa only [Polynomial.eval_C, encBits_apply] using
    mixed.gapCount_mem_GapP encBits (Polynomial.C 2)

/--
info: 'Turing.MultiTapeCTM.Checker.computableTidilyInPolyTime_checkBinary' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeCTM.Checker.computableTidilyInPolyTime_checkBinary
/--
info: 'Turing.MultiTapeCTM.Checker.acceptCount_checkBinary' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeCTM.Checker.acceptCount_checkBinary
/--
info: 'Turing.MultiTapeCTM.acceptCount_mem_SharpP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeCTM.acceptCount_mem_SharpP
/--
info: 'Turing.MultiTapeCTM.rejectCount_mem_SharpP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeCTM.rejectCount_mem_SharpP
/--
info: 'Turing.MultiTapeCTM.gapCount_mem_GapP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeCTM.gapCount_mem_GapP

end ComplexityTests.CountingMachine
