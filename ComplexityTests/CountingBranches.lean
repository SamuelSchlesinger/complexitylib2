/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Counting.Certificate
import Mathlib.Tactic.FinCases

/-! Adversarial clients for occurrence multiplicity, early halting and certificate validity. -/

namespace ComplexityTests.CountingBranches

open Turing MultiTapeCTM

private def haltAction (bit : Bool) : MultiTapeMachine.Action 0 Bool Unit Empty :=
  .step { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
    Empty.elim Empty.elim

private def duplicate : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ := [haltAction true, haltAction true]

private def initial : Cfg 0 Bool Unit [] := Cfg.init () []

-- Equal actions are distinct occurrences, with distinct traces and certificates.
example : duplicate.branches 1 initial = {[0], [1]} := by decide
example : duplicate.acceptCount 1 initial = 2 := by decide
example : duplicate.rejectCount 1 initial = 0 := by decide
example : duplicate.certificateCount (· == [true]) 3 initial = 2 := by decide

private theorem duplicate_halts : duplicate.HaltsWithin 1 initial := by
  apply HaltsWithin.step (by decide)
  intro index
  apply HaltsWithin.halt
  fin_cases index <;> rfl

example (fuel : ℕ) (h : 1 ≤ fuel) : duplicate.acceptCount fuel initial = 2 := by
  calc
    duplicate.acceptCount fuel initial = duplicate.acceptCount 1 initial :=
      duplicate_halts.branchCount_eq h _
    _ = 2 := by decide

-- A deterministic singleton halt has one branch, without a discarded final choice.
private def singleton : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ := [haltAction true]

example : singleton.branches 1 initial = {[0]} := by decide
example : singleton.acceptCount 3 initial = 1 := by decide

-- Different actions may also have the same successor: leftward movement at the left boundary
-- agrees with staying put, but the two transition occurrences still contribute separately.
private def boundaryAction (move : SignType) : Turing.Action 0 Bool Unit :=
  { inputTape := move, workTapes := Fin.elim0, output := some true, state := none }

private def sameSuccessor : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ := [MultiTapeMachine.Action.emptyOracleEquiv.symm (boundaryAction (-1)),
    MultiTapeMachine.Action.emptyOracleEquiv.symm (boundaryAction 0)]

private def leftBoundary : Cfg 0 Bool Unit [] := { initial with inputPos := 0 }

example : boundaryAction (-1) ≠ boundaryAction 0 := by
  intro h
  have := congrArg Turing.Action.inputTape h
  contradiction

example : (boundaryAction (-1)).apply leftBoundary = (boundaryAction 0).apply leftBoundary := by
  apply Cfg.ext_zero_tapes <;> simp [Turing.Action.apply, boundaryAction, leftBoundary]

example : sameSuccessor.acceptCount 1 leftBoundary = 2 := by decide

private def stop (bit : Bool) : MultiTapeMachine.Action 0 Bool Bool Empty :=
  .step { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
    Empty.elim Empty.elim

private def advance : MultiTapeMachine.Action 0 Bool Bool Empty :=
  .step { inputTape := 0, workTapes := Fin.elim0, output := none, state := some true }
    Empty.elim Empty.elim

private def mixed : MultiTapeCTM 0 Bool Bool where
  initial := false
  tr state _ _ _ := if state then [stop false, stop true, stop true] else [stop true, advance]

private def mixedInitial : Cfg 0 Bool Bool [] := Cfg.init false []

-- Binary and ternary branching coexist. Early halting does not multiply the short branch,
-- and both terminal verdicts are counted exactly.
example : mixed.branches 2 mixedInitial = {[0], [1, 0], [1, 1], [1, 2]} := by decide
example : mixed.certificates 2 mixedInitial = {[0, 0], [1, 0], [1, 1], [1, 2]} := by decide
example : mixed.acceptCount 2 mixedInitial = 3 := by decide
example : mixed.rejectCount 2 mixedInitial = 1 := by decide
example : mixed.certificateCount (fun out => !(out == [true])) 4 mixedInitial = 1 := by decide

private theorem mixed_halts : mixed.HaltsWithin 2 mixedInitial := by
  apply HaltsWithin.step (by decide)
  intro index
  fin_cases index
  · exact HaltsWithin.halt rfl
  · apply HaltsWithin.step (by decide)
    intro index
    fin_cases index <;> exact HaltsWithin.halt rfl

example (fuel : ℕ) (h : 2 ≤ fuel) :
    mixed.branches fuel mixedInitial = mixed.branches 2 mixedInitial :=
  mixed_halts.branches_eq h

-- Truncation, an invalid occurrence and nonzero post-halt padding each fail both classifiers.
example : mixed.decodeCertificate mixedInitial [1] = none := by rfl
example : mixed.decodeCertificate mixedInitial [2, 0] = none := by rfl
example : mixed.decodeCertificate mixedInitial [0, 1] = none := by decide
example : mixed.certificateAccepts (· == [true]) mixedInitial [0, 1] = false := by decide
example : mixed.certificateAccepts (fun out => !(out == [true])) mixedInitial [0, 1] = false :=
  by decide

-- The single padding label does not turn an already halted branch into many longer branches.
private def halted : Cfg 0 Bool Unit [] := { initial with state := none, output := [true] }

example : duplicate.branches 0 halted = {[]} := by decide
example : duplicate.branches 4 halted = {[]} := by decide
example : duplicate.certificateCount (· == [true]) 0 halted = 1 := by decide
example : duplicate.certificateCount (· == [true]) 4 halted = 1 := by decide
example : duplicate.decodeCertificate halted [1] = none := by decide
example : duplicate.branches 0 initial = ∅ := by decide

private def stuck : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ := []

example : stuck.branches 3 initial = ∅ := by decide
example : stuck.rejectCount 3 initial = 0 := by decide
example (fuel : ℕ) : ¬stuck.HaltsWithin fuel initial := by
  intro h
  cases h with
  | halt h => cases h
  | step h _ => exact h rfl

-- The finite-control occurrence bound and all-branches hypothesis have concrete inhabitants.
example : ∃ bound, ∀ input (cfg : Cfg 0 Bool Bool input), (mixed.actions cfg).length ≤ bound :=
  mixed.exists_branchBound

example : (mixed.branches 2 mixedInitial).Nonempty := mixed_halts.branches_nonempty

/--
info: 'Turing.MultiTapeCTM.mem_branches_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeCTM.mem_branches_iff
/--
info: 'Turing.MultiTapeCTM.HaltsWithin.branches_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeCTM.HaltsWithin.branches_eq
/--
info: 'Turing.MultiTapeCTM.padCertificate_bijOn' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeCTM.padCertificate_bijOn
/--
info: 'Turing.MultiTapeCTM.certificateCounts_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeCTM.certificateCounts_eq

end ComplexityTests.CountingBranches
