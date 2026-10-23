/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.FusionTree.MSBProgram

/-! Actual shift/transfer regressions and nonvacuous MSB execution clients. Full MSB
interpretation is deliberately avoided here; the charged execution theorem covers it. -/

open Cslib.WordRAM Cslib.WordRAM.Multiword

namespace WordRAMMSBTests

def shiftInput (s : ℕ) : Data 9 := ⟨![7, 7, 7, 7, 3, 3, 7, 7, s], fun _ => 7⟩

/-- Whole-digit, residual, zero, and beyond-capacity shifts execute on real instructions. -/
example : ∀ s ∈ [0, 1, 2, 3, 4, 5, 6],
    ((Shift.program 4 [4, 5] [6, 7] 8).eval 4 0 (shiftInput s)).map
      (fun (y, _) => y.regs 6 + 4 * y.regs 7) = some (15 >>> s) := by decide

def oddShiftInput (s : ℕ) : Data 9 := ⟨![7, 7, 7, 7, 1, 1, 7, 7, s], fun _ => 3⟩

example : ∀ s ∈ [0, 1, 2, 3, 4, 5, 6, 7],
    ((Shift.program 3 [4, 5] [6, 7] 8).eval 3 0 (oddShiftInput s)).map
      (fun (y, _) => y.regs 6 + 2 * y.regs 7) = some (3 >>> s) := by decide

/-- Both conversions are charged, including radix setup. -/
def roundTrip : Code .standard 8 :=
  .seq (Transfer.split 4 [5, 6, 7]) (Transfer.assemble [5, 6, 7] 4)

example : ∀ q ∈ List.range 8,
    (roundTrip.eval 3 0 ⟨![7, 7, 7, 7, q, 7, 7, 7], fun _ => 5⟩).map
      (fun (y, t) => (y.regs 4, t, y.mem 12)) = some (q, 28, 5) := by decide

open Cslib.Algorithms.WordRAM.FusionTree.MSB

/-- The singleton-input endpoint includes a real width-two instance. -/
example : ∃ t ≤ 200001, Executes 2 (Program.program 2) (State.init [3]) 1 t := by
  simpa using Program.executes_program (by decide : 2 ≤ 2) (by decide : 3 < 2 ^ 2)

/-- Dirty but fitting workspace, a fitting scalar input, and nonzero memory. -/
def input (w q : ℕ) : Data (Bank.capacity 44 + 4) :=
  ⟨fun i => if i = Bank.inputReg then q else 2 ^ w - 1, fun a => (a + 1) % 2 ^ w⟩

example : ∃ y, ExecWithin 5 (Program.scalarCode 5) (input 5 31) y 200000 ∧
    y.regs Program.output = 4 ∧ y.mem = (input 5 31).mem := by
  have hlog : (31 : ℕ).log2 = 4 := by decide
  simpa only [input, ↓reduceIte, hlog] using
    Program.exec_scalarCode (by decide : 3 ≤ 5) (input 5 31) (by decide)

example : ∃ y, ExecWithin 3 (Program.scalarCode 3) (input 3 0) y 200000 ∧
    y.regs Program.output = 0 ∧ y.mem = (input 3 0).mem := by
  simpa only [input, ↓reduceIte, Nat.log2_zero] using
    Program.exec_scalarCode (by decide : 3 ≤ 3) (input 3 0) (by decide)

/-- Instruction-named registers are a fixed constant independent of physical width. -/
example : Bank.capacity 44 + 4 = 836 := by decide
example (w : ℕ) : (Program.scalarCode w).size ≤ 200000 := Program.size_scalarCode w

/-- info: 'Cslib.Algorithms.WordRAM.FusionTree.MSB.Program.exec_scalarCode' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Program.exec_scalarCode

/-- info: 'Cslib.Algorithms.WordRAM.FusionTree.MSB.Program.executes_program' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Program.executes_program

/-- info: 'Cslib.WordRAM.Multiword.Shift.exec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Shift.exec

/-- info: 'Cslib.WordRAM.Multiword.Transfer.exec_split' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Transfer.exec_split

end WordRAMMSBTests
