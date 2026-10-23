/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.MapOp

/-!
# Word-RAM bases

Regressions for operation bases: a program over the additive basis runs, faults and halts exactly
as its translation over the standard basis does, the translation is the program written with the
standard instructions, programs avoiding the word-size operation do not read the word size,
the exact basis faults on subtraction below zero and division by zero, and decision transfers
along the maps between the named bases.
-/

namespace ComplexityTests.WordRAMBasis

open Cslib.WordRAM

/-! ## The named bases and their maps -/

/-- Addition, as an operation of the additive basis. -/
def addOp : Basis.additive.Op := ⟨.bin .add, by decide⟩

/-- Multiplication is an arithmetic operation. -/
def mulOp : Basis.arithmetic.Op := ⟨.bin .mul, by decide⟩

/-- The operations of the sub-bases are those listed, and the word size is not one of them. -/
example : (∀ f : Basis.additive.Op, f.1 = .bin .add ∨ f.1 = .bin .sub) ∧
    ¬∃ f : Basis.arithmetic.Op, f.1 = .width := by
  constructor
  · rintro ⟨f, hf⟩
    simpa using hf
  · rintro ⟨⟨f, hf⟩, rfl⟩
    simp at hf

/-- The two routes from the additive to the standard basis agree. -/
example (f : Basis.additive.Op) :
    (Basis.arithmeticHomStandard.comp Basis.additiveHomArithmetic).map f =
      Basis.additiveHomStandard.map f :=
  Basis.arithmeticHomStandard_comp_additiveHomArithmetic f

/-! ## Running a program over a smaller basis -/

/-- Load the first input word into register `0` and add it to itself, over the additive basis. -/
def double : Program .additive 2 :=
  [.op (.const 1 1), .op (.load 0 1), .op (.alu addOp 0 ![0, 0]), .halt 0]

/-- The same program over the standard basis. -/
def doubleStandard : Program .standard 2 :=
  [.op (.const 1 1), .op (.load 0 1), .op (.bin .add 0 0 0), .halt 0]

/-- Translating along the inclusion yields the program written with standard instructions. -/
example : double.mapOp Basis.additiveHomStandard = doubleStandard := by decide

/-- The additive program doubles the first input word, and overflow faults: `4 + 4` does not fit
a three-bit word. -/
example : run 4 double 10 (.init [3]) = some (6, 4) ∧ run 3 double 10 (.init [4]) = none := by
  decide

/-- The translation runs identically, at every word size and from every state. -/
example (w fuel : ℕ) (s : State 2) :
    run w doubleStandard fuel s = run w double fuel s := by
  rw [← run_mapOp Basis.additiveHomStandard]
  rfl

/-- Programs over the additive basis never read the word size, and neither do their
translations. -/
example : ¬double.ReadsWidth ∧ ¬doubleStandard.ReadsWidth := by decide

/-- The standard word-size operation is the only one that reads the word size. -/
example (f : StandardOp) : Basis.standard.ReadsWidth f ↔ f = .width := Iff.rfl

/-- A program that does not read the word size halts in the same way at every larger word size. -/
example (w : ℕ) (hw : 4 ≤ w) : Executes w double (.init [3]) 6 4 :=
  (Executes.of_run (fuel := 10) (by decide : run 4 double 10 (.init [3]) = some (6, 4))).mono_width
    (by decide) hw

/-! ## The exact basis -/

/-- Load the two input words into registers `0` and `1` and apply `f` to them, over the exact
basis. -/
def applyExact (f : BinOp) : Program .exact 3 :=
  [.op (.const 2 1), .op (.load 0 2), .op (.const 2 2), .op (.load 1 2),
    .op (.exactBin f 0 0 1), .halt 0]

/-- The same program over the standard basis. -/
def applyStandard (f : BinOp) : Program .standard 3 :=
  [.op (.const 2 1), .op (.load 0 2), .op (.const 2 2), .op (.load 1 2), .op (.bin f 0 0 1),
    .halt 0]

/-- Exact subtraction faults below zero, where the standard basis truncates to `0`. -/
example : run 4 (applyExact .sub) 10 (.init [5, 3]) = some (2, 6) ∧
    run 4 (applyExact .sub) 10 (.init [3, 5]) = none ∧
    run 4 (applyStandard .sub) 10 (.init [3, 5]) = some (0, 6) := by
  decide

/-- Exact division and remainder fault on a zero divisor, where the standard basis follows
Lean's `x / 0 = 0` and `x % 0 = x`. -/
example : run 4 (applyExact .div) 10 (.init [7, 2]) = some (3, 6) ∧
    run 4 (applyExact .div) 10 (.init [7, 0]) = none ∧
    run 4 (applyExact .mod) 10 (.init [7, 0]) = none ∧
    run 4 (applyStandard .div) 10 (.init [7, 0]) = some (0, 6) ∧
    run 4 (applyStandard .mod) 10 (.init [7, 0]) = some (7, 6) := by
  decide

/-- Word-size monotonicity covers exact subtraction: a successful run is a run at every larger
word size. -/
example (w : ℕ) (hw : 4 ≤ w) : Executes w (applyExact .sub) (.init [5, 3]) 2 6 :=
  (Executes.of_run (fuel := 10)
    (by decide : run 4 (applyExact .sub) 10 (.init [5, 3]) = some (2, 6))).mono_width
    (by decide) hw

/-! ## Decision grows with the basis -/

example {α : Type} {A : Set α} {encode : ℕ → α → List ℕ} {size : α → ℕ}
    (h : LinearTime .additive A encode size) : LinearTime .standard A encode size :=
  (h.mapOp Basis.additiveHomArithmetic).mapOp Basis.arithmeticHomStandard

example {α : Type} {A : Set α} {encode : ℕ → α → List ℕ} {size : α → ℕ}
    (h : PolynomialTime .arithmetic A encode size) : PolynomialTime .standard A encode size :=
  h.mapOp Basis.arithmeticHomStandard

example {α : Type} {A : Set α} {encode : ℕ → α → List ℕ} {size : α → ℕ}
    (h : UniformLinearTime .additive A encode size) : UniformLinearTime .standard A encode size :=
  (h.mapOp Basis.additiveHomArithmetic).mapOp Basis.arithmeticHomStandard

example {α : Type} {A : Set α} {encode : ℕ → α → List ℕ} {size : α → ℕ}
    (h : UniformPolynomialTime .arithmetic A encode size) :
    UniformPolynomialTime .standard A encode size :=
  h.mapOp Basis.arithmeticHomStandard

/--
info: 'Cslib.WordRAM.executes_mapOp_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.executes_mapOp_iff

/--
info: 'Cslib.WordRAM.LinearTime.mapOp' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.LinearTime.mapOp

end ComplexityTests.WordRAMBasis
