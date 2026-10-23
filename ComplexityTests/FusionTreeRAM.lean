/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.Lean.FusionTree.Capacity
import Complexity.Algorithms.Lean.FusionTree.XorCorrection
import Complexity.Algorithms.WordRAM.FusionTree.Boundary
import Complexity.Algorithms.WordRAM.FusionTree.Binary
import Complexity.Algorithms.WordRAM.FusionTree.Compress
import Complexity.Algorithms.WordRAM.FusionTree.LowerRank
import Complexity.Algorithms.WordRAM.FusionTree.MSB
import Complexity.Algorithms.WordRAM.FusionTree.Neighbors

/-! Regression clients for the checked RAM fragments and pure MSB arithmetic. These do not
assert the complete fusion-node or data-structure execution endpoint. -/

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.FusionTree

namespace FusionTreeRAMTests

/-- Duplicates distinguish strict from inclusive ranks, independently of tree sortedness. -/
def sketches (i : ℕ) : ℕ := if i = 0 then 0 else 2

/-- All eight rank inputs are real packed constants at the minimum stated physical width. -/
def rankInput (q : ℕ) : Data 10 :=
  ⟨![q, packedNode 2 3 (fun i => 3 - sketches i), queryMultiplier 2 3,
    guardMask 2 3, 2, 2 ^ 6, 8, 3, 77, 99], fun a => a + 10⟩

/-- Strict rank uses uncomplemented sketches and occupancy in register seven. -/
def lowerInput (q : ℕ) : Data 10 :=
  ⟨![q, packedNode 2 3 sketches, queryMultiplier 2 3, guardMask 2 3,
    2, 2 ^ 6, 8, 3, 77, 99], fun a => a + 10⟩

example : (RankProgram.code.eval 18 0 (rankInput 0)).map
    (fun (y, t) => (y.regs 9, t)) = some (1, 8) := by decide
example : (RankProgram.code.eval 18 0 (rankInput 2)).map
    (fun (y, t) => (y.regs 9, t)) = some (3, 8) := by decide
example : (RankProgram.code.eval 18 0 (rankInput 3)).map
    (fun (y, t) => (y.regs 9, t)) = some (3, 8) := by decide
example : (LowerRankProgram.code.eval 18 0 (lowerInput 0)).map
    (fun (y, t) => (y.regs 9, t)) = some (0, 8) := by decide
example : (LowerRankProgram.code.eval 18 0 (lowerInput 2)).map
    (fun (y, t) => (y.regs 9, t)) = some (1, 8) := by decide
example : (LowerRankProgram.code.eval 18 0 (lowerInput 3)).map
    (fun (y, t) => (y.regs 9, t)) = some (3, 8) := by decide

/-- Instantiate every premise of the checked execution theorem at the packed-width boundary. -/
example : Exec 18 RankProgram.code (rankInput 2)
    (RankProgram.result (rankInput 2) 2 3 sketches 2) 8 :=
  (RankProgram.exec sketches (rankInput 2) (by decide) (by decide)
    (by intro i _; unfold sketches; split <;> decide) (by decide) (by decide)
    rfl rfl rfl rfl rfl rfl rfl rfl).1

example : Exec 18 LowerRankProgram.code (lowerInput 2)
    (LowerRankProgram.result (lowerInput 2) 2 3 sketches 2) 8 :=
  (LowerRankProgram.exec sketches (lowerInput 2) (by decide) (by decide)
    (by intro i _; unfold sketches; split <;> decide) (by decide) (by decide)
    rfl rfl rfl rfl rfl rfl rfl rfl).1

/-- Top-bit correction does not create `2^w` in any register. -/
example : (BoundaryProgram.code.eval 4 0
    ⟨![15, 3, 91, 91, 91, 91, 91, 91, 91, 91], fun _ => 7⟩).map
    (fun (y, t) => (y.regs 7, y.regs 8, y.regs 9, t)) = some (7, 8, 1, 10) := by decide

example : (BoundaryProgram.code.eval 1 0
    ⟨![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], fun _ => 0⟩).map
    (fun (y, t) => (y.regs 7, y.regs 8, y.regs 9, t)) = some (0, 1, 0, 10) := by decide

/-- Preload three multiplier digits and dirty the workspace; conversion is part of the code. -/
def compressionInput (w q C M D : ℕ) : Data 21 :=
  ⟨fun i =>
    if i = 7 then M % Multiword.radix w
    else if i = 8 then M / Multiword.radix w % Multiword.radix w
    else if i = 9 then M / Multiword.radix w / Multiword.radix w % Multiword.radix w
    else if i = 16 then q
    else if i = 17 then C
    else if i = 18 then D
    else if i = 19 then w - 2 * (w / 2)
    else 2 ^ w - 1,
    fun a => (a + 1) % 2 ^ w⟩

/-- Odd-width maximum window, with a multiplier wider than the physical word. -/
example : (CompressProgram.code.eval 25 0
    (compressionInput 25 (2 ^ 25 - 1) 9 (2 ^ 25 + 2 ^ 32) 1025)).map
    (fun (y, t) => (y.regs 20, t, y.regs 16, y.mem 123)) =
      some (1025, 94, 2 ^ 25 - 1, 124) := by decide

example : (CompressProgram.code.eval 2 0 (compressionInput 2 3 3 7 1)).map
    (fun (y, t) => (y.regs 20, t)) = some (1, 94) := by decide

/-- Pure MSB arithmetic includes zero and nonsquare physical widths. -/
example : MSB.widthMSB 0 0 = 0 ∧ MSB.widthMSB 1 1 = 0 ∧
    MSB.widthMSB 17 (2 ^ 16 + 1) = 16 ∧ MSB.widthMSB 7 65 = 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [MSB.widthMSB_eq_log2 (by decide)] <;> decide

example : ∀ x < 2 ^ 17, MSB.widthMSB 17 x = x.log2 :=
  fun _ hx => MSB.widthMSB_eq_log2 hx

/-- A real array with nonzero stride exercises both clamped end cuts and an interior cut. -/
def neighborInput (q t : ℕ) : Data 17 :=
  ⟨![q, t, 3, 10, 2, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99],
    fun a => if a = 10 then 2 else if a = 12 then 6 else if a = 14 then 9 else 0⟩

example : (NeighborProgram.code.eval 4 0 (neighborInput 0 0)).map
    (fun (y, t) => (y.regs 14, y.regs 15, y.regs 16, t)) = some (2, 2, 0, 18) := by decide
example : (NeighborProgram.code.eval 4 0 (neighborInput 7 1)).map
    (fun (y, t) => (y.regs 14, y.regs 15, y.regs 16, t)) = some (6, 1, 1, 17) := by decide
example : (NeighborProgram.code.eval 4 0 (neighborInput 15 3)).map
    (fun (y, t) => (y.regs 14, y.regs 15, y.regs 16, t)) = some (9, 6, 2, 18) := by decide

example : Cslib.Algorithms.Lean.FusionTree.xorCorrectedRank 4 ![0, 2, 12, 15] 5 = 2 := by
  rw [Cslib.Algorithms.Lean.FusionTree.xorCorrectedRank_eq_upperRank
    (by decide) (by decide) (by decide)]
  unfold Cslib.Algorithms.Lean.FusionTree.upperRank
  decide

example : Cslib.Algorithms.Lean.FusionTree.branching 511 = 2 ∧
    Cslib.Algorithms.Lean.FusionTree.branching 512 = 2 := by decide

/-- The small-width fallback reads the same stride-two child-minimum table. -/
def binaryInput (q : ℕ) : Data 1024 :=
  ⟨fun i => if i = 0 then q else 0,
    fun a => if a = 18 then 2 else if a = 20 then 9 else 0⟩

example : (BinaryNodeProgram.code.eval 6 0 (binaryInput 1)).map
    (fun (y, t) => (y.regs 2, t)) = some (0, 8) := by decide
example : (BinaryNodeProgram.code.eval 6 0 (binaryInput 2)).map
    (fun (y, t) => (y.regs 2, t)) = some (1, 10) := by decide
example : (BinaryNodeProgram.code.eval 6 0 (binaryInput 9)).map
    (fun (y, t) => (y.regs 2, t)) = some (2, 11) := by decide

/-- info: 'Cslib.Algorithms.WordRAM.FusionTree.BinaryNodeProgram.exec' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BinaryNodeProgram.exec

/-- info: 'Cslib.Algorithms.WordRAM.FusionTree.RankProgram.exec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RankProgram.exec

/-- info: 'Cslib.Algorithms.WordRAM.FusionTree.LowerRankProgram.exec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerRankProgram.exec

/-- info: 'Cslib.Algorithms.WordRAM.FusionTree.MSB.widthMSB_eq_log2' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MSB.widthMSB_eq_log2

/-- info: 'Cslib.Algorithms.WordRAM.FusionTree.MSB.widthMSB_virtual_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MSB.widthMSB_virtual_bounds

/-- info: 'Cslib.Algorithms.WordRAM.FusionTree.CompressProgram.exec_approximateSketch'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressProgram.exec_approximateSketch

/-- info: 'Cslib.Algorithms.WordRAM.FusionTree.BoundaryProgram.exec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BoundaryProgram.exec

/-- info: 'Cslib.Algorithms.WordRAM.FusionTree.NeighborProgram.exec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NeighborProgram.exec

/-- info: 'Cslib.Algorithms.Lean.FusionTree.xorCorrectedRank_eq_upperRank' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Algorithms.Lean.FusionTree.xorCorrectedRank_eq_upperRank

end FusionTreeRAMTests
