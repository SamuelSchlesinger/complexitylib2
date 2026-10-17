/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.MassProduction.Synthesis
import Complexity.Computability.Circuit.Boolean.ShannonSynthesis

/-!
# Finite Shannon synthesis regression clients

Check actual circuit evaluation on small truth tables, empty input blocks, constants,
the finite threshold and the placement of natural division in the replicated bound.
-/

namespace ComplexityTests.ShannonSynthesis

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.ShannonSynthesis

-- The sole zero-input minterm is true, and its constant gate is included in the count.
example : (mintermCircuit 0).eval interpretation ![] 0 = true ∧
    (mintermCircuit 0).size = 1 := by decide

-- The native index order is least-significant-bit first, shared with BitString.equivFin.
example : (mintermCircuit 2).eval interpretation ![true, false] =
    ![false, true, false, false] := by decide +kernel

example : (mintermCircuit 2).size = 10 := by decide +kernel

-- An empty column costs one constant gate; a full column shares its input minterms.
example : (columnFormula ![false, false, false, false]).size = 1 ∧
    (columnFormula ![true, true, true, true]).size = 3 := by decide +kernel

example : (columnFormula ![false, true, false, true]).eval interpretation
    ![true, false, true, false] = false := by decide +kernel

-- Exhaustively execute all two-bit functions on all four inputs, through the actual circuit.
example : ∀ (table : BitString 4) (x : BitString 2),
    (circuit (k := 1) (d := 1) (fun a => table (BitString.equivFin 2 a))).eval
      interpretation x 0 = table (BitString.equivFin 2 x) := by decide +kernel

-- Either side of the split, or both, can be empty.
example : ∀ x : BitString 1,
    (circuit (k := 0) (d := 1) (fun a => !a 0)).eval interpretation x 0 = !x 0 := by decide +kernel

example : ∀ x : BitString 1,
    (circuit (k := 1) (d := 0) (fun a => !a 0)).eval interpretation x 0 = !x 0 := by decide +kernel

example : ∀ b : Bool,
    (circuit (k := 0) (d := 0) (fun _ => b)).eval interpretation ![] 0 = b := by decide +kernel

-- Reindexing the selected split remains executable even below the theorem's size threshold.
example : ∀ x : BitString 2,
    (synthesize (fun a : BitString 2 => a 0 ^^ a 1)).eval interpretation x 0 =
      (x 0 ^^ x 1) := by decide +kernel

example : addressWidth 16 = 3 ∧ dataWidth 16 = 13 ∧ bound 3 13 ≤ 27 * 2 ^ 16 / 16 := by
  decide

-- Rounding before multiplication would incorrectly strengthen the claimed endpoint.
example : 27 * 2 ^ 17 / 17 = 208173 ∧ 27 * (2 ^ 17 / 17) = 208170 := by decide

-- The universal bound is usable at its stated finite threshold without additional hypotheses.
example (f : BooleanFunction 16) : ∃ c : Circuit signature 16 1,
    c.Computes interpretation (single f) ∧ c.size ≤ 110592 :=
  exists_circuit (by decide) f

example (f : BooleanFunction 17) (copies : ℕ) :
    MassProduction.massComplexity f copies ≤ (copies * 208173 : ℕ) :=
  MassProduction.massComplexity_le_shannon (by decide) f copies

example (f : BooleanFunction 16) : MassProduction.massComplexity f 0 ≤ (0 : ℕ) :=
  MassProduction.massComplexity_le_shannon (by decide) f 0

end ComplexityTests.ShannonSynthesis
