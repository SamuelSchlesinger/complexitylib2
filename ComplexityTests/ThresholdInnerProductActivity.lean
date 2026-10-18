/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.WeightedThreshold.InnerProduct
import Mathlib.Algebra.BigOperators.Fin

/-! Concrete and boundary clients for the inner-product pattern and activity inequalities. -/

open Cslib Cslib.Circuits Cslib.BitString Finset Matrix
open Cslib.Circuits.Boolean.WeightedThreshold

namespace ThresholdInnerProductActivity

-- With no coordinates or gates, the constant false readout genuinely computes inner product.
example : 1 ≤ (attainableTranscripts (Program.empty : Program signature 0 0)).card ^ 2 :=
  two_pow_le_card_attainableTranscripts_sq_of_hadamardCode Program.empty
    (finSumFinEquiv : Fin 0 ⊕ Fin 0 ≃ Fin 0).symm (fun _ => false)
    (fun _ _ => by simp [hadamardCode_apply, dotProduct, Bool.zero_eq_false])

-- At positive dimension, zero input-reading activity cannot compute inner product.
example {n g : ℕ} (p : Program signature n g) (split : Fin n ≃ Fin 1 ⊕ Fin 1)
    (readout : (Fin g → Bool) → Bool) (he : inputActivity p = 0) :
    ¬ ∀ x y, readout (p.eval interpretation (inputOfSplit split x y)) = hadamardCode x y := by
  intro h
  have := two_pow_le_sum_choose_sq_of_hadamardCode p split readout h
  simp [he] at this

private abbrev andCircuit : Circuit signature 2 1 :=
  ⟨Program.empty.gate ⟨⟨2, fun _ => 1, 2⟩, Wire.input⟩, fun _ => .gate 0⟩

private theorem andCircuit_computes (x y : Fin 1 → Bool) :
    andCircuit.eval interpretation
      (inputOfSplit (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm x y) 0 = hadamardCode x y := by
  change (Program.empty.gate _).eval interpretation _ (Fin.last 0) = _
  rw [Program.eval_gate_last]
  cases hx : x 0 <;> cases hy : y 0 <;>
    dsimp only [Line.eval, interpretation, Function.comp_apply, Wire.elim] <;>
    norm_num [Fin.sum_univ_two, inputOfSplit, finSumFinEquiv, Fin.addCases,
      hadamardCode_apply, dotProduct, Bool.mul_eq_and, hx, hy]

-- The single gate at threshold two supplies a nonconstant circuit computing one-bit inner product.
example : 2 ≤
    (∑ j ∈ range (inputActivity andCircuit.program + 1),
      (inputGates andCircuit.program).card.choose j) ^ 2 :=
  two_pow_le_sum_choose_sq_of_circuit_hadamardCode andCircuit
    (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm
    ⟨0, rfl⟩ andCircuit_computes

-- The pattern theorem also applies directly to the underlying native program.
example : 2 ≤ (attainableTranscripts andCircuit.program).card ^ 2 := by
  apply two_pow_le_card_attainableTranscripts_sq_of_hadamardCode andCircuit.program
    (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm (fun z => z 0)
  intro x y
  simpa only [andCircuit, Circuit.eval, Function.comp_apply, Program.trace_gateWire,
    Program.gateFunction_apply] using andCircuit_computes x y

end ThresholdInnerProductActivity
