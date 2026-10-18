/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.Nat.Choose.Real
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.ActivityBounds
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Numerical and native-circuit clients for unrestricted binomial size-activity bounds. -/

open Cslib Cslib.Circuits Cslib.BitString Finset Matrix
open Cslib.Circuits.Boolean.WeightedThreshold

universe u

-- Real parameters include nonintegral choices; the general bound also permits radius > q.
example : (7 : ℝ) ≤ Real.exp 2 * (3 / 2) ^ 2 := by
  have h := sum_choose_le_exp_mul_pow 3 2 (3 / 2) (by norm_num)
  norm_num [sum_range_succ, Nat.choose] at h ⊢
  exact h

example : (2 : ℝ) ≤ Real.exp (1 / 2) * 2 ^ 4 := by
  have h := sum_choose_le_exp_mul_pow 1 4 2 (by norm_num)
  norm_num [sum_range_succ, Nat.choose] at h ⊢
  exact h

-- These radii lie above half the dimension, including the full-radius endpoint.
example : (15 : ℝ) ≤ (Real.exp 1 * 4 / 3) ^ 3 := by
  have h := sum_choose_le_exp_one_mul_div_pow (q := 4) (e := 3) (by decide)
  norm_num [sum_range_succ, Nat.choose] at h ⊢
  exact h

example : (16 : ℝ) ≤ Real.exp 1 ^ 4 := by
  have h := sum_choose_le_exp_one_mul_div_pow (q := 4) (e := 4) le_rfl
  norm_num [sum_range_succ, Nat.choose] at h ⊢
  exact h

example (q : ℕ) : (∑ j ∈ range (0 + 1), (q.choose j : ℝ)) ≤
    (Real.exp 1 * q / 0) ^ (0 : ℕ) :=
  sum_choose_le_exp_one_mul_div_pow (Nat.zero_le q)

-- The optimized estimate really needs e ≤ q, even though the parameterized bound does not.
example : ¬ (∑ j ∈ range 5, ((1 : ℕ).choose j : ℝ)) ≤ (Real.exp 1 / 4) ^ (4 : ℕ) := by
  intro h
  have hpow : (Real.exp 1 / 4) ^ (4 : ℕ) < (3 / 4 : ℝ) ^ (4 : ℕ) := by
    gcongr
    exact Real.exp_one_lt_three
  norm_num [sum_range_succ, Nat.choose] at h hpow
  linarith

example : (3 : ℝ) / 2 ≤ Real.logb 2 (Real.exp 1 * 2) := by
  simpa using le_mul_logb_of_two_pow_le_sum_choose_sq (m := 3) (q := 2) (e := 1)
    (by decide) (by decide)

example : 1 / Real.exp 1 * (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 2 := by
  simpa using mul_rpow_le_of_two_pow_le_sum_choose_sq (m := 3) (q := 2) (e := 1)
    (by decide) (by decide)

example : (7 : ℝ) / 2 ≤ 3 * Real.logb 2 (Real.exp 1 * 4 / 3) := by
  simpa using le_mul_logb_of_two_pow_le_sum_choose_sq (m := 7) (q := 4) (e := 3)
    (by decide) (by decide)

example : 3 / Real.exp 1 * (2 : ℝ) ^ (7 / 6 : ℝ) ≤ 4 := by
  have h := mul_rpow_le_of_two_pow_le_sum_choose_sq (m := 7) (q := 4) (e := 3)
    (by decide) (by decide)
  norm_num at h ⊢
  exact h

example : (0 : ℝ) / 2 ≤ (0 : ℝ) * Real.logb 2 (Real.exp 1 * 0 / 0) := by
  simpa only [Nat.cast_zero] using
    le_mul_logb_of_two_pow_le_sum_choose_sq (m := 0) (q := 0) (e := 0) le_rfl (by decide)

example : (0 : ℝ) / Real.exp 1 * (2 : ℝ) ^ ((0 : ℝ) / (2 * 0)) ≤ 0 := by
  simpa only [Nat.cast_zero] using
    mul_rpow_le_of_two_pow_le_sum_choose_sq (m := 0) (q := 0) (e := 0) le_rfl (by decide)

example (q : ℕ) : ¬ 2 ^ 1 ≤ (∑ j ∈ range (0 + 1), q.choose j) ^ 2 := by simp

-- One threshold gate computes one-coordinate inner product, with activity equal to its size.
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

private theorem andProgram_computes (x y : Fin 1 → Bool) :
    andCircuit.program.eval interpretation
      (inputOfSplit (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm x y) 0 = hadamardCode x y :=
  andCircuit_computes x y

example : inputActivity andCircuit.program = 1 ∧ (inputGates andCircuit.program).card = 1 := by
  have hpos := inputActivity_pos_of_hadamardCode andCircuit.program
    (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm (fun z => z 0) (by decide)
    andProgram_computes
  have hle := inputActivity_le_card andCircuit.program
  have hcard : (inputGates andCircuit.program).card ≤ 1 := by
    simpa using card_le_univ (inputGates andCircuit.program)
  omega

example : (1 : ℝ) / 2 ≤ inputActivity andCircuit.program *
    Real.logb 2 (Real.exp 1 * (inputGates andCircuit.program).card /
      inputActivity andCircuit.program) := by
  simpa using le_inputActivity_mul_logb_of_circuit_hadamardCode andCircuit
    (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm ⟨0, rfl⟩ andCircuit_computes

example : inputActivity andCircuit.program / Real.exp 1 *
    (2 : ℝ) ^ ((1 : ℝ) / (2 * inputActivity andCircuit.program)) ≤
      (inputGates andCircuit.program).card := by
  simpa using inputActivity_mul_rpow_le_card_of_circuit_hadamardCode andCircuit
    (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm ⟨0, rfl⟩ andCircuit_computes

-- This native example has maximum total activity equal to its full gate count.
example : gateActivity andCircuit.program = 1 := by
  have hpos := inputActivity_pos_of_hadamardCode andCircuit.program
    (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm (fun z => z 0) (by decide)
    andProgram_computes
  have hle := inputActivity_le_gateActivity andCircuit.program
  have hcard : gateActivity andCircuit.program ≤ 1 := gateActivity_le andCircuit.program
  omega

example : (1 : ℝ) / 2 ≤ gateActivity andCircuit.program *
    Real.logb 2 (Real.exp 1 * andCircuit.size / gateActivity andCircuit.program) := by
  simpa using le_gateActivity_mul_logb_of_circuit_hadamardCode andCircuit
    (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm ⟨0, rfl⟩ andCircuit_computes

example : gateActivity andCircuit.program / Real.exp 1 *
    (2 : ℝ) ^ ((1 : ℝ) / (2 * gateActivity andCircuit.program)) ≤ andCircuit.size := by
  simpa using gateActivity_mul_rpow_le_of_circuit_hadamardCode andCircuit
    (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm ⟨0, rfl⟩ andCircuit_computes

-- Zero coordinates and zero gates really attain the zero-activity boundary.
example : (0 : ℝ) / 2 ≤ inputActivity (Program.empty : Program signature 0 0) *
    Real.logb 2 (Real.exp 1 * (inputGates (Program.empty : Program signature 0 0)).card /
      inputActivity (Program.empty : Program signature 0 0)) := by
  simpa using le_inputActivity_mul_logb_of_hadamardCode (Program.empty : Program signature 0 0)
    (finSumFinEquiv : Fin 0 ⊕ Fin 0 ≃ Fin 0).symm (fun _ => false)
    (fun _ _ => by simp [hadamardCode_apply, dotProduct, Bool.zero_eq_false])

example : (0 : ℝ) / 2 ≤ gateActivity (Program.empty : Program signature 0 0) *
    Real.logb 2 (Real.exp 1 * 0 / gateActivity (Program.empty : Program signature 0 0)) := by
  simpa only [Fintype.card_fin, Nat.cast_zero] using
    le_gateActivity_mul_logb_of_hadamardCode (Program.empty : Program signature 0 0)
    (finSumFinEquiv : Fin 0 ⊕ Fin 0 ≃ Fin 0).symm (fun _ => false)
    (fun _ _ => by simp [hadamardCode_apply, dotProduct, Bool.zero_eq_false])

example : gateActivity (Program.empty : Program signature 0 0) / Real.exp 1 *
    (2 : ℝ) ^ ((0 : ℝ) / (2 * gateActivity (Program.empty : Program signature 0 0))) ≤ 0 := by
  simpa only [Fintype.card_fin, Nat.cast_zero] using
    gateActivity_mul_rpow_le_of_hadamardCode (Program.empty : Program signature 0 0)
    (finSumFinEquiv : Fin 0 ⊕ Fin 0 ≃ Fin 0).symm (fun _ => false)
    (fun _ _ => by simp [hadamardCode_apply, dotProduct, Bool.zero_eq_false])

example {n g : ℕ} {ι : Type u} [Fintype ι] (p : Program signature n g)
    (split : Fin n ≃ ι ⊕ ι) (readout : (Fin g → Bool) → Bool)
    (h : ∀ x y, readout (p.eval interpretation (inputOfSplit split x y)) = hadamardCode x y) :
    (Fintype.card ι : ℝ) / 2 ≤
      inputActivity p * Real.logb 2 (Real.exp 1 * (inputGates p).card / inputActivity p) :=
  le_inputActivity_mul_logb_of_hadamardCode p split readout h
