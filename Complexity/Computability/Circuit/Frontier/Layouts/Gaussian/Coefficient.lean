/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Layouts.Gaussian.Straddle
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The Gaussian coefficient and its numerical bound

The cubic layout coefficient of Gaussian edge scores is
`p = (3 / (2π)) arccos ((1 + 2√2)/4) ≈ 0.14035`, the straddling bound at the limiting adjacent
correlation `2√2/3` (`Cslib.Circuits.Frontier.Gaussian.gaussianCoefficient_eq`). It is positive,
and the circuit coefficient `1 + 1 / (2p) = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625` is at
least `114/25 = 4.56` (`Cslib.Circuits.Frontier.Gaussian.circuitCoefficient_ge_456`), by
rational bounds on `√2`, `cos` and `π`.

## Main definitions

* `Cslib.Circuits.Frontier.Gaussian.gaussianCoefficient`: the coefficient `p`.

## Main results

* `Cslib.Circuits.Frontier.Gaussian.gaussianCoefficient_pos`: `p > 0`.
* `Cslib.Circuits.Frontier.Gaussian.one_add_inv_two_mul_gaussianCoefficient`: the circuit
  coefficient `1 + 1 / (2p)`.
* `Cslib.Circuits.Frontier.Gaussian.circuitCoefficient_ge_456`: the circuit coefficient is at
  least `114/25`.
-/

@[expose] public section

open Real

namespace Cslib.Circuits.Frontier.Gaussian

/-- The cubic layout coefficient of Gaussian edge scores, `(3 / (2π)) arccos ((1 + 2√2)/4)`. -/
noncomputable def gaussianCoefficient : ℝ :=
  3 / (2 * π) * arccos ((1 + 2 * √2) / 4)

/-- The Gaussian coefficient is the straddling bound at the limiting correlation `2√2/3`. -/
theorem gaussianCoefficient_eq : gaussianCoefficient = straddleBound (2 * √2 / 3) := by
  rw [gaussianCoefficient, straddleBound]
  congr 2
  ring

/-- A crude lower bound, `p ≥ 1/20`, from `cos (π/30) ≥ (1 + 2√2)/4`. -/
theorem gaussianCoefficient_ge : 1 / 20 ≤ gaussianCoefficient := by
  have hsqrt : √2 < 71 / 50 := (sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hpi4 := pi_le_four
  have hθ : π / 30 ≤ arccos ((1 + 2 * √2) / 4) := by
    have hcos : (1 + 2 * √2) / 4 ≤ cos (π / 30) := by
      have := one_sub_sq_div_two_le_cos (x := π / 30)
      have hsq : (π / 30) ^ 2 ≤ (4 / 30) ^ 2 := by gcongr
      linarith
    calc π / 30 = arccos (cos (π / 30)) :=
          (arccos_cos (by positivity) (by linarith [pi_pos])).symm
      _ ≤ _ := arccos_le_arccos hcos
  unfold gaussianCoefficient
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [pi_pos]

theorem gaussianCoefficient_pos : 0 < gaussianCoefficient :=
  lt_of_lt_of_le (by norm_num) gaussianCoefficient_ge

/-- The circuit coefficient `1 + 1 / (2p)` of the cubic coefficient `p`. -/
theorem one_add_inv_two_mul_gaussianCoefficient :
    1 + 1 / (2 * gaussianCoefficient) = 1 + π / (3 * arccos ((1 + 2 * √2) / 4)) := by
  have hsqrt : √2 < 3 / 2 := (sqrt_lt' (by norm_num)).mpr (by norm_num)
  have h : 0 < arccos ((1 + 2 * √2) / 4) := arccos_pos.mpr (by linarith)
  unfold gaussianCoefficient
  congr 1
  field_simp

/-- **The numerical bound.** The circuit coefficient `1 + π / (3 arccos ((1 + 2√2)/4))` is at
least `114/25 = 4.56`.

With `θ = arccos ((1 + 2√2)/4) = 0.293950…`, the bound `θ ≤ 0.2941` has a margin of
`1.5 · 10⁻⁴`, and `π / (3 · 0.2941) = 3.5607…` exceeds `89/25 = 3.56` by `6 · 10⁻⁴`. The cosine
is bounded at the half angle `0.14705` by its Taylor polynomial and doubled:
`2 cos² (0.14705) - 1 ≤ 0.957083…`, against `(1 + 2√2)/4 = 0.957107…`. -/
theorem circuitCoefficient_ge_456 :
    (114 / 25 : ℝ) ≤ 1 + π / (3 * arccos ((1 + 2 * √2) / 4)) := by
  have hsqrt : (141421 : ℝ) / 100000 < √2 := (lt_sqrt (by norm_num)).mpr (by norm_num)
  have hsqrt' : √2 < 3 / 2 := (sqrt_lt' (by norm_num)).mpr (by norm_num)
  have ha : 0 < arccos ((1 + 2 * √2) / 4) := arccos_pos.mpr (by linarith)
  have hcos : cos (2941 / 10000) ≤ (1 + 2 * √2) / 4 := by
    have hb := cos_bound (x := 2941 / 20000) (by norm_num)
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2941 / 20000)] at hb
    have hlo := one_sub_sq_div_two_le_cos (x := 2941 / 20000)
    have hnonneg : 0 ≤ cos (2941 / 20000) := by linarith
    have hupper : cos (2941 / 20000) ≤
        1 - (2941 / 20000 : ℝ) ^ 2 / 2 + (2941 / 20000 : ℝ) ^ 4 * (5 / 96) := by
      linarith [(abs_le.mp hb).2]
    have hsq := pow_le_pow_left₀ hnonneg hupper 2
    rw [show (2941 / 10000 : ℝ) = 2 * (2941 / 20000) by ring, cos_two_mul]
    nlinarith [hsq, hsqrt]
  have hangle : arccos ((1 + 2 * √2) / 4) ≤ 2941 / 10000 :=
    (arccos_le_arccos hcos).trans_eq (arccos_cos (by norm_num) (by linarith [pi_gt_d6]))
  have hdiv : (89 / 25 : ℝ) ≤ π / (3 * arccos ((1 + 2 * √2) / 4)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [pi_gt_d6, hangle]
  linarith

end Cslib.Circuits.Frontier.Gaussian
