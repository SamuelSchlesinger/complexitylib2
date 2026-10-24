/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.BooleanAnalysis.Bonami

/-! Instances, non-vacuity witnesses and axiom guards for hypercontractivity and the Bonami
Lemma. -/

namespace ComplexityTests.Hypercontractivity

open Cslib Cslib.BitString Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- The two-point inequality at concrete exponents: `p = 4/3`, `ρ = 1/√3`, as in the
-- `(4/3, 2)`-Hypercontractivity Theorem.
example (a b : ℝ) :
    (a ^ 2 + (1 / √3) ^ 2 * b ^ 2) ^ ((4 / 3 : ℝ) / 2) ≤
      (|a + b| ^ (4 / 3 : ℝ) + |a - b| ^ (4 / 3 : ℝ)) / 2 :=
  sq_add_sq_mul_sq_rpow_le (by norm_num) (by norm_num) (by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num)

-- At `p = 1` only `ρ = 0` is allowed, and the inequality is `|a| ≤ (|a + b| + |a - b|) / 2`.
example (a b : ℝ) :
    (a ^ 2 + 0 ^ 2 * b ^ 2) ^ ((1 : ℝ) / 2) ≤ (|a + b| ^ (1 : ℝ) + |a - b| ^ (1 : ℝ)) / 2 :=
  sq_add_sq_mul_sq_rpow_le le_rfl (by norm_num) (by norm_num)

-- The hypotheses of the Weak Two-Function Hypercontractivity Theorem are satisfiable at every
-- corner: `r = s = 1` and `ρ = 1` is the Cauchy–Schwarz inequality.
example (f g : (ι → Bool) → ℝ) : 𝔼 x, f x * noiseOp 1 g x ≤ lpNorm 2 f * lpNorm 2 g := by
  have h := expect_mul_noiseOp_le_lpNorm_mul_lpNorm zero_le_one le_rfl zero_le_one le_rfl
    zero_le_one (by norm_num) f g
  rwa [one_add_one_eq_two] at h

example (f g : (ι → Bool) → ℝ) : 𝔼 x, f x * noiseOp 0 g x ≤ lpNorm 1 f * lpNorm 1 g := by
  have h := expect_mul_noiseOp_le_lpNorm_mul_lpNorm le_rfl zero_le_one le_rfl zero_le_one le_rfl
    (by norm_num) f g
  rwa [add_zero] at h

-- `(p, 2)` and `(2, q)` at their endpoints and at the exponents of the `(4/3, 2)` and `(2, 4)`
-- theorems.
example (f : (ι → Bool) → ℝ) : lpNorm 2 (noiseOp 1 f) ≤ lpNorm 2 f :=
  lpNorm_two_noiseOp_le (by norm_num) le_rfl zero_le_one (by norm_num) f

example (f : (ι → Bool) → ℝ) : lpNorm 2 (noiseOp (1 / √3) f) ≤ lpNorm (4 / 3) f :=
  lpNorm_two_noiseOp_le (by norm_num) (by norm_num) (by positivity) (by
    rw [one_div, ← Real.sqrt_inv]
    exact Real.sqrt_le_sqrt (by norm_num)) f

example (f : (ι → Bool) → ℝ) : lpNorm 4 (noiseOp (1 / √3) f) ≤ lpNorm 2 f :=
  lpNorm_noiseOp_le_lpNorm_two (by norm_num) (by positivity) (by norm_num) f

example (f : (ι → Bool) → ℝ) : lpNorm 4 (noiseOp (1 / 3) f) ≤ lpNorm (4 / 3) f :=
  lpNorm_noiseOp_le_lpNorm (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by
    rw [show ((4 / 3 : ℝ) - 1) / (4 - 1) = (1 / 3) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]) f

-- The Bonami Lemma for the library's notion of degree, `lowDegree ℝ ι k`.
example {k : ℕ} {f : (ι → Bool) → ℝ} (hf : f ∈ lowDegree ℝ ι k) :
    𝔼 x, f x ^ 4 ≤ 9 ^ k * (𝔼 x, f x ^ 2) ^ 2 :=
  expect_pow_four_le hf

-- The degree hypothesis is satisfiable: a character of `S` has degree `|S|`.
theorem fourierCoeff_chi_eq_zero_of_card_lt (S : Finset ι) {T : Finset ι} (hT : #S < #T) :
    fourierCoeff (chi ℝ S) T = 0 := by
  rw [fourierCoeff, expect_chi_mul_chi]
  split_ifs with h
  · subst h
    exact absurd hT (lt_irrefl _)
  · rfl

example (S : Finset ι) : 𝔼 x, chi ℝ S x ^ 4 ≤ 9 ^ #S * (𝔼 x, chi ℝ S x ^ 2) ^ 2 :=
  expect_pow_four_le (chi_mem_lowDegree S)

example (S : Finset ι) : 𝔼 x, chi ℝ S x ^ 4 ≤ 9 ^ #S * (𝔼 x, chi ℝ S x ^ 2) ^ 2 :=
  expect_pow_four_le_of_fourierCoeff_eq_zero fun _ hT => fourierCoeff_chi_eq_zero_of_card_lt S hT

example (S : Finset ι) {q : ℝ} (hq : 2 ≤ q) :
    lpNorm q (chi ℝ S) ≤ √(q - 1) ^ #S * lpNorm 2 (chi ℝ S) :=
  lpNorm_le_sqrt_pow_mul_lpNorm_two hq (chi_mem_lowDegree S)

example (S : Finset ι) {q : ℝ} (hq : 2 ≤ q) :
    lpNorm q (chi ℝ S) ≤ √(q - 1) ^ #S * lpNorm 2 (chi ℝ S) :=
  lpNorm_le_sqrt_pow_mul_lpNorm_two_of_fourierCoeff_eq_zero hq fun _ hT =>
    fourierCoeff_chi_eq_zero_of_card_lt S hT

-- A concrete instance of the `(2, 4)` theorem on one coordinate: the dictator.
example : 𝔼 x : Fin 1 → Bool, noiseOp (√3)⁻¹ (chi ℝ {0}) x ^ 4 ≤
    (𝔼 x : Fin 1 → Bool, chi ℝ {0} x ^ 2) ^ 2 :=
  expect_noiseOp_pow_four_le _

-- `lpNorm` on any finite type agrees with Mathlib's `MeasureTheory.lpNorm` for the uniform
-- measure.
example (f : (ι → Bool) → ℝ) :
    lpNorm 2 f = MeasureTheory.lpNorm f (ENNReal.ofReal 2)
      (Probability.PMF.uniformOfFintype (ι → Bool)).toMeasure :=
  lpNorm_eq_measureTheory_lpNorm two_pos f

/--
info: 'Cslib.BitString.lpNorm_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.lpNorm_equiv

/--
info: 'Cslib.BitString.lpNorm_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.lpNorm_prod

/--
info: 'Cslib.BitString.lpNorm_subsingleton' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.lpNorm_subsingleton

/--
info: 'Cslib.BitString.lpNorm_eq_measureTheory_lpNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.lpNorm_eq_measureTheory_lpNorm

/--
info: 'Cslib.BitString.sq_add_sq_mul_sq_rpow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.sq_add_sq_mul_sq_rpow_le

/--
info: 'Cslib.BitString.lpNorm_two_noiseOp_le_of_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.lpNorm_two_noiseOp_le_of_unit

/--
info: 'Cslib.BitString.expect_mul_noiseOp_le_of_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.expect_mul_noiseOp_le_of_unit

/--
info: 'Cslib.BitString.expect_mul_noiseOp_le_lpNorm_mul_lpNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.expect_mul_noiseOp_le_lpNorm_mul_lpNorm

/--
info: 'Cslib.BitString.lpNorm_two_noiseOp_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.lpNorm_two_noiseOp_le

/--
info: 'Cslib.BitString.noiseStability_le_lpNorm_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.noiseStability_le_lpNorm_sq

/--
info: 'Cslib.BitString.lpNorm_noiseOp_le_lpNorm_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.lpNorm_noiseOp_le_lpNorm_two

/--
info: 'Cslib.BitString.lpNorm_noiseOp_le_lpNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.lpNorm_noiseOp_le_lpNorm

/--
info: 'Cslib.BitString.expect_noiseOp_pow_four_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.expect_noiseOp_pow_four_le

/--
info: 'Cslib.BitString.noiseStability_one_third_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.noiseStability_one_third_le

/--
info: 'Cslib.BitString.lpNorm_le_sqrt_pow_mul_lpNorm_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.lpNorm_le_sqrt_pow_mul_lpNorm_two

/--
info: 'Cslib.BitString.expect_pow_four_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.expect_pow_four_le

end ComplexityTests.Hypercontractivity
