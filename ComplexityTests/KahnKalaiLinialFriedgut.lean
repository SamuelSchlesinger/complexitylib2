/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.BooleanAnalysis.KahnKalaiLinial

/-! Instances, non-vacuity witnesses and axiom guards for the Kahn–Kalai–Linial theorem and
Talagrand's inequality. -/

namespace ComplexityTests.KahnKalaiLinialFriedgut

open Cslib Cslib.BitString Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The Kahn–Kalai–Linial theorem -/

-- The statement for `f : (Fin n → Bool) → Bool`, `n ≥ 1`: some coordinate has influence at
-- least `Var[F] log n / (12 n)`.
example {n : ℕ} [NeZero n] (f : (Fin n → Bool) → Bool) :
    ∃ i, (𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2) * Real.log n / (12 * n) ≤
      influence i (fun x => signVal (f x)) := by
  simpa only [Fintype.card_fin] using exists_expect_sub_expect_sq_mul_log_card_div_le_influence f

-- The total influence form with `δ` the largest influence.
example [Nonempty ι] (f : (ι → Bool) → Bool) :
    (𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2) *
        Real.log (univ.sup' univ_nonempty fun i => influence i fun x => signVal (f x))⁻¹ ≤
      6 * totalInfluence (fun x => signVal (f x)) :=
  expect_sub_expect_sq_mul_log_inv_le_six_mul_totalInfluence f fun i =>
    le_sup' (fun i => influence i fun x => signVal (f x)) (mem_univ i)

/-! ### Talagrand's inequality -/

/-- The conjunction of two bits. -/
def and₂ (x : Fin 2 → Bool) : Bool :=
  x 0 && x 1

-- Its influences are less than one: at the all-`false` point no single flip changes it.
theorem influence_and₂_lt_one (i : Fin 2) : influence i (fun x => signVal (and₂ x)) < 1 := by
  rw [influence_signVal]
  calc 𝔼 x, (if and₂ (Function.update x i !x i) = and₂ x then (0 : ℝ) else 1)
      < 𝔼 _x : Fin 2 → Bool, (1 : ℝ) := by
        refine expect_lt_expect (fun x _ => by split_ifs <;> norm_num) ⟨0, mem_univ _, ?_⟩
        have h : and₂ (Function.update 0 i !(0 : Fin 2 → Bool) i) = and₂ 0 := by
          fin_cases i <;> decide
        rw [ite_eq_left h]
        exact one_pos
    _ = 1 := expect_const univ_nonempty 1

-- So the hypothesis of Talagrand's inequality is satisfiable by a nonconstant function.
example : 𝔼 x, (signVal (and₂ x) - 𝔼 y, signVal (and₂ y)) ^ 2 ≤
    6 * ∑ i, influence i (fun x => signVal (and₂ x)) /
      Real.log (influence i fun x => signVal (and₂ x))⁻¹ :=
  expect_sub_expect_sq_le_six_mul_sum_influence_div_log and₂ influence_and₂_lt_one

/--
info: 'Cslib.BitString.sum_filter_mem_one_third_pow_mul_fourierCoeff_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.sum_filter_mem_one_third_pow_mul_fourierCoeff_sq_le

/--
info: 'Cslib.BitString.expect_sub_expect_sq_mul_log_inv_le_six_mul_totalInfluence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.expect_sub_expect_sq_mul_log_inv_le_six_mul_totalInfluence

/--
info: 'Cslib.BitString.exists_expect_sub_expect_sq_mul_log_card_div_le_influence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.exists_expect_sub_expect_sq_mul_log_card_div_le_influence

/--
info: 'Cslib.BitString.expect_sub_expect_sq_le_six_mul_sum_influence_div_log' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.expect_sub_expect_sq_le_six_mul_sum_influence_div_log

/--
info: 'Cslib.BitString.expect_sub_expect_sq_le_seven_mul_sum_influence_div_one_add_log' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.expect_sub_expect_sq_le_seven_mul_sum_influence_div_one_add_log

end ComplexityTests.KahnKalaiLinialFriedgut
