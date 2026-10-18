/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Real bounds for partial binomial sums

The binomial generating function gives `∑ j ≤ e, q.choose j ≤ exp (q / T) * T ^ e`
for any real `T ≥ 1`. For `0 < e ≤ q`, choosing `T = q / e` gives `(exp 1 * q / e) ^ e`.
This bound remains valid above half the dimension. At radius zero the sum and bound are both one.

The generating-function proof is shared with the sparsification lemma. The logarithmic
consequences turn an exponential lower bound on the square of a partial binomial sum into
size-activity bounds; they include the zero-radius case using the usual total real operations.

## Main results

* `Cslib.sum_choose_le_exp_mul_pow`: a real-parameter generating-function bound.
* `Cslib.sum_choose_le_exp_one_mul_div_pow`: the bound with parameter `q / e`.
* `Cslib.le_mul_logb_of_two_pow_le_sum_choose_sq`: the logarithmic consequence.
* `Cslib.mul_rpow_le_of_two_pow_le_sum_choose_sq`: the rearranged size lower bound.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Theorem 3.2]
  [ThresholdCircuitRepresentations2026]
* [C. Calabro, R. Impagliazzo, R. Paturi, *A duality between clause width and clause density for
  SAT*][CalabroImpagliazzoPaturi2006]
-/

@[expose] public section

namespace Cslib

open Finset

/-- A partial binomial sum is at most `exp (q / T) * T ^ e` for every real `T ≥ 1`.
The radius `e` may exceed `q`. -/
theorem sum_choose_le_exp_mul_pow (q e : ℕ) (T : ℝ) (hT : 1 ≤ T) :
    (∑ j ∈ range (e + 1), (q.choose j : ℝ)) ≤ Real.exp (q / T) * T ^ e := by
  have hT0 : 0 < T := by linarith
  set t : ℝ := 1 / T with ht
  have ht0 : 0 ≤ t := by positivity
  have hg : ∀ j, 0 ≤ (q.choose j : ℝ) * t ^ j := fun j => by positivity
  have hpartial : ∑ j ∈ range (e + 1), (q.choose j : ℝ) * t ^ j ≤ (1 + t) ^ q := by
    set m := max (e + 1) (q + 1)
    calc ∑ j ∈ range (e + 1), (q.choose j : ℝ) * t ^ j
        ≤ ∑ j ∈ range m, (q.choose j : ℝ) * t ^ j :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (le_max_left _ _))
            fun j _ _ => hg j
      _ = ∑ j ∈ range (q + 1), (q.choose j : ℝ) * t ^ j := by
          refine (sum_subset (range_subset_range.mpr (le_max_right _ _)) fun j _ hj => ?_).symm
          rw [Nat.choose_eq_zero_of_lt (by simpa using hj), Nat.cast_zero, zero_mul]
      _ = (1 + t) ^ q := by
          rw [add_comm (1 : ℝ) t, add_pow]
          refine sum_congr rfl fun j _ => ?_
          rw [one_pow, mul_one, mul_comm]
  calc (∑ j ∈ range (e + 1), (q.choose j : ℝ))
      ≤ ∑ j ∈ range (e + 1), (q.choose j : ℝ) * t ^ j * T ^ e := by
        refine sum_le_sum fun j hj => ?_
        have hje : j ≤ e := Nat.lt_succ_iff.mp (mem_range.mp hj)
        have : 1 ≤ t ^ j * T ^ e := by
          rw [← Nat.add_sub_cancel' hje, pow_add, ← mul_assoc, ht, ← mul_pow, one_div,
            inv_mul_cancel₀ hT0.ne', one_pow, one_mul]
          exact one_le_pow₀ hT
        calc (q.choose j : ℝ) = (q.choose j : ℝ) * 1 := (mul_one _).symm
          _ ≤ (q.choose j : ℝ) * (t ^ j * T ^ e) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = (q.choose j : ℝ) * t ^ j * T ^ e := by ring
    _ = (∑ j ∈ range (e + 1), (q.choose j : ℝ) * t ^ j) * T ^ e := by rw [sum_mul]
    _ ≤ (1 + t) ^ q * T ^ e := by gcongr
    _ ≤ Real.exp t ^ q * T ^ e := by
        gcongr
        linarith [Real.add_one_le_exp t]
    _ = Real.exp (q / T) * T ^ e := by
        rw [← Real.exp_nat_mul, ht]
        ring_nf

/-- The standard bound `(exp 1 * q / e) ^ e` holds throughout `e ≤ q`, not just for
`e ≤ q / 2`. At `e = 0` both sides are one. -/
theorem sum_choose_le_exp_one_mul_div_pow {q e : ℕ} (heq : e ≤ q) :
    (∑ j ∈ range (e + 1), (q.choose j : ℝ)) ≤ (Real.exp 1 * q / e) ^ e := by
  by_cases he : e = 0
  · simp [he]
  have he0 : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero he
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le he0 (by exact_mod_cast heq)
  have hT : (1 : ℝ) ≤ q / e :=
    (le_div_iff₀ he0).mpr (by simpa only [one_mul] using (Nat.cast_le.mpr heq : (e : ℝ) ≤ q))
  have hqe : (q : ℝ) / (q / e) = e := by field_simp
  calc (∑ j ∈ range (e + 1), (q.choose j : ℝ)) ≤ Real.exp e * ((q : ℝ) / e) ^ e := by
        simpa only [hqe] using sum_choose_le_exp_mul_pow q e ((q : ℝ) / e) hT
    _ = (Real.exp 1 * q / e) ^ e := by
        rw [mul_div_assoc, mul_pow, ← Real.exp_nat_mul]
        simp

/-- If the square of the radius-`e` binomial sum is at least `2 ^ m`, then
`m / 2 ≤ e * log₂ (exp 1 * q / e)`. The statement includes `e = 0`, which forces `m = 0`. -/
theorem le_mul_logb_of_two_pow_le_sum_choose_sq {m q e : ℕ} (heq : e ≤ q)
    (h : 2 ^ m ≤ (∑ j ∈ range (e + 1), q.choose j) ^ 2) :
    (m : ℝ) / 2 ≤ e * Real.logb 2 (Real.exp 1 * q / e) := by
  have hreal : (2 : ℝ) ^ m ≤ (∑ j ∈ range (e + 1), (q.choose j : ℝ)) ^ 2 := by
    exact_mod_cast h
  have hs : 0 ≤ ∑ j ∈ range (e + 1), (q.choose j : ℝ) := sum_nonneg fun _ _ => by positivity
  have hpow := hreal.trans (pow_le_pow_left₀ hs
    (sum_choose_le_exp_one_mul_div_pow heq) 2)
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num)
    (by positivity : (0 : ℝ) < 2 ^ m) hpow
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    Nat.cast_ofNat, mul_one] at hlog
  linarith

/-- The logarithmic partial-binomial-sum bound rearranged as a lower bound on `q`.
At radius zero the lower bound is zero. -/
theorem mul_rpow_le_of_two_pow_le_sum_choose_sq {m q e : ℕ} (heq : e ≤ q)
    (h : 2 ^ m ≤ (∑ j ∈ range (e + 1), q.choose j) ^ 2) :
    e / Real.exp 1 * (2 : ℝ) ^ ((m : ℝ) / (2 * e)) ≤ q := by
  by_cases he : e = 0
  · simp [he]
  have he0 : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero he
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le he0 (by exact_mod_cast heq)
  have hlog := le_mul_logb_of_two_pow_le_sum_choose_sq heq h
  have hx : (m : ℝ) / (2 * e) ≤ Real.logb 2 (Real.exp 1 * q / e) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * e)).mpr
    linarith
  have hp := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by positivity)).mp hx
  calc e / Real.exp 1 * (2 : ℝ) ^ ((m : ℝ) / (2 * e))
      ≤ e / Real.exp 1 * (Real.exp 1 * q / e) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
    _ = q := by field_simp

end Cslib
