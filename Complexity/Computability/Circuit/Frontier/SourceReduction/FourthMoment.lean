/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Quartic certificates for positive and negative tails

To prove that the majority of almost-independent votes takes each Boolean value with constant
probability (as in [Chattopadhyay and Liao][ChattopadhyayLiao2022], Lemma 5.4), we use an explicit
degree-4 polynomial certificate rather than a general Berry–Esseen or bounded-independence theorem
for halfspaces.

For any real `x`, the quartic `tailQuartic x = x * (x + 1)^2 * (3 - x)` satisfies
`tailQuartic x ≤ 0` when `x ≤ 0` and `tailQuartic x ≤ 36` when `0 < x`. Evaluating
`tailQuartic (Z - 1 / 8)` under any probability weight `w` whose first four moments of `Z` are
`0.01`-close to the standard normal moments `(0, 1, 0, 3)` shows that the positive tail
`{i | 1 / 8 < Z i}` has probability mass at least `1 / 36`. Applying the same certificate to `-Z`
gives the symmetric negative-tail lower bound on `{i | Z i < -1 / 8}`.

## Main results

* `Cslib.Circuits.Frontier.fourthMoment_positive_tail_of_approx`: approximate normal moments through
  degree 4 force `P[Z > 1 / 8] ≥ 1 / 36`.
* `Cslib.Circuits.Frontier.fourthMoment_negative_tail_of_approx`: approximate normal moments through
  degree 4 force `P[Z < -1 / 8] ≥ 1 / 36`.
* `Cslib.Circuits.Frontier.fourthMoment_positive_tail`,
  `Cslib.Circuits.Frontier.fourthMoment_negative_tail`: specializations to exact moments through
  degree 3 and fourth moment at most `3`.

## References

* [E. Chattopadhyay and J.-J. Liao, *Extractors for Sum of Two Sources*][ChattopadhyayLiao2022]
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

private def tailQuartic (x : ℝ) : ℝ := x * (x + 1) ^ 2 * (3 - x)

private theorem tailQuartic_le (x : ℝ) :
    tailQuartic x ≤ if 0 < x then 36 else 0 := by
  by_cases hx : 0 < x
  · rw [ite_eq_left_iff.mpr (fun h => (h hx).elim)]
    by_cases h3 : x ≤ 3
    · have hprod : x * (3 - x) ≤ 9 / 4 := by nlinarith [sq_nonneg (x - 3 / 2)]
      have hsq : (x + 1) ^ 2 ≤ 16 := by nlinarith
      calc
        tailQuartic x = (x * (3 - x)) * (x + 1) ^ 2 := by unfold tailQuartic; ring
        _ ≤ (9 / 4) * 16 := mul_le_mul hprod hsq (sq_nonneg _) (by norm_num)
        _ = 36 := by norm_num
    · have hnonpos : tailQuartic x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hx.le (sq_nonneg _)) (by linarith)
      linarith
  · rw [ite_eq_right_iff.mpr (fun h => (hx h).elim)]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hx) (sq_nonneg _)) (by linarith)

/-- **Approximate fourth-moment positive-tail certificate:** if a probability weight `w` on `s` has
first four moments of `Z` within `1 / 100` of `(0, 1, 0, ≤ 3)`, then the positive tail beyond
`1 / 8` has mass at least `1 / 36`. -/
theorem fourthMoment_positive_tail_of_approx {α : Type*} (s : Finset α) (w Z : α → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hmass : ∑ i ∈ s, w i = 1)
    (hmean : |∑ i ∈ s, w i * Z i| ≤ 1 / 100)
    (hsecond : (99 / 100 : ℝ) ≤ ∑ i ∈ s, w i * Z i ^ 2)
    (hthird : |∑ i ∈ s, w i * Z i ^ 3| ≤ 1 / 100)
    (hfourth : ∑ i ∈ s, w i * Z i ^ 4 ≤ 301 / 100) :
    (1 / 36 : ℝ) ≤ ∑ i ∈ s, if 1 / 8 < Z i then w i else 0 := by
  have hexpand : (∑ i ∈ s, w i * tailQuartic (Z i - 1 / 8)) =
      -(∑ i ∈ s, w i * Z i ^ 4) + (3 / 2) * (∑ i ∈ s, w i * Z i ^ 3) +
      (145 / 32) * (∑ i ∈ s, w i * Z i ^ 2) +
      (231 / 128) * (∑ i ∈ s, w i * Z i) - (1225 / 4096) * (∑ i ∈ s, w i) := by
    simp only [← Finset.sum_neg_distrib, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold tailQuartic
    ring
  have hupper : (∑ i ∈ s, w i * tailQuartic (Z i - 1 / 8)) ≤
      36 * (∑ i ∈ s, if 1 / 8 < Z i then w i else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_left (tailQuartic_le (Z i - 1 / 8)) (hw i hi)
    simpa only [sub_pos, mul_ite, mul_zero, mul_comm (w i) (36 : ℝ)] using h
  rw [hexpand, hmass] at hupper
  have hm := (abs_le.mp hmean).1
  have ht := (abs_le.mp hthird).1
  linarith

/-- **Approximate fourth-moment negative-tail certificate:** under the same approximate normal
moment bounds, the negative tail below `-1 / 8` also has mass at least `1 / 36`. -/
theorem fourthMoment_negative_tail_of_approx {α : Type*} (s : Finset α) (w Z : α → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hmass : ∑ i ∈ s, w i = 1)
    (hmean : |∑ i ∈ s, w i * Z i| ≤ 1 / 100)
    (hsecond : (99 / 100 : ℝ) ≤ ∑ i ∈ s, w i * Z i ^ 2)
    (hthird : |∑ i ∈ s, w i * Z i ^ 3| ≤ 1 / 100)
    (hfourth : ∑ i ∈ s, w i * Z i ^ 4 ≤ 301 / 100) :
    (1 / 36 : ℝ) ≤ ∑ i ∈ s, if Z i < -(1 / 8) then w i else 0 := by
  have hcubic (i) : w i * (-Z i) ^ 3 = -(w i * Z i ^ 3) := by ring
  have hquartic (i) : w i * (-Z i) ^ 4 = w i * Z i ^ 4 := by ring
  have h := fourthMoment_positive_tail_of_approx s w (fun i => -Z i) hw hmass
    (by simpa only [mul_neg, Finset.sum_neg_distrib, abs_neg] using hmean)
    (by simpa only [even_two.neg_pow] using hsecond)
    (by simpa only [hcubic, Finset.sum_neg_distrib, abs_neg] using hthird)
    (by simpa only [hquartic] using hfourth)
  simpa only [lt_neg] using h

/-- **Exact fourth-moment positive-tail certificate:** exact normal moments through degree 3 and
fourth moment at most `3` imply `P[Z > 1 / 8] ≥ 1 / 36`. -/
theorem fourthMoment_positive_tail {α : Type*} (s : Finset α) (w Z : α → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hmass : ∑ i ∈ s, w i = 1)
    (hmean : ∑ i ∈ s, w i * Z i = 0)
    (hsecond : ∑ i ∈ s, w i * Z i ^ 2 = 1)
    (hthird : ∑ i ∈ s, w i * Z i ^ 3 = 0)
    (hfourth : ∑ i ∈ s, w i * Z i ^ 4 ≤ 3) :
    (1 / 36 : ℝ) ≤ ∑ i ∈ s, if 1 / 8 < Z i then w i else 0 :=
  fourthMoment_positive_tail_of_approx s w Z hw hmass
    (by rw [hmean]; norm_num) (by rw [hsecond]; norm_num)
    (by rw [hthird]; norm_num) (by linarith)

/-- **Exact fourth-moment negative-tail certificate:** exact normal moments through degree 3 and
fourth moment at most `3` imply `P[Z < -1 / 8] ≥ 1 / 36`. -/
theorem fourthMoment_negative_tail {α : Type*} (s : Finset α) (w Z : α → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hmass : ∑ i ∈ s, w i = 1)
    (hmean : ∑ i ∈ s, w i * Z i = 0)
    (hsecond : ∑ i ∈ s, w i * Z i ^ 2 = 1)
    (hthird : ∑ i ∈ s, w i * Z i ^ 3 = 0)
    (hfourth : ∑ i ∈ s, w i * Z i ^ 4 ≤ 3) :
    (1 / 36 : ℝ) ≤ ∑ i ∈ s, if Z i < -(1 / 8) then w i else 0 :=
  fourthMoment_negative_tail_of_approx s w Z hw hmass
    (by rw [hmean]; norm_num) (by rw [hsecond]; norm_num)
    (by rw [hthird]; norm_num) (by linarith)

end Cslib.Circuits.Frontier
