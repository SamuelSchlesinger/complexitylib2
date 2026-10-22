/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Frontier.SourceReduction.FourthMoment
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Moments and tails of almost four-wise independent sign sums

When `m` sign variables `σ a 0, …, σ a (m - 1) ∈ {-1, 1}` have bias at most `δ` on every nonempty
parity of size at most `4` (`ParityBiasBound s w σ δ`), the first four moments of their sum
`signSum σ a = ∑ i, σ a i` are close to the moments `(0, m, 0, 3 m^2)` of an independent sign sum:
* `|E[S]| ≤ m δ` (`signSum_first_moment`),
* `|E[S^2] - m| ≤ m^2 δ` (`signSum_second_moment`),
* `|E[S^3]| ≤ m^3 δ` (`signSum_third_moment`),
* `E[S^4] ≤ 3 m^2 + m^4 δ` (`signSum_fourth_moment`).

Dividing by `√m` and applying the quartic certificates of
`Complexity.Computability.Circuit.Frontier.SourceReduction.FourthMoment` shows that whenever
`100 m^2 δ ≤ 1`, both tails `{a | √m / 8 < signSum σ a}` and `{a | signSum σ a < -√m / 8}` have
probability mass at least `1 / 36` (`signSum_positive_tail_of_parityBias`,
`signSum_negative_tail_of_parityBias`).

## Main definitions

* `Cslib.Circuits.Frontier.weightedMean`: expectation of `X : α → ℝ` under weight `w` on `s`.
* `Cslib.Circuits.Frontier.signSum`: sum `∑ i : Fin m, σ a i` of `m` real-valued coordinates.
* `Cslib.Circuits.Frontier.ParityBiasBound`: every nonempty product of at most `4` coordinates has
  weighted mean at most `δ` in absolute value.

## Main results

* `Cslib.Circuits.Frontier.signSum_first_moment`,
  `Cslib.Circuits.Frontier.signSum_second_moment`,
  `Cslib.Circuits.Frontier.signSum_third_moment`,
  `Cslib.Circuits.Frontier.signSum_fourth_moment`: moment bounds from `ParityBiasBound`.
* `Cslib.Circuits.Frontier.signSum_positive_tail_of_parityBias`,
  `Cslib.Circuits.Frontier.signSum_negative_tail_of_parityBias`: tail mass at least `1 / 36` beyond
  `± √m / 8` when `100 m^2 δ ≤ 1`.

## References

* [E. Chattopadhyay and J.-J. Liao, *Extractors for Sum of Two Sources*][ChattopadhyayLiao2022]
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

/-- Weighted sum `∑ a ∈ s, w a * X a`, representing expectation when `w` is a probability weight on
`s`. -/
def weightedMean {α : Type*} (s : Finset α) (w X : α → ℝ) : ℝ :=
  ∑ a ∈ s, w a * X a

/-- Sum of `m` real-valued (typically `±1`) coordinates at sample point `a`. -/
def signSum {α : Type*} {m : ℕ} (σ : α → Fin m → ℝ) (a : α) : ℝ :=
  ∑ i : Fin m, σ a i

/-- `ParityBiasBound s w σ δ` states that every nonempty product of at most `4` distinct coordinates
has `w`-weighted mean at most `δ` in absolute value. -/
def ParityBiasBound {α : Type*} {m : ℕ} (s : Finset α) (w : α → ℝ)
    (σ : α → Fin m → ℝ) (δ : ℝ) : Prop :=
  ∀ T : Finset (Fin m), T.Nonempty → T.card ≤ 4 →
    |weightedMean s w (fun a => ∏ i ∈ T, σ a i)| ≤ δ

private theorem mean_congr {α : Type*} {s : Finset α} {w X Y : α → ℝ}
    (h : ∀ a ∈ s, X a = Y a) : weightedMean s w X = weightedMean s w Y := by
  apply Finset.sum_congr rfl
  intro a ha
  rw [h a ha]

private theorem mean_sum {α ι : Type*} [Fintype ι]
    (s : Finset α) (w : α → ℝ) (X : α → ι → ℝ) :
    weightedMean s w (fun a => ∑ i, X a i) =
      ∑ i, weightedMean s w (fun a => X a i) := by
  unfold weightedMean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem abs_sum_le_mul {m : ℕ} {f : Fin m → ℝ} {δ : ℝ}
    (h : ∀ i, |f i| ≤ δ) : |∑ i, f i| ≤ m * δ := by
  calc
    |∑ i, f i| ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin m, δ := Finset.sum_le_sum fun i _ => h i
    _ = m * δ := by simp

private theorem bias_one {α : Type*} {m : ℕ} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} {δ : ℝ} (h : ParityBiasBound s w σ δ) (i : Fin m) :
    |weightedMean s w (fun a => σ a i)| ≤ δ := by
  simpa using h {i} (by simp) (by simp)

private theorem bias_two {α : Type*} {m : ℕ} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} {δ : ℝ} (h : ParityBiasBound s w σ δ)
    {i j : Fin m} (hij : i ≠ j) :
    |weightedMean s w (fun a => σ a i * σ a j)| ≤ δ := by
  simpa [Finset.prod_pair hij] using h {i, j} (by simp) (by simp [hij])

private theorem mean_sign_square {α : Type*} {m : ℕ} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} (hmass : ∑ a ∈ s, w a = 1)
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1) (i : Fin m) :
    weightedMean s w (fun a => σ a i * σ a i) = 1 := by
  calc
    _ = weightedMean s w (fun _ => 1) := mean_congr fun a ha => by
      rcases hσ a ha i with h | h <;> rw [h] <;> norm_num
    _ = 1 := by simpa [weightedMean] using hmass

private theorem bias_two_centered {α : Type*} {m : ℕ} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) (hmass : ∑ a ∈ s, w a = 1)
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1)
    (h : ParityBiasBound s w σ δ) (i j : Fin m) :
    |weightedMean s w (fun a => σ a i * σ a j) - if i = j then 1 else 0| ≤ δ := by
  by_cases hij : i = j
  · subst j
    simpa [mean_sign_square hmass hσ] using hδ
  · simpa [hij] using bias_two h hij

/-- **First moment of `signSum`:** if every singleton parity has bias at most `δ`, the mean of
`signSum σ` is at most `m * δ` in absolute value. -/
theorem signSum_first_moment {α : Type*} {m : ℕ} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} {δ : ℝ} (h : ParityBiasBound s w σ δ) :
    |weightedMean s w (signSum σ)| ≤ m * δ := by
  change |weightedMean s w (fun a => ∑ i, σ a i)| ≤ m * δ
  rw [mean_sum]
  exact abs_sum_le_mul (bias_one h)

/-- **Second moment of `signSum`:** if `σ` takes `±1` values and every pair parity has bias at most
`δ`, the second moment of `signSum σ` is within `m^2 * δ` of `m`. -/
theorem signSum_second_moment {α : Type*} {m : ℕ} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) (hmass : ∑ a ∈ s, w a = 1)
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1)
    (h : ParityBiasBound s w σ δ) :
    |weightedMean s w (fun a => signSum σ a ^ 2) - m| ≤ (m : ℝ) ^ 2 * δ := by
  have hexpand : weightedMean s w (fun a => signSum σ a ^ 2) =
      ∑ i, ∑ j, weightedMean s w (fun a => σ a i * σ a j) := by
    simp only [signSum, pow_two, Finset.sum_mul_sum, mean_sum]
  have hdiag : (∑ i : Fin m, ∑ j : Fin m, if i = j then (1 : ℝ) else 0) = m := by
    simp
  conv_lhs => rw [hexpand, ← hdiag, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ (m : ℝ) * (m * δ) :=
      abs_sum_le_mul fun i => abs_sum_le_mul (bias_two_centered hδ hmass hσ h i)
    _ = (m : ℝ) ^ 2 * δ := by ring

private theorem bias_three {α : Type*} {m : ℕ} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} {δ : ℝ}
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1)
    (h : ParityBiasBound s w σ δ) (i j k : Fin m) :
    |weightedMean s w (fun a => σ a i * σ a j * σ a k)| ≤ δ := by
  by_cases hij : i = j
  · subst j
    have heq : weightedMean s w (fun a => σ a i * σ a i * σ a k) =
        weightedMean s w (fun a => σ a k) := mean_congr fun a ha => by
      rcases hσ a ha i with h | h <;> rw [h] <;> ring
    rw [heq]
    exact bias_one h k
  by_cases hik : i = k
  · subst k
    have heq : weightedMean s w (fun a => σ a i * σ a j * σ a i) =
        weightedMean s w (fun a => σ a j) := mean_congr fun a ha => by
      rcases hσ a ha i with h | h <;> rw [h] <;> ring
    rw [heq]
    exact bias_one h j
  by_cases hjk : j = k
  · subst k
    have heq : weightedMean s w (fun a => σ a i * σ a j * σ a j) =
        weightedMean s w (fun a => σ a i) := mean_congr fun a ha => by
      rcases hσ a ha j with h | h <;> rw [h] <;> ring
    rw [heq]
    exact bias_one h i
  simpa [hij, hik, hjk, mul_assoc] using h {i, j, k} (by simp) (by simp [hij, hik, hjk])

private theorem indicator_nonneg (p : Prop) [Decidable p] :
    (0 : ℝ) ≤ if p then 1 else 0 := by
  split_ifs <;> norm_num

private theorem mean_four_le {α : Type*} {m : ℕ} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) (hmass : ∑ a ∈ s, w a = 1)
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1)
    (h : ParityBiasBound s w σ δ) (i j k l : Fin m) :
    weightedMean s w (fun a => σ a i * σ a j * σ a k * σ a l) ≤
      δ + (if i = j ∧ k = l then 1 else 0) +
        (if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0) := by
  by_cases hij : i = j
  · subst j
    have heq : weightedMean s w (fun a => σ a i * σ a i * σ a k * σ a l) =
        weightedMean s w (fun a => σ a k * σ a l) := mean_congr fun a ha => by
      rcases hσ a ha i with h | h <;> rw [h] <;> ring
    rw [heq]
    simp only [true_and]
    have hkl := (abs_le.mp (bias_two_centered hδ hmass hσ h k l)).2
    have h2 := indicator_nonneg (i = k ∧ i = l)
    have h3 := indicator_nonneg (i = l ∧ i = k)
    linarith
  by_cases hik : i = k
  · subst k
    have heq : weightedMean s w (fun a => σ a i * σ a j * σ a i * σ a l) =
        weightedMean s w (fun a => σ a j * σ a l) := mean_congr fun a ha => by
      rcases hσ a ha i with h | h <;> rw [h] <;> ring
    rw [heq]
    simp only [hij, false_and, ite_false, add_zero, true_and]
    have hjl := (abs_le.mp (bias_two_centered hδ hmass hσ h j l)).2
    have h3 := indicator_nonneg (i = l ∧ j = i)
    linarith
  by_cases hil : i = l
  · subst l
    have heq : weightedMean s w (fun a => σ a i * σ a j * σ a k * σ a i) =
        weightedMean s w (fun a => σ a j * σ a k) := mean_congr fun a ha => by
      rcases hσ a ha i with h | h <;> rw [h] <;> ring
    rw [heq]
    simp only [hij, hik, false_and, ite_false, add_zero, true_and]
    have hjk := (abs_le.mp (bias_two_centered hδ hmass hσ h j k)).2
    linarith
  simp only [hij, hik, hil, false_and, ite_false, add_zero]
  apply (le_abs_self _).trans
  by_cases hjk : j = k
  · subst k
    have heq : weightedMean s w (fun a => σ a i * σ a j * σ a j * σ a l) =
        weightedMean s w (fun a => σ a i * σ a l) := mean_congr fun a ha => by
      rcases hσ a ha j with h | h <;> rw [h] <;> ring
    rw [heq]
    exact bias_two h hil
  by_cases hjl : j = l
  · subst l
    have heq : weightedMean s w (fun a => σ a i * σ a j * σ a k * σ a j) =
        weightedMean s w (fun a => σ a i * σ a k) := mean_congr fun a ha => by
      rcases hσ a ha j with h | h <;> rw [h] <;> ring
    rw [heq]
    exact bias_two h hik
  by_cases hkl : k = l
  · subst l
    have heq : weightedMean s w (fun a => σ a i * σ a j * σ a k * σ a k) =
        weightedMean s w (fun a => σ a i * σ a j) := mean_congr fun a ha => by
      rcases hσ a ha k with h | h <;> rw [h] <;> ring
    rw [heq]
    exact bias_two h hij
  simpa [hij, hik, hil, hjk, hjl, hkl, mul_assoc] using
    h {i, j, k, l} (by simp) (by simp [hij, hik, hil, hjk, hjl, hkl])

/-- **Third moment of `signSum`:** if `σ` takes `±1` values and every nonempty parity of size at
most `3` has bias at most `δ`, the third moment of `signSum σ` is at most `m^3 * δ` in absolute
value. -/
theorem signSum_third_moment {α : Type*} {m : ℕ} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} {δ : ℝ}
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1)
    (h : ParityBiasBound s w σ δ) :
    |weightedMean s w (fun a => signSum σ a ^ 3)| ≤ (m : ℝ) ^ 3 * δ := by
  have hexpand : weightedMean s w (fun a => signSum σ a ^ 3) =
      ∑ i, ∑ j, ∑ k, weightedMean s w (fun a => σ a i * σ a j * σ a k) := by
    simp only [signSum, pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum, mean_sum]
    simp only [mul_comm, mul_left_comm]
  rw [hexpand]
  calc
    _ ≤ (m : ℝ) * (m * (m * δ)) :=
      abs_sum_le_mul fun i => abs_sum_le_mul fun j => abs_sum_le_mul (bias_three hσ h i j)
    _ = (m : ℝ) ^ 3 * δ := by ring

/-- **Fourth moment of `signSum`:** if `σ` takes `±1` values and every nonempty parity of size at
most `4` has bias at most `δ`, the fourth moment of `signSum σ` is at most `3 m^2 + m^4 * δ`. -/
theorem signSum_fourth_moment {α : Type*} {m : ℕ} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) (hmass : ∑ a ∈ s, w a = 1)
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1)
    (h : ParityBiasBound s w σ δ) :
    weightedMean s w (fun a => signSum σ a ^ 4) ≤
      3 * (m : ℝ) ^ 2 + (m : ℝ) ^ 4 * δ := by
  have hexpand : weightedMean s w (fun a => signSum σ a ^ 4) =
      ∑ i, ∑ j, ∑ k, ∑ l,
        weightedMean s w (fun a => σ a i * σ a j * σ a k * σ a l) := by
    simp only [signSum, pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum, mean_sum]
    simp only [mul_comm, mul_left_comm]
  rw [hexpand]
  calc
    _ ≤ ∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m, ∑ l : Fin m,
        (δ + (if i = j ∧ k = l then 1 else 0) +
          (if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0)) := by
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ =>
          mean_four_le hδ hmass hσ h i j k l
    _ = 3 * (m : ℝ) ^ 2 + (m : ℝ) ^ 4 * δ := by
      have h1 : (∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m, ∑ l : Fin m,
          if i = j ∧ k = l then (1 : ℝ) else 0) = (m : ℝ) ^ 2 := by
        simp [ite_and, ← sq]
      have h2 : (∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m, ∑ l : Fin m,
          if i = k ∧ j = l then (1 : ℝ) else 0) = (m : ℝ) ^ 2 := by
        simp [ite_and, ← sq]
      have h3 : (∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m, ∑ l : Fin m,
          if i = l ∧ j = k then (1 : ℝ) else 0) = (m : ℝ) ^ 2 := by
        simp [ite_and, ← sq]
      have h0 : (∑ _i : Fin m, ∑ _j : Fin m, ∑ _k : Fin m, ∑ _l : Fin m, δ) =
          (m : ℝ) ^ 4 * δ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      simp only [Finset.sum_add_distrib, h0, h1, h2, h3]
      ring

private theorem mean_div_pow {α : Type*} (s : Finset α) (w X : α → ℝ)
    (r : ℝ) (k : ℕ) :
    (∑ a ∈ s, w a * (X a / r) ^ k) =
      weightedMean s w (fun a => X a ^ k) / r ^ k := by
  simp only [div_pow]
  simp only [div_eq_mul_inv, weightedMean, Finset.sum_mul, mul_assoc]

/-- **Simultaneous positive and negative tail bounds for `signSum`:** if `m > 0`, `σ` takes `±1`
values, `ParityBiasBound s w σ δ` holds, and `100 m^2 δ ≤ 1`, then both tails beyond `± √m / 8`
have `w`-mass at least `1 / 36`. -/
theorem signSum_tails_of_parityBias {α : Type*} {m : ℕ} {s : Finset α}
    {w : α → ℝ} {σ : α → Fin m → ℝ} {δ : ℝ}
    (hw : ∀ a ∈ s, 0 ≤ w a) (hmass : ∑ a ∈ s, w a = 1) (hm : 0 < m)
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1)
    (hδ : 0 ≤ δ) (hbudget : 100 * (m : ℝ) ^ 2 * δ ≤ 1)
    (h : ParityBiasBound s w σ δ) :
    ((1 / 36 : ℝ) ≤ ∑ a ∈ s, if Real.sqrt (m : ℝ) / 8 < signSum σ a then w a else 0) ∧
      ((1 / 36 : ℝ) ≤ ∑ a ∈ s,
        if signSum σ a < -(Real.sqrt (m : ℝ) / 8) then w a else 0) := by
  let r := Real.sqrt (m : ℝ)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.succ_le_iff.mpr hm
  have hr1 : 1 ≤ r := by simpa only [r, Real.sqrt_one] using Real.sqrt_le_sqrt hm1
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hr2 : r ^ 2 = m := Real.sq_sqrt hm0.le
  have hr3 : r ^ 3 = (m : ℝ) * r := by
    calc
      r ^ 3 = r ^ 2 * r := by ring
      _ = (m : ℝ) * r := by rw [hr2]
  have hr4 : r ^ 4 = (m : ℝ) ^ 2 := by
    calc
      r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ = (m : ℝ) ^ 2 := by rw [hr2]
  have hb : (m : ℝ) ^ 2 * δ ≤ 1 / 100 := by nlinarith [hbudget]
  have h1 := signSum_first_moment h
  have h2 := signSum_second_moment hδ hmass hσ h
  have h3 := signSum_third_moment hσ h
  have h4 := signSum_fourth_moment hδ hmass hσ h
  have hmean : |∑ a ∈ s, w a * (signSum σ a / r)| ≤ 1 / 100 := by
    have heq : (∑ a ∈ s, w a * (signSum σ a / r)) =
        weightedMean s w (signSum σ) / r := by
      simpa only [pow_one] using mean_div_pow s w (signSum σ) r 1
    rw [heq, abs_div, abs_of_pos hr0, div_le_iff₀ hr0]
    have hmle : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    have hb1 := mul_le_mul_of_nonneg_right hmle hδ
    linarith
  have hsecond : (99 / 100 : ℝ) ≤ ∑ a ∈ s, w a * (signSum σ a / r) ^ 2 := by
    rw [mean_div_pow, hr2, le_div_iff₀ hm0]
    have hlow := (abs_le.mp h2).1
    linarith
  have hthird : |∑ a ∈ s, w a * (signSum σ a / r) ^ 3| ≤ 1 / 100 := by
    rw [mean_div_pow, abs_div, abs_of_pos (pow_pos hr0 _), div_le_iff₀ (pow_pos hr0 _)]
    have hb3 : (m : ℝ) ^ 3 * δ ≤ (m : ℝ) / 100 := by
      nlinarith [mul_le_mul_of_nonneg_left hb hm0.le]
    have hmle : (m : ℝ) ≤ r ^ 3 := by
      rw [hr3]
      exact le_mul_of_one_le_right hm0.le hr1
    linarith
  have hfourth : (∑ a ∈ s, w a * (signSum σ a / r) ^ 4) ≤ 301 / 100 := by
    rw [mean_div_pow, div_le_iff₀ (pow_pos hr0 _), hr4]
    have hb4 : (m : ℝ) ^ 4 * δ ≤ (m : ℝ) ^ 2 / 100 := by
      nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg (m : ℝ))]
    linarith
  have hpos := fourthMoment_positive_tail_of_approx s w (fun a => signSum σ a / r)
    hw hmass hmean hsecond hthird hfourth
  have hneg := fourthMoment_negative_tail_of_approx s w (fun a => signSum σ a / r)
    hw hmass hmean hsecond hthird hfourth
  have hpos_iff (a : α) : (1 / 8 : ℝ) < signSum σ a / r ↔ r / 8 < signSum σ a := by
    rw [lt_div_iff₀ hr0]
    ring_nf
  have hneg_iff (a : α) : signSum σ a / r < -(1 / 8 : ℝ) ↔ signSum σ a < -(r / 8) := by
    rw [div_lt_iff₀ hr0]
    ring_nf
  constructor
  · simpa only [hpos_iff] using hpos
  · simpa only [hneg_iff] using hneg

/-- **Positive tail of `signSum` beyond `√m / 8` has mass at least `1 / 36`.** -/
theorem signSum_positive_tail_of_parityBias {α : Type*} {m : ℕ} {s : Finset α}
    {w : α → ℝ} {σ : α → Fin m → ℝ} {δ : ℝ}
    (hw : ∀ a ∈ s, 0 ≤ w a) (hmass : ∑ a ∈ s, w a = 1) (hm : 0 < m)
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1)
    (hδ : 0 ≤ δ) (hbudget : 100 * (m : ℝ) ^ 2 * δ ≤ 1)
    (h : ParityBiasBound s w σ δ) :
    (1 / 36 : ℝ) ≤ ∑ a ∈ s, if Real.sqrt (m : ℝ) / 8 < signSum σ a then w a else 0 :=
  (signSum_tails_of_parityBias hw hmass hm hσ hδ hbudget h).1

/-- **Negative tail of `signSum` below `-√m / 8` has mass at least `1 / 36`.** -/
theorem signSum_negative_tail_of_parityBias {α : Type*} {m : ℕ} {s : Finset α}
    {w : α → ℝ} {σ : α → Fin m → ℝ} {δ : ℝ}
    (hw : ∀ a ∈ s, 0 ≤ w a) (hmass : ∑ a ∈ s, w a = 1) (hm : 0 < m)
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1)
    (hδ : 0 ≤ δ) (hbudget : 100 * (m : ℝ) ^ 2 * δ ≤ 1)
    (h : ParityBiasBound s w σ δ) :
    (1 / 36 : ℝ) ≤ ∑ a ∈ s, if signSum σ a < -(Real.sqrt (m : ℝ) / 8) then w a else 0 :=
  (signSum_tails_of_parityBias hw hmass hm hσ hδ hbudget h).2

end Cslib.Circuits.Frontier
