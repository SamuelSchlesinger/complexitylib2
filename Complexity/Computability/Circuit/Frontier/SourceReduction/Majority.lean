/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Frontier.SourceReduction.Moments
public import Complexity.Foundations.Data.BitString.Weight
import Mathlib.Tactic.Linarith

/-!
# Strict majority on non-oblivious bit-fixing sources via sign-sum tails

In [Chattopadhyay and Liao][ChattopadhyayLiao2022] (Lemma 5.4 and Theorem 2), the final stage of
the constant-error sumset extractor applies majority to `D` coordinates, of which `m` "good"
coordinates are almost four-wise independent and the remaining `D - m` "bad" coordinates may depend
arbitrarily on the good ones.

This module connects `Cslib.strictMajority` to the sign-sum tail bounds of
`Complexity.Computability.Circuit.Frontier.SourceReduction.Moments`:
1. **Deterministic margin robustness (`strictMajority_eq_true_of_margin`,
   `strictMajority_eq_false_of_margin`):** if the signed vote margin `voteMargin good x` on a subset
   `good ⊆ Fin n` exceeds the number `n - good.card` of remaining coordinates, `strictMajority n x`
   is forced to `true` (and symmetrically `false` when `voteMargin good x ≤ -(n - good.card)`),
   regardless of the values on the complement `goodᶜ`.
2. **Probabilistic outcome mass (`strictMajority_mass_ge_of_parityBias`):** if
   `good : Fin m ↪ Fin n` indexes `m` coordinates satisfying `ParityBiasBound` with
   `100 m^2 δ ≤ 1` and the bad-coordinate count satisfies `n - m ≤ √m / 8`, then
   `strictMajority n (x a)` takes each Boolean value `b` with probability mass at least `1 / 36`.

## Main definitions

* `Cslib.Circuits.Frontier.voteMargin`: signed vote margin
  `2 * #{i ∈ good | x i = true} - good.card` on a designated coordinate set `good`.

## Main results

* `Cslib.Circuits.Frontier.strictMajority_eq_true_of_margin`,
  `Cslib.Circuits.Frontier.strictMajority_eq_false_of_margin`: deterministic robustness of
  `strictMajority` against `n - good.card` arbitrary bad coordinates.
* `Cslib.Circuits.Frontier.signSum_eq_voteMargin`: the `±1` sign sum over `good : Fin m ↪ Fin n`
  equals `voteMargin (Finset.univ.map good)`.
* `Cslib.Circuits.Frontier.strictMajority_mass_ge_of_parityBias`: both Boolean outcomes of
  `strictMajority` have probability mass at least `1 / 36` under `ParityBiasBound`.

## References

* [E. Chattopadhyay and J.-J. Liao, *Extractors for Sum of Two Sources*][ChattopadhyayLiao2022]
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Cslib.BitString

/-- The signed vote margin (number of `true` votes minus number of `false` votes) on a designated
set `good` of coordinates. -/
def voteMargin {n : ℕ} (good : Finset (Fin n)) (x : BitString n) : ℤ :=
  2 * ((good.filter fun i => x i = true).card : ℤ) - good.card

private theorem count_good_le {n : ℕ} (good : Finset (Fin n)) (x : BitString n) :
    (good.filter fun i => x i = true).card ≤ weight x := by
  rw [weight]
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩

private theorem count_le_good_add_bad {n : ℕ} (good : Finset (Fin n)) (x : BitString n) :
    weight x ≤ (good.filter fun i => x i = true).card + (n - good.card) := by
  have hsub : Finset.univ.filter (fun i => x i = true) ⊆
      (good.filter fun i => x i = true) ∪ (Finset.univ \ good) := by
    intro i hi
    have hx : x i = true := (Finset.mem_filter.mp hi).2
    by_cases hg : i ∈ good
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hg, hx⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hg⟩)
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simpa only [weight, Finset.card_sdiff_of_subset (Finset.subset_univ good),
    Finset.card_univ, Fintype.card_fin] using h

/-- **Deterministic positive margin:** if the signed vote margin on `good` is strictly larger than
the number `n - good.card` of remaining coordinates, then `strictMajority n x = true`, regardless of
how the remaining coordinates vote. -/
theorem strictMajority_eq_true_of_margin {n : ℕ} {good : Finset (Fin n)}
    {x : BitString n} (h : ((n - good.card : ℕ) : ℤ) < voteMargin good x) :
    strictMajority n x = true := by
  have hg : good.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ good
  have hc := count_good_le good x
  simp only [voteMargin] at h
  rw [strictMajority_eq_true_iff]
  omega

/-- **Deterministic negative margin:** if the signed vote margin on `good` is at most
`-(n - good.card)`, then `strictMajority n x = false`, even if every coordinate outside `good` votes
`true`. -/
theorem strictMajority_eq_false_of_margin {n : ℕ} {good : Finset (Fin n)}
    {x : BitString n} (h : voteMargin good x ≤ -((n - good.card : ℕ) : ℤ)) :
    strictMajority n x = false := by
  have hg : good.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ good
  have hc := count_le_good_add_bad good x
  simp only [voteMargin] at h
  rw [strictMajority_eq_false_iff]
  omega

/-- The `±1` sign sum over an embedded coordinate set `good : Fin m ↪ Fin n` equals the integer
`voteMargin` on `Finset.univ.map good`. -/
theorem signSum_eq_voteMargin {α : Type*} {m n : ℕ}
    (good : Fin m ↪ Fin n) (x : α → BitString n) (a : α) :
    signSum (fun a i => if x a (good i) then 1 else -1) a =
      (voteMargin (Finset.univ.map good) (x a) : ℝ) := by
  unfold signSum
  calc
    _ = ∑ i, (2 * (if x a (good i) then (1 : ℝ) else 0) - 1) := by
      apply Finset.sum_congr rfl
      intro i _
      cases h : x a (good i) <;> norm_num [h]
    _ = 2 * ((Finset.univ.filter fun i => x a (good i) = true).card : ℝ) - m := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp
    _ = _ := by simp [voteMargin, Finset.filter_map]

/-- If the sign sum on `good : Fin m ↪ Fin n` exceeds `n - m`, then `strictMajority n (x a)` is
`true`. -/
theorem strictMajority_eq_true_of_signSum {α : Type*} {m n : ℕ} (good : Fin m ↪ Fin n)
    (x : α → BitString n) (a : α)
    (margin : ((n - m : ℕ) : ℝ) < signSum (fun a i => if x a (good i) then 1 else -1) a) :
    strictMajority n (x a) = true := by
  apply strictMajority_eq_true_of_margin (good := Finset.univ.map good)
  have h := margin
  rw [signSum_eq_voteMargin] at h
  exact_mod_cast (by simpa using h :
    (((n - (Finset.univ.map good).card : ℕ) : ℤ) : ℝ) <
      (voteMargin (Finset.univ.map good) (x a) : ℝ))

/-- If the sign sum on `good : Fin m ↪ Fin n` is at most `-(n - m)`, then `strictMajority n (x a)`
is `false`. -/
theorem strictMajority_eq_false_of_signSum {α : Type*} {m n : ℕ} (good : Fin m ↪ Fin n)
    (x : α → BitString n) (a : α)
    (margin : signSum (fun a i => if x a (good i) then 1 else -1) a ≤ -((n - m : ℕ) : ℝ)) :
    strictMajority n (x a) = false := by
  apply strictMajority_eq_false_of_margin (good := Finset.univ.map good)
  have h := margin
  rw [signSum_eq_voteMargin] at h
  exact_mod_cast (by simpa using h :
    (voteMargin (Finset.univ.map good) (x a) : ℝ) ≤
      -((((n - (Finset.univ.map good).card : ℕ) : ℤ) : ℝ)))

/-- Tail lower bounds beyond `± t` (with `n - m ≤ t`) for the sign sum on `good` transfer directly
to probability lower bounds for both Boolean outcomes of `strictMajority n`. -/
theorem strictMajority_mass_ge_of_signSum_tails {α : Type*} {m n : ℕ}
    (good : Fin m ↪ Fin n) (x : α → BitString n) (s : Finset α) (w : α → ℝ)
    {t ρ : ℝ} (hw : ∀ a ∈ s, 0 ≤ w a) (bad : ((n - m : ℕ) : ℝ) ≤ t)
    (positive : ρ ≤ ∑ a ∈ s,
      if t < signSum (fun a i => if x a (good i) then 1 else -1) a then w a else 0)
    (negative : ρ ≤ ∑ a ∈ s,
      if signSum (fun a i => if x a (good i) then 1 else -1) a < -t then w a else 0)
    (b : Bool) : ρ ≤ ∑ a ∈ s, if strictMajority n (x a) = b then w a else 0 := by
  cases b
  · apply negative.trans
    apply Finset.sum_le_sum
    intro a ha
    by_cases h : signSum (fun a i => if x a (good i) then 1 else -1) a < -t
    · have verdict := strictMajority_eq_false_of_signSum good x a
        (h.le.trans (neg_le_neg bad))
      simp [h, verdict]
    · rw [ite_eq_right_iff.mpr (fun h' => (h h').elim)]
      split_ifs with hv
      · exact hw a ha
      · exact le_rfl
  · apply positive.trans
    apply Finset.sum_le_sum
    intro a ha
    by_cases h : t < signSum (fun a i => if x a (good i) then 1 else -1) a
    · have verdict := strictMajority_eq_true_of_signSum good x a (bad.trans_lt h)
      simp [h, verdict]
    · rw [ite_eq_right_iff.mpr (fun h' => (h h').elim)]
      split_ifs with hv
      · exact hw a ha
      · exact le_rfl

/-- **Strict majority outcome mass from `ParityBiasBound`:** if `good : Fin m ↪ Fin n` indexes
`m > 0` coordinates whose `±1` signs satisfy `ParityBiasBound s w _ δ` with `100 m^2 δ ≤ 1`, and the
number of remaining coordinates satisfies `n - m ≤ √m / 8`, then both Boolean outcomes of
`strictMajority n (x a)` have `w`-mass at least `1 / 36`. -/
theorem strictMajority_mass_ge_of_parityBias {α : Type*} {m n : ℕ}
    {s : Finset α} {w : α → ℝ} (good : Fin m ↪ Fin n) (x : α → BitString n)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hmass : ∑ a ∈ s, w a = 1) (hm : 0 < m)
    {δ : ℝ} (hδ : 0 ≤ δ) (budget : 100 * (m : ℝ) ^ 2 * δ ≤ 1)
    (bias : ParityBiasBound s w (fun a i => if x a (good i) then 1 else -1) δ)
    (bad : ((n - m : ℕ) : ℝ) ≤ Real.sqrt (m : ℝ) / 8) (b : Bool) :
    (1 / 36 : ℝ) ≤ ∑ a ∈ s, if strictMajority n (x a) = b then w a else 0 := by
  have signs : ∀ a ∈ s, ∀ i,
      (if x a (good i) then (1 : ℝ) else -1) = 1 ∨
        (if x a (good i) then (1 : ℝ) else -1) = -1 := by
    intro a _ i
    split_ifs <;> simp
  exact strictMajority_mass_ge_of_signSum_tails good x s w hw bad
    (signSum_positive_tail_of_parityBias hw hmass hm signs hδ budget bias)
    (signSum_negative_tail_of_parityBias hw hmass hm signs hδ budget bias) b

end Cslib.Circuits.Frontier
