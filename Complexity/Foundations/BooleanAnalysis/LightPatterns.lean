/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.Bernoulli
public import Complexity.Foundations.BooleanAnalysis.HarmonicMean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Korten's improved light-patterns lemma

Lemma 10 of [Korten2026].

`improved_light_patterns` uses an arbitrary nonnegative real probability mass
function summing to one. The pointwise bound `mass x ≤ 2 ^ (k - Fintype.card ι)` expresses
min-entropy deficit at most `k`. With probability at least `63/64` over
independent coordinate sampling of rate `r ≤ 1/(512*k)`, at most `2^(|R|-k)`
patterns have marginal probability at most `2^(-|R|-2*k-2)`.

`improved_light_patterns_density` gives the equivalent fraction statement for
normalized densities. `coordinateMarginal_normalize` verifies the passage from
probability masses to normalized marginal densities. All results include
arbitrary finite coordinate types, dimension zero, zero masses, and sampling rate
zero. `Complexity.Foundations.BooleanAnalysis.MirrorSets` applies this lemma in the
improved mirror-set argument.
-/

@[expose] public section

/-! ### Marginal probability masses on coordinate patterns

The marginal of a finite real-valued probability mass function is the sum of
its masses over all completions of a selected-coordinate pattern. This differs
from `coordinateMarginal`, which averages normalized densities.
-/


namespace Cslib.BooleanAnalysis

open scoped BigOperators

/-- Sum of the masses of all completions of a coordinate pattern. For a
nonnegative mass function summing to one, this is the probability of the pattern. -/
noncomputable def coordinateMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mass : (ι → Bool) → ℝ) (selected : ι → Bool)
    (pattern : {i // selected i = true} → Bool) : ℝ :=
  ∑ rest : {i // selected i ≠ true} → Bool,
    mass (fun i => if h : selected i = true then pattern ⟨i, h⟩ else rest ⟨i, h⟩)

end Cslib.BooleanAnalysis

/-! ### Proof of Korten's improved light-patterns lemma

Theorem specialization for Lemma 10 of [Korten2026].

Transfer the downward-closed event that the harmonic transform is large,
then bound light patterns by the reciprocal-density Markov inequality.
The final step converts normalized marginal densities into probability masses
and counts, preserving the paper's real deficit parameter and constants.
-/


namespace Cslib.BooleanAnalysis

open Finset
open scoped BigOperators

theorem harmonicTransform_sparse_good_probability_fin {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hmean : (𝔼 x, f x) = 1) {k r : ℝ} (hk : 1 ≤ k)
    (hbound : ∀ x, f x ≤ (2 : ℝ) ^ k) (hr : 0 ≤ r) (hr' : r ≤ 1 / (512 * k)) :
    63 / 64 ≤ bernoulliAverage r
      (fun s => if 1 / (4 * (2 : ℝ) ^ k) ≤ harmonicTransform f s then 1 else 0) := by
  let B : ℝ := (2 : ℝ) ^ k
  let a : ℝ := 1 / (2 * Real.sqrt B)
  let A : Set (Fin n → Bool) := {s | 1 / (4 * B) ≤ harmonicTransform f s}
  have hB : 1 ≤ B := Real.one_le_rpow (by norm_num) (by linarith)
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have ha : 0 < a := by dsimp [a]; positivity
  have hA : IsLowerSet A := by
    intro s t hst ht
    exact ht.trans (harmonicTransform_antitone hf fun i hi => Bool.le_iff_imp.mp (hst i) hi)
  have hA' : A.Nonempty := by
    refine ⟨fun _ => false, ?_⟩
    change 1 / (4 * B) ≤ harmonicTransform f (fun _ => false)
    rw [harmonicTransform_empty, hmean]
    apply (div_le_one (by positivity)).mpr
    linarith
  have hkr : r * (512 * k) ≤ 1 := (le_div_iff₀ (by positivity)).mp hr'
  have hrk : r ≤ r * k := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hk)]
  have hr20 : r ≤ 1 / 20 := by nlinarith
  have hgood : a ≤ bernoulliAverage (1 / 4) (fun s => if s ∈ A then (1 : ℝ) else 0) :=
    harmonicTransform_good_probability hf hmean hB hbound
  have htransfer := (Real.rpow_le_rpow ha.le hgood (by positivity : 0 ≤ 5 * r)).trans
    (bernoulliAverage_lowerSet_transfer hA hA' hr hr20)
  have hlog : Real.log a = -(k / 2 + 1) * Real.log 2 := by
    dsimp [a]
    rw [Real.log_div one_ne_zero (by positivity), Real.log_one,
      Real.log_mul (by norm_num) (by positivity), Real.log_sqrt hBp.le]
    dsimp [B]
    rw [Real.log_rpow (by norm_num)]
    ring
  have he := Real.add_one_le_exp (Real.log a * (5 * r))
  rw [← Real.rpow_def_of_pos ha] at he
  rw [hlog] at he
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hloss : (k / 2 + 1) * (5 * r) * Real.log 2 ≤ (k / 2 + 1) * (5 * r) :=
    mul_le_of_le_one_right (by positivity) hlog2
  change 63 / 64 ≤ bernoulliAverage r (fun s => if s ∈ A then (1 : ℝ) else 0)
  nlinarith

/-- Sparse-sampling estimate for the harmonic transform in the proof of Lemma 10. -/
theorem harmonicTransform_sparse_good_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (hmean : (𝔼 x, f x) = 1)
    {k r : ℝ} (hk : 1 ≤ k) (hbound : ∀ x, f x ≤ (2 : ℝ) ^ k)
    (hr : 0 ≤ r) (hr' : r ≤ 1 / (512 * k)) :
    63 / 64 ≤ bernoulliAverage r
      (fun s => if 1 / (4 * (2 : ℝ) ^ k) ≤ harmonicTransform f s then 1 else 0) := by
  let e := (Fintype.equivFin ι).symm
  have hmean' : (𝔼 x : Fin (Fintype.card ι) → Bool,
      f (fun j => x (e.symm j))) = 1 := by
    exact (Fintype.expect_equiv (Equiv.arrowCongr e (Equiv.refl Bool))
      (fun x => f (fun j => x (e.symm j))) f (fun _ => rfl)).trans hmean
  have h := harmonicTransform_sparse_good_probability_fin
    (fun x => hf (fun j => x (e.symm j))) hmean' hk (fun x => hbound _) hr hr'
  simp_rw [harmonicTransform_reindex e] at h
  rwa [bernoulliAverage_reindex e r
    (fun s => if 1 / (4 * (2 : ℝ) ^ k) ≤ harmonicTransform f s then 1 else 0)] at h

/-- Lemma 10 for normalized densities: with probability at least `63/64`, the
fraction of patterns with marginal density at most `2^(-2*k-2)` is at most `2^-k`. -/
theorem improved_light_patterns_density {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hmean : (𝔼 x, f x) = 1) {k r : ℝ} (hk : 1 ≤ k)
    (hbound : ∀ x, f x ≤ (2 : ℝ) ^ k) (hr : 0 ≤ r) (hr' : r ≤ 1 / (512 * k)) :
    63 / 64 ≤ bernoulliAverage r (fun s =>
      if (𝔼 z, if coordinateMarginal f s z ≤ (2 : ℝ) ^ (-2 * k - 2) then (1 : ℝ) else 0) ≤
        (2 : ℝ) ^ (-k) then 1 else 0) := by
  have ht : (2 : ℝ) ^ (-2 * k - 2) / (1 / (4 * (2 : ℝ) ^ k)) = (2 : ℝ) ^ (-k) := by
    have hfour : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
    rw [one_div, div_inv_eq_mul, hfour, ← Real.rpow_add (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hkr : r * (512 * k) ≤ 1 := (le_div_iff₀ (by positivity)).mp hr'
  have hr1 : r ≤ 1 := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hk)]
  refine (harmonicTransform_sparse_good_probability hf hmean hk hbound hr hr').trans
    (bernoulliAverage_mono hr hr1 fun s => ?_)
  by_cases hs : 1 / (4 * (2 : ℝ) ^ k) ≤ harmonicTransform f s
  · have hlight := coordinateMarginal_light_fraction_le hf s (by positivity) hs
      (by positivity : 0 ≤ (2 : ℝ) ^ (-2 * k - 2))
    rw [ht] at hlight
    simp only [ite_eq_left hs, ite_eq_left hlight, le_refl]
  · rw [ite_eq_right hs]
    split_ifs <;> norm_num

/-- Normalizing the input mass by `2^n` normalizes each marginal by `2^|R|`. -/
theorem coordinateMarginal_normalize {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mass : (ι → Bool) → ℝ) (s : ι → Bool)
    (z : {i // s i = true} → Bool) :
    coordinateMarginal (fun x => (2 : ℝ) ^ Fintype.card ι * mass x) s z =
      (2 : ℝ) ^ Fintype.card {i // s i = true} * coordinateMass mass s z := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => s i = true) (fun _ => Bool)
  have hc : (2 : ℝ) ^ Fintype.card ι =
      (2 : ℝ) ^ Fintype.card {i // s i = true} *
        (Fintype.card ({i // s i ≠ true} → Bool) : ℝ) := by
    have h := Fintype.card_congr e
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_prod] at h
    simp only [Fintype.card_fun, Fintype.card_bool]
    exact_mod_cast h
  unfold coordinateMarginal coordinateMass
  rw [Fintype.expect_eq_sum_div_card, ← mul_sum, hc]
  have hp : (0 : ℝ) < Fintype.card ({i // s i ≠ true} → Bool) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ({i // s i ≠ true} → Bool))
  field_simp

/-- Korten's improved light-patterns lemma (Lemma 10), with its exact constants
and pattern count. Nonnegative masses summing to one represent a distribution;
the pointwise bound is min-entropy deficit at most the real parameter `k`. -/
theorem improved_light_patterns {ι : Type*} [Fintype ι] [DecidableEq ι]
    {mass : (ι → Bool) → ℝ}
    (hm : ∀ x, 0 ≤ mass x) (hmean : (∑ x, mass x) = 1) {k r : ℝ} (hk : 1 ≤ k)
    (hbound : ∀ x, mass x ≤ (2 : ℝ) ^ (k - Fintype.card ι))
    (hr : 0 ≤ r) (hr' : r ≤ 1 / (512 * k)) :
    63 / 64 ≤ bernoulliAverage r (fun s =>
      if ((univ.filter fun z => coordinateMass mass s z ≤
          (2 : ℝ) ^ (-(Fintype.card {i // s i = true} : ℝ) - 2 * k - 2)).card : ℝ) ≤
        (2 : ℝ) ^ ((Fintype.card {i // s i = true} : ℝ) - k) then 1 else 0) := by
  let f : (ι → Bool) → ℝ := fun x => (2 : ℝ) ^ Fintype.card ι * mass x
  have hf : ∀ x, 0 ≤ f x := fun x => mul_nonneg (by positivity) (hm x)
  have hsum : (𝔼 x, f x) = 1 := by
    dsimp [f]
    rw [Fintype.expect_eq_sum_div_card, ← mul_sum, hmean]
    simp
  have hproduct : (2 : ℝ) ^ Fintype.card ι * (2 : ℝ) ^ (k - Fintype.card ι) = (2 : ℝ) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hfb : ∀ x, f x ≤ (2 : ℝ) ^ k := by
    intro x
    exact (mul_le_mul_of_nonneg_left (hbound x) (by positivity)).trans_eq hproduct
  have hkr : r * (512 * k) ≤ 1 := (le_div_iff₀ (by positivity)).mp hr'
  have hr1 : r ≤ 1 := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hk)]
  refine (improved_light_patterns_density hf hsum hk hfb hr hr').trans
    (bernoulliAverage_mono hr hr1 fun s => ?_)
  let m := Fintype.card {i // s i = true}
  have hp : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hthreshold : (2 : ℝ) ^ m * (2 : ℝ) ^ (-(m : ℝ) - 2 * k - 2) =
      (2 : ℝ) ^ (-2 * k - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hcount : (2 : ℝ) ^ (-k) * (2 : ℝ) ^ m = (2 : ℝ) ^ ((m : ℝ) - k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have he (z : {i // s i = true} → Bool) :
      coordinateMarginal f s z ≤ (2 : ℝ) ^ (-2 * k - 2) ↔
        coordinateMass mass s z ≤ (2 : ℝ) ^ (-(m : ℝ) - 2 * k - 2) := by
    change coordinateMarginal (fun x => (2 : ℝ) ^ Fintype.card ι * mass x) s z ≤ _ ↔ _
    rw [coordinateMarginal_normalize, ← hthreshold]
    exact mul_le_mul_iff_right₀ hp
  have havg : (𝔼 z, if coordinateMarginal f s z ≤ (2 : ℝ) ^ (-2 * k - 2) then
        (1 : ℝ) else 0) =
      ((univ.filter fun z => coordinateMass mass s z ≤
        (2 : ℝ) ^ (-(m : ℝ) - 2 * k - 2)).card : ℝ) / (2 : ℝ) ^ m := by
    simp_rw [he]
    rw [Fintype.expect_eq_sum_div_card]
    simp [m]
  simp only [havg, div_le_iff₀ hp, hcount]
  exact le_rfl

/-- Marginalization preserves total probability mass. -/
theorem sum_coordinateMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mass : (ι → Bool) → ℝ) (s : ι → Bool) :
    (∑ z, coordinateMass mass s z) = ∑ x, mass x := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => s i = true) (fun _ => Bool)
  rw [← e.symm.sum_comp mass, Fintype.sum_prod_type]
  rfl

end Cslib.BooleanAnalysis



namespace Cslib.BooleanAnalysis

open Finset
open scoped BigOperators

/-- Marginal masses of a nonnegative mass function are nonnegative. -/
theorem coordinateMass_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {mass : (ι → Bool) → ℝ} (hm : ∀ x, 0 ≤ mass x) (s : ι → Bool)
    (z : {i // s i = true} → Bool) : 0 ≤ coordinateMass mass s z :=
  sum_nonneg fun _ _ => hm _

end Cslib.BooleanAnalysis
