/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Extractor.Sumset
public import Complexity.Init
public import Complexity.Probability.MinEntropy
public import Complexity.Probability.Uniform

import Complexity.Probability.MinEntropy.Flat
import Complexity.Probability.StatisticalDistance
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Distributional two-source sumset extractors and flat-source equivalence

A function `E : G → β` on an additive type `G` is a `(k, δ)`-*sumset extractor*
(`IsSumsetExtractor E k δ`, in the sense of [Chattopadhyay and Liao][ChattopadhyayLiao2022]) if for
every pair of independent `k`-sources `X, Y : PMF G`, the distribution of `E (X + Y)` is within
statistical distance `δ` of the uniform distribution on `β`.

Specializing to flat sources connects distributional sumset extractors to the combinatorial
`SumsetBias` and `RectangleBias` predicates from `Cslib.Circuits.Frontier`:

* every Boolean `(k, δ)`-sumset extractor has `SumsetBias {z | E z = true} ⌈2^k⌉₊ δ` and
  `RectangleBias {z | E z = true} ⌈2^k⌉₊ δ` (`IsSumsetExtractor.sumsetBias_ceil`,
  `IsSumsetExtractor.rectangleBias_ceil`);
* for natural-number min-entropy `k : ℕ`, `IsSumsetExtractor E k δ` is equivalent to
  `SumsetBias {z | E z = true} (2 ^ k) δ` (`isSumsetExtractor_iff_sumsetBias_two_pow`) via the
  flat-source decomposition `Cslib.Probability.PMF.exists_eq_bind_uniformOfFinset_of_le_minEntropy`;
* when `k_n = o(n)` and `δ_n ≤ δ₀ < 1 / 2`, the threshold `⌈2^(k_n)⌉₊` has sublinear logarithm
  (`isLittleO_log_ceil_two_rpow`) and the logarithmic density deficit of `{z | E_n z = true}` is
  `o(n)` (`isLittleO_sub_log_ncard_of_sumsetBias`).

## Main definitions

* `Cslib.Circuits.Frontier.IsSumsetExtractor`: `E (X + Y)` is `δ`-close to uniform for independent
  `k`-sources `X, Y`.

## Main results

* `Cslib.Circuits.Frontier.IsSumsetExtractor.sumsetBias_ceil`,
  `Cslib.Circuits.Frontier.IsSumsetExtractor.rectangleBias_ceil`: extractor-to-frontier bridge at
  threshold `⌈2^k⌉₊`.
* `Cslib.Circuits.Frontier.isSumsetExtractor_iff_sumsetBias_two_pow`: Chor–Goldreich flat-source
  equivalence for Boolean sumset extractors.
* `Cslib.Circuits.Frontier.isLittleO_log_ceil_two_rpow`,
  `Cslib.Circuits.Frontier.isLittleO_sub_log_ncard_of_sumsetBias`: asymptotic threshold and density
  lemmas for sumset-extractor families.
* `Cslib.Circuits.Frontier.IsSumsetExtractor.isAffineDisperser`: every `(k, δ)`-sumset extractor
  with `δ < 1 / 2` and `k ≤ d` is an affine disperser for dimension `d`.

## References

* [B. Chor and O. Goldreich, *Unbiased bits from sources of weak randomness and probabilistic
  communication complexity*][ChorGoldreich1988]
* [E. Chattopadhyay and J.-J. Liao, *Extractors for Sum of Two Sources*][ChattopadhyayLiao2022]
* [S. Schlesinger, *Frontier circuit lower bounds and two-source sumset extractors in
  Complexitylib*][Schlesinger2026FrontierExtractor]
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Filter Asymptotics Real Cslib.Probability.PMF

universe u

variable {ι : Type*} {U : Type u} {G β γ : Type*}

/-! ### Distributional two-source sumset extractors -/

/-- `E : G → β` is a `(k, δ)`-sumset extractor if for every pair of independent `k`-sources
`X, Y : PMF G`, the distribution of `E (X + Y)` is within statistical distance `δ` of the uniform
distribution on `β` [Chattopadhyay and Liao][ChattopadhyayLiao2022]. -/
def IsSumsetExtractor [Add G] [Fintype β] [Nonempty β] (E : G → β) (k : ℝ) (δ : ℝ) : Prop :=
  ∀ X Y : PMF G, k ≤ minEntropy X → k ≤ minEntropy Y →
    dist ((X.bind fun x => Y.map fun y => x + y).map E) (uniformOfFintype β) ≤ δ

theorem IsSumsetExtractor.mono [Add G] [Fintype β] [Nonempty β] {E : G → β} {k k' δ δ' : ℝ}
    (h : IsSumsetExtractor E k δ) (hk : k ≤ k') (hδ : δ ≤ δ') :
    IsSumsetExtractor E k' δ' :=
  fun X Y hX hY => (h X Y (hk.trans hX) (hk.trans hY)).trans hδ

/-- Post-composing a sumset extractor with any map that pushes the uniform distribution to the
uniform distribution preserves `(k, δ)`-sumset extraction. -/
theorem IsSumsetExtractor.comp_of_map_uniform [Add G] [Fintype β] [Nonempty β] [Fintype γ]
    [Nonempty γ] {E : G → β} {k δ : ℝ} (h : IsSumsetExtractor E k δ) {g : β → γ}
    (hg : (uniformOfFintype β).map g = uniformOfFintype γ) :
    IsSumsetExtractor (g ∘ E) k δ := by
  intro X Y hX hY
  rw [← PMF.map_comp, ← hg]
  exact (dist_map_le _ _ g).trans (h X Y hX hY)

/-- Summing a non-empty subset of output coordinates of a tuple-valued sumset extractor yields a
single-coordinate sumset extractor with the same parameters. -/
theorem IsSumsetExtractor.sum_apply {κ H : Type*} [Add G] [Fintype κ] [DecidableEq κ]
    [AddCommGroup H] [Fintype H] {E : G → κ → H} {k δ : ℝ} (h : IsSumsetExtractor E k δ)
    (s : Finset κ) (hs : s.Nonempty) :
    IsSumsetExtractor (fun z => ∑ i ∈ s, E z i) k δ :=
  h.comp_of_map_uniform (g := fun f => ∑ i ∈ s, f i) (uniformOfFintype_map_sum s hs)

/-- Projecting a tuple-valued sumset extractor onto a single output coordinate yields a sumset
extractor with the same parameters. -/
theorem IsSumsetExtractor.apply {κ H : Type*} [Add G] [Fintype κ] [DecidableEq κ]
    [AddCommGroup H] [Fintype H] {E : G → κ → H} {k δ : ℝ} (h : IsSumsetExtractor E k δ)
    (i : κ) :
    IsSumsetExtractor (fun z => E z i) k δ := by
  simpa only [Finset.sum_singleton] using h.sum_apply {i} (Finset.singleton_nonempty i)

/-- The probability that `E (X + Y) = true` under two flat sources `uniformOfFinset A` and
`uniformOfFinset B` is the fraction of pairs `(a, b) ∈ A ×ˢ B` with `E (a + b) = true`. -/
theorem uniformOfFinset_bind_map_add_apply_true [Finite G] [Add G]
    (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty) (E : G → Bool) :
    ((((uniformOfFinset A hA).bind fun x =>
      (uniformOfFinset B hB).map fun y => x + y).map E) true).toReal =
      (((A ×ˢ B).filter fun p => E (p.1 + p.2) = true).card : ℝ) /
        ((A.card : ℝ) * (B.card : ℝ)) := by
  classical
  cases nonempty_fintype G
  have inner_eq (x : G) :
      (((uniformOfFinset B hB).map fun y => E (x + y)) true).toReal =
        ((B.filter fun y => E (x + y) = true).card : ℝ) / (B.card : ℝ) := by
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum fun y _ => by
      split_ifs
      · exact PMF.apply_ne_top _ _
      · exact ENNReal.zero_ne_top]
    trans ∑ y, if y ∈ B ∧ E (x + y) = true then (B.card : ℝ)⁻¹ else 0
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [uniformOfFinset_apply]
      cases E (x + y) <;> by_cases hy : y ∈ B <;> simp [hy]
    · rw [← Finset.sum_filter, ← Finset.filter_filter, Finset.filter_mem_eq_inter,
        Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  rw [PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  rw [PMF.bind_apply, tsum_fintype,
    ENNReal.toReal_sum fun x _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  simp only [ENNReal.toReal_mul, inner_eq]
  trans ∑ x, if x ∈ A then
      ((B.filter fun y => E (x + y) = true).card : ℝ) / ((A.card : ℝ) * (B.card : ℝ))
    else 0
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [uniformOfFinset_apply]
    by_cases hx : x ∈ A
    · simp only [hx, ite_true, ENNReal.toReal_inv, ENNReal.toReal_natCast]
      ring
    · simp [hx]
  · rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sum_div,
      ← Nat.cast_sum]
    congr 1
    norm_cast
    simp only [Finset.card_filter, Finset.sum_product]

/-- Statistical distance from uniform on `Bool` for the sum of two flat sources
`A, B : Finset G`. -/
theorem dist_uniformOfFinset_bind_map_add_bool [Finite G] [Add G]
    (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty) (E : G → Bool) :
    dist (((uniformOfFinset A hA).bind fun x =>
        (uniformOfFinset B hB).map fun y => x + y).map E)
      (uniformOfFintype Bool) =
      |(((A ×ˢ B).filter fun p => E (p.1 + p.2) = true).card : ℝ) -
          (A.card : ℝ) * (B.card : ℝ) / 2| /
        ((A.card : ℝ) * (B.card : ℝ)) := by
  have hAB : (0 : ℝ) < (A.card : ℝ) * (B.card : ℝ) := by
    have : 0 < A.card := hA.card_pos
    have : 0 < B.card := hB.card_pos
    positivity
  rw [dist_uniformOfFintype_bool, uniformOfFinset_bind_map_add_apply_true,
    show (((A ×ˢ B).filter fun p => E (p.1 + p.2) = true).card : ℝ) /
        ((A.card : ℝ) * (B.card : ℝ)) - 1 / 2 =
      ((((A ×ˢ B).filter fun p => E (p.1 + p.2) = true).card : ℝ) -
        (A.card : ℝ) * (B.card : ℝ) / 2) / ((A.card : ℝ) * (B.card : ℝ)) by
      field_simp,
    abs_div, abs_of_pos hAB]

/-- Any Boolean `(k, δ)`-sumset extractor on a finite additive type `G` has `SumsetBias` at most
`δ` at every threshold `K` satisfying `2 ^ k ≤ K`. -/
theorem IsSumsetExtractor.sumsetBias_of_rpow_le [Finite G] [Add G] {E : G → Bool} {k δ : ℝ}
    (h : IsSumsetExtractor E k δ) {K : ℕ} (hK : (2 : ℝ) ^ k ≤ K) :
    SumsetBias {z | E z = true} K δ := by
  classical
  let := Fintype.ofFinite G
  intro A B hA hB
  have hKpos : 0 < K := by
    have : (0 : ℝ) < K := lt_of_lt_of_le (by positivity) hK
    exact_mod_cast this
  have hAcard : A.toFinset.card = A.ncard := (Set.ncard_eq_toFinset_card' A).symm
  have hBcard : B.toFinset.card = B.ncard := (Set.ncard_eq_toFinset_card' B).symm
  have hAne : A.toFinset.Nonempty :=
    Finset.card_pos.mp (hAcard.symm ▸ lt_of_lt_of_le hKpos hA)
  have hBne : B.toFinset.Nonempty :=
    Finset.card_pos.mp (hBcard.symm ▸ lt_of_lt_of_le hKpos hB)
  have hminA : k ≤ minEntropy (uniformOfFinset A.toFinset hAne) := by
    rw [minEntropy_uniformOfFinset, hAcard,
      Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast lt_of_lt_of_le hKpos hA)]
    exact hK.trans (by exact_mod_cast hA)
  have hminB : k ≤ minEntropy (uniformOfFinset B.toFinset hBne) := by
    rw [minEntropy_uniformOfFinset, hBcard,
      Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast lt_of_lt_of_le hKpos hB)]
    exact hK.trans (by exact_mod_cast hB)
  have hdist := h _ _ hminA hminB
  rw [dist_uniformOfFinset_bind_map_add_bool] at hdist
  have hAB : (0 : ℝ) < (A.toFinset.card : ℝ) * (B.toFinset.card : ℝ) := by
    have : 0 < A.toFinset.card := hAne.card_pos
    have : 0 < B.toFinset.card := hBne.card_pos
    positivity
  have hle := (div_le_iff₀ hAB).mp hdist
  have hfilter :
      ((A.toFinset ×ˢ B.toFinset).filter fun p => E (p.1 + p.2) = true).card =
        {p ∈ A ×ˢ B | p.1 + p.2 ∈ {z | E z = true}}.ncard := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext ⟨a, b⟩
    simp
  rwa [hfilter, hAcard, hBcard] at hle

/-- A Boolean `(k, δ)`-sumset extractor has `SumsetBias` at most `δ` at threshold `⌈2^k⌉₊`. -/
theorem IsSumsetExtractor.sumsetBias_ceil [Finite G] [Add G] {E : G → Bool} {k δ : ℝ}
    (h : IsSumsetExtractor E k δ) :
    SumsetBias {z | E z = true} ⌈(2 : ℝ) ^ k⌉₊ δ :=
  h.sumsetBias_of_rpow_le (Nat.le_ceil _)

/-- **Extractor-to-frontier bridge.** Any Boolean `(k, δ)`-sumset extractor on `ι → U` induces
`RectangleBias` at threshold `⌈2^k⌉₊` with bias at most `δ`. -/
theorem IsSumsetExtractor.rectangleBias_ceil [AddZeroClass U] [Finite ι] [Finite U]
    {E : (ι → U) → Bool} {k δ : ℝ} (h : IsSumsetExtractor E k δ) :
    RectangleBias {z | E z = true} ⌈(2 : ℝ) ^ k⌉₊ δ :=
  h.sumsetBias_ceil.rectangleBias

/-- Projecting a multi-bit `(k, δ)`-sumset extractor onto coordinate `i` yields a Boolean function
with `RectangleBias` at most `δ` at threshold `⌈2^k⌉₊`. -/
theorem IsSumsetExtractor.rectangleBias_apply_ceil {κ : Type*} [AddZeroClass U] [Finite ι]
    [Finite U] [Fintype κ] [DecidableEq κ] {E : (ι → U) → κ → Bool} {k δ : ℝ}
    (h : IsSumsetExtractor E k δ) (i : κ) :
    RectangleBias {z | E z i = true} ⌈(2 : ℝ) ^ k⌉₊ δ :=
  (h.apply i).rectangleBias_ceil

/-- **Flat-source characterization of Boolean sumset extractors.** For a natural number `k`,
`E : G → Bool` is a `(k, δ)`-sumset extractor if and only if `{z | E z = true}` has `SumsetBias`
at most `δ` at threshold `2 ^ k` [Chor and Goldreich][ChorGoldreich1988]. -/
theorem isSumsetExtractor_iff_sumsetBias_two_pow [Finite G] [Add G] (E : G → Bool) (k : ℕ)
    (δ : ℝ) :
    IsSumsetExtractor E (k : ℝ) δ ↔ SumsetBias {z | E z = true} (2 ^ k) δ := by
  classical
  let := Fintype.ofFinite G
  refine ⟨fun h => h.sumsetBias_of_rpow_le (by norm_cast), fun h X Y hX hY => ?_⟩
  obtain ⟨mixX, rfl⟩ := exists_eq_bind_uniformOfFinset_of_le_minEntropy X hX
  obtain ⟨mixY, rfl⟩ := exists_eq_bind_uniformOfFinset_of_le_minEntropy Y hY
  let flatX (A : {S : Finset G // S.card = 2 ^ k}) : PMF G :=
    uniformOfFinset A.1 (Finset.card_ne_zero.mp (A.2.trans_ne (pow_ne_zero k two_ne_zero)))
  let flatY (B : {S : Finset G // S.card = 2 ^ k}) : PMF G :=
    uniformOfFinset B.1 (Finset.card_ne_zero.mp (B.2.trans_ne (pow_ne_zero k two_ne_zero)))
  change dist (((mixX.bind flatX).bind fun x => (mixY.bind flatY).map fun y => x + y).map E)
    (uniformOfFintype Bool) ≤ δ
  have hbind :
      ((mixX.bind flatX).bind fun x => (mixY.bind flatY).map fun y => x + y).map E =
        mixX.bind fun A => mixY.bind fun B =>
          ((flatX A).bind fun x => (flatY B).map fun y => x + y).map E := by
    simp only [PMF.bind_bind, PMF.map_bind]
    refine congrArg (mixX.bind ·) (funext fun A => ?_)
    rw [PMF.bind_comm]
  rw [hbind]
  refine dist_bind_left_le_of_le mixX _ _ fun A _ => ?_
  refine dist_bind_left_le_of_le mixY _ _ fun B _ => ?_
  rw [dist_uniformOfFinset_bind_map_add_bool]
  have hAcard : (A.1 : Set G).ncard = 2 ^ k := by
    rw [Set.ncard_coe_finset, A.2]
  have hBcard : (B.1 : Set G).ncard = 2 ^ k := by
    rw [Set.ncard_coe_finset, B.2]
  have hAB : (0 : ℝ) < (A.1.card : ℝ) * (B.1.card : ℝ) := by
    rw [A.2, B.2]
    positivity
  rw [div_le_iff₀ hAB]
  have hbias := h (A.1 : Set G) (B.1 : Set G) hAcard.ge hBcard.ge
  have hfilter :
      ((A.1 ×ˢ B.1).filter fun p => E (p.1 + p.2) = true).card =
        {p ∈ (A.1 : Set G) ×ˢ (B.1 : Set G) | p.1 + p.2 ∈ {z | E z = true}}.ncard := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext ⟨a, b⟩
    simp
  rw [Set.ncard_coe_finset, Set.ncard_coe_finset] at hbias
  rwa [hfilter]

/-! ### Asymptotic threshold and density lemmas -/

/-- If `k_n = o(n)`, then `log ⌈2^(k_n)⌉₊ = o(n)`. -/
theorem isLittleO_log_ceil_two_rpow {k : ℕ → ℝ}
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ)) :
    (fun n => Real.log (⌈(2 : ℝ) ^ k n⌉₊ : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ) := by
  have hbound (n : ℕ) :
      ‖Real.log (⌈(2 : ℝ) ^ k n⌉₊ : ℝ)‖ ≤ Real.log 2 * (‖k n‖ + 1) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases hkn : k n ≤ 0
    · have hle : (2 : ℝ) ^ k n ≤ 1 := by
        calc (2 : ℝ) ^ k n ≤ (2 : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two hkn
          _ = 1 := Real.rpow_zero 2
      have hceil : ⌈(2 : ℝ) ^ k n⌉₊ = 1 :=
        le_antisymm (Nat.ceil_le.mpr (by exact_mod_cast hle))
          (Nat.succ_le_of_lt (Nat.ceil_pos.mpr (by positivity)))
      rw [hceil, Nat.cast_one, Real.log_one, abs_zero]
      positivity
    · have hkn_pos : 0 < k n := not_le.mp hkn
      have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ k n := by
        calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 2).symm
          _ ≤ (2 : ℝ) ^ k n := Real.rpow_le_rpow_of_exponent_le one_le_two hkn_pos.le
      have hceil_ge : (1 : ℝ) ≤ (⌈(2 : ℝ) ^ k n⌉₊ : ℝ) := hge1.trans (Nat.le_ceil _)
      have hceil_le : (⌈(2 : ℝ) ^ k n⌉₊ : ℝ) ≤ (2 : ℝ) ^ (k n + 1) := by
        calc (⌈(2 : ℝ) ^ k n⌉₊ : ℝ) ≤ (2 : ℝ) ^ k n + 1 := (Nat.ceil_lt_add_one (by positivity)).le
          _ ≤ (2 : ℝ) ^ k n + (2 : ℝ) ^ k n := by linarith
          _ = (2 : ℝ) ^ (k n + 1) := by rw [Real.rpow_add_one two_ne_zero]; ring
      rw [abs_of_nonneg (Real.log_nonneg hceil_ge), abs_of_pos hkn_pos]
      calc Real.log (⌈(2 : ℝ) ^ k n⌉₊ : ℝ)
          ≤ Real.log ((2 : ℝ) ^ (k n + 1)) :=
            Real.log_le_log (by positivity) hceil_le
        _ = (k n + 1) * Real.log 2 := Real.log_rpow two_pos (k n + 1)
        _ = Real.log 2 * (k n + 1) := mul_comm _ _
  have h1 : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ) :=
    (isLittleO_const_id_atTop (1 : ℝ)).natCast_atTop
  have hsum : (fun n => Real.log 2 * (‖k n‖ + 1)) =o[atTop] fun n : ℕ => (n : ℝ) :=
    (hk.norm_left.add h1).const_mul_left (Real.log 2)
  exact (IsBigO.of_bound 1 (Filter.Eventually.of_forall fun n => by
    rw [one_mul]
    exact (hbound n).trans (le_abs_self _))).trans_isLittleO hsum

/-- A family of sets with `SumsetBias (S n) (K n) (b n)`, `log (K n) = o(n)`, and
`b n ≤ b₀ < 1 / 2` eventually has logarithmic density deficit
`n * log |U| - log |(S n)| = o(n)`. -/
theorem isLittleO_sub_log_ncard_of_sumsetBias [AddGroup U] [Finite U] [Nontrivial U]
    {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ} {b : ℕ → ℝ} {b₀ : ℝ}
    (hbias : ∀ᶠ n in atTop, SumsetBias (S n) (K n) (b n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hb : ∀ᶠ n in atTop, b n ≤ b₀) (hb₀ : b₀ < 1 / 2) :
    (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop] fun n => (n : ℝ) := by
  have hUpos : (0 : ℝ) < Nat.card U := by exact_mod_cast Nat.card_pos
  have hlogU : 0 < Real.log (Nat.card U) :=
    Real.log_pos (by exact_mod_cast Finite.one_lt_card)
  have h12b : 0 < 1 / 2 - b₀ := by linarith
  have hKle : ∀ᶠ n in atTop, K n ≤ Nat.card (Fin n → U) := by
    filter_upwards [hK.bound hlogU] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Nat.abs_cast] at hn
    by_cases hKn : K n = 0
    · simp [hKn]
    · have hKn_pos : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero hKn
      have hlog_le : Real.log (K n) ≤ Real.log ((Nat.card U : ℝ) ^ n) := by
        rw [Real.log_pow]
        linarith [le_abs_self (Real.log (K n))]
      have hpow_le : (K n : ℝ) ≤ (Nat.card U : ℝ) ^ n :=
        (Real.log_le_log_iff hKn_pos (by positivity)).mp hlog_le
      have hcard : Nat.card (Fin n → U) = Nat.card U ^ n := by
        simp [Nat.card_pi]
      rw [hcard]
      exact_mod_cast hpow_le
  have hbound : ∀ᶠ n in atTop,
      ‖n * Real.log (Nat.card U) - Real.log (S n).ncard‖ ≤ ‖-Real.log (1 / 2 - b₀)‖ := by
    filter_upwards [hbias, hKle, hb] with n hbiasn hKlen hbn
    have hcard : (Nat.card (Fin n → U) : ℝ) = (Nat.card U : ℝ) ^ n := by
      simp [Nat.card_pi]
    have hge : (1 / 2 - b₀) * (Nat.card U : ℝ) ^ n ≤ (S n).ncard := by
      calc (1 / 2 - b₀) * (Nat.card U : ℝ) ^ n
          ≤ (1 / 2 - b n) * (Nat.card (Fin n → U) : ℝ) := by
            rw [hcard]
            exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ ≤ (S n).ncard := hbiasn.ncard_ge hKlen
    have hle : (S n).ncard ≤ Nat.card U ^ n := by
      simpa [Nat.card_pi] using Set.ncard_le_ncard (Set.subset_univ (S n))
    have hSpos : (0 : ℝ) < (S n).ncard := lt_of_lt_of_le (by positivity) hge
    have hdiff_nonneg : 0 ≤ n * Real.log (Nat.card U) - Real.log (S n).ncard := by
      rw [sub_nonneg, ← Real.log_pow]
      exact Real.log_le_log hSpos (by exact_mod_cast hle)
    have hdiff_le : n * Real.log (Nat.card U) - Real.log (S n).ncard ≤ -Real.log (1 / 2 - b₀) := by
      have hlog := Real.log_le_log (by positivity) hge
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg hdiff_nonneg, Real.norm_eq_abs]
    exact hdiff_le.trans (le_abs_self _)
  have hconst : (fun _ : ℕ => -Real.log (1 / 2 - b₀)) =o[atTop] fun n : ℕ => (n : ℝ) :=
    (isLittleO_const_id_atTop (-Real.log (1 / 2 - b₀))).natCast_atTop
  exact (IsBigO.of_bound 1 (by
    filter_upwards [hbound] with n hn
    rwa [one_mul])).trans_isLittleO hconst

/-! ### Sumset extractors are affine dispersers -/

section AffineDisperser

open Cslib.BitString

/-- **Every `(k, δ)`-sumset extractor with `δ < 1 / 2` and `k ≤ d` is an affine disperser for
dimension `d`.** -/
theorem IsSumsetExtractor.isAffineDisperser {n d : ℕ} {f : BitString n → Bool} {k δ : ℝ}
    (h : IsSumsetExtractor f k δ) (hδ : δ < 1 / 2) (hk : k ≤ d) :
    IsAffineDisperser f d := by
  refine h.sumsetBias_ceil.isAffineDisperser (Nat.ceil_pos.mpr (by positivity)) hδ ?_
  rw [Nat.ceil_le, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le one_le_two hk

end AffineDisperser

end Cslib.Circuits.Frontier
