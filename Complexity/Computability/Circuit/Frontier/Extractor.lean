/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.BoundedFanIn
public import Complexity.Computability.Circuit.Frontier.FanInTwo
public import Complexity.Computability.Circuit.Frontier.Ledger.Unconditional
public import Complexity.Computability.Circuit.Frontier.Nondeterministic
public import Complexity.Computability.Circuit.Frontier.Unconditional
public import Complexity.Foundations.Data.BitString.AffineDisperser
public import Complexity.Foundations.Data.BitString.Basic
public import Complexity.Probability.MinEntropy
public import Complexity.Probability.Uniform

import Complexity.Probability.MinEntropy.Flat
import Complexity.Probability.StatisticalDistance
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Sumset extractors, sumset dispersers, and frontier circuit lower bounds

Let `U` be an additive monoid with zero and `ι` be a coordinate set. Given a subset `X : Set ι` and
partial assignments `a : X → U` and `b : ↥Xᶜ → U`, padding `a` with `0` outside `X` and `b` with `0`
outside `Xᶜ` embeds `A ⊆ X → U` and `B ⊆ ↥Xᶜ → U` injectively into `ι → U` (`zeroPad_injective`),
with restrictions

`X.domRestrict (zeroPad X a + zeroPad Xᶜ b) = a` (`domRestrict_zeroPad_add_zeroPad_compl_self`) and
`Xᶜ.domRestrict (zeroPad X a + zeroPad Xᶜ b) = b` (`domRestrict_zeroPad_add_zeroPad_compl_compl`).

Consequently, every combinatorial rectangle `rectangle X A B` in `ι → U` is the sumset of two sets
of the same cardinalities `|A|` and `|B|` (`image2_add_image_zeroPad_eq_rectangle`), and the number
of pairs in `(zeroPad X '' A) ×ˢ (zeroPad Xᶜ '' B)` whose sum lies in `S ⊆ ι → U` is
`(rectangle X A B ∩ S).ncard` (`ncard_sep_add_mem_image_zeroPad`). This connects two-source sumset
pseudorandomness directly to the rectangle hypotheses of the frontier method:

* a sumset disperser (`SumsetDisperser S K`) is `K`-rectangle-free together with its complement
  (`SumsetDisperser.rectangleFree`, `SumsetDisperser.rectangleFree_compl`);
* a set with sumset bias at most `b` above threshold `K` (`SumsetBias S K b`) has rectangle bias at
  most `b` above threshold `K` (`SumsetBias.rectangleBias`), and when `b < 1 / 2` its global density
  is within `b` of `1 / 2` (`SumsetBias.abs_ncard_sub_half_le`);
* a distributional `(k, δ)`-sumset extractor (`IsSumsetExtractor E k δ`, in the sense of
  [Chattopadhyay and Liao][ChattopadhyayLiao2022]) induces `SumsetBias {z | E z = true} ⌈2^k⌉₊ δ`
  and `RectangleBias {z | E z = true} ⌈2^k⌉₊ δ` (`IsSumsetExtractor.sumsetBias_ceil`,
  `IsSumsetExtractor.rectangleBias_ceil`), and for natural-number min-entropy `k : ℕ` is equivalent
  to `SumsetBias {z | E z = true} (2 ^ k) δ` (`isSumsetExtractor_iff_sumsetBias_two_pow`) via the
  flat-source decomposition `Cslib.Probability.PMF.exists_eq_bind_uniformOfFinset_of_le_minEntropy`.

Combined with `Cslib.Circuits.Frontier.averageCaseBound_gaussian` and
`Cslib.Circuits.Frontier.eventually_gaussian_sub_mul_lt_innerSize`, any family of Boolean sumset
extractors `E_n : (Fin n → Bool) → Bool` (or multi-bit extractors composed with a coordinate
projection or parity) with sublinear min-entropy `k_n = o(n)` satisfies the Gaussian frontier
average-case bound `(4.56249 - ε) n` (`eventually_agreement_le_of_isSumsetExtractor`,
`eventually_agreement_le_of_isSumsetExtractor_fullSignature`), and when the error is bounded away
from `1 / 2` also satisfies the worst-case gate-count lower bounds for fan-in two (`4.56249 n`) and
general fan-in `r` (`(r - 1) s > (2 - ε) n`).

## Main definitions

* `Cslib.Circuits.Frontier.zeroPad`: extend `a : X → U` by `0` outside `X`.
* `Cslib.Circuits.Frontier.SumsetDisperser`: neither `S` nor `Sᶜ` contains `A + B` for
  `|A|, |B| ≥ K`.
* `Cslib.Circuits.Frontier.SumsetBias`: `a + b ∈ S` has bias at most `b` on `A ×ˢ B` for
  `|A|, |B| ≥ K`.
* `Cslib.Circuits.Frontier.IsSumsetExtractor`: `E (X + Y)` is `δ`-close to uniform for independent
  `k`-sources `X, Y`.
* `Cslib.Circuits.Frontier.balancePad`, `balancePadFamily`: one-bit balanced padding of a Boolean
  function or family by XORing with the first coordinate.

## Main results

* `Cslib.Circuits.Frontier.SumsetDisperser.rectangleFree`: a sumset disperser is rectangle-free.
* `Cslib.Circuits.Frontier.SumsetBias.rectangleBias`: sumset bias bounds rectangle bias.
* `Cslib.Circuits.Frontier.IsSumsetExtractor.rectangleBias_ceil`: a `(k, δ)`-sumset extractor has
  rectangle bias at most `δ` at threshold `⌈2^k⌉₊`.
* `Cslib.Circuits.Frontier.isSumsetExtractor_iff_sumsetBias_two_pow`: flat-source equivalence for
  Boolean sumset extractors.
* `Cslib.Circuits.Frontier.SumsetDisperser.isAffineDisperser`,
  `IsSumsetExtractor.isAffineDisperser`: every sumset disperser at threshold `K ≤ 2 ^ d` (and every
  `(k, δ)`-sumset extractor with `δ < 1 / 2` and `k ≤ d`) is an affine disperser for dimension `d`.
* `Cslib.Circuits.Frontier.SumsetDisperser.balancePad`,
  `frontierHypotheses_balancePadFamily`: balanced padding accepts `2 ^ n` inputs, preserves sumset
  dispersion at threshold `2 * K`, and satisfies all worst-case frontier hypotheses without a
  quantitative bias assumption.
* `Cslib.Circuits.Frontier.eventually_agreement_le_of_isSumsetExtractor`: conditional Gaussian
  frontier average-case lower bound from a sumset extractor family.
* `Cslib.Circuits.Frontier.eventually_456249_div_100000_sub_mul_lt_size_of_isSumsetExtractor`,
  `eventually_degreeCoefficient_lt_mul_innerSize_of_isSumsetExtractor`,
  `eventually_456249_div_100000_sub_mul_lt_innerSize_nondeterministic_of_isSumsetExtractor`,
  `eventually_456249_div_100000_sub_mul_lt_card_of_aggregates_of_isSumsetExtractor`:
  conditional `(4.56249 - ε) n` worst-case circuit lower bounds over `fullSignature 2 Bool`, for
  bounded fan-in `r ≥ 2`, for nondeterministic verifier circuits, and for circuits with `o(n)`
  monoid-aggregate gates of unbounded fan-in.

## References

* [B. Chor and O. Goldreich, *Unbiased bits from sources of weak randomness and probabilistic
  communication complexity*][ChorGoldreich1988]
* [E. Chattopadhyay and J.-J. Liao, *Extractors for Sum of Two Sources*][ChattopadhyayLiao2022]
* [E. Chattopadhyay and D. Zuckerman, *Explicit Two-Source Extractors and Resilient
  Functions*][ChattopadhyayZuckerman2019]
* [X. Li, *Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More*][Li2023]
* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
* [S. Schlesinger, *Frontier circuit lower bounds and two-source sumset extractors in
  Complexitylib*][Schlesinger2026FrontierExtractor]
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Filter Asymptotics Real Cslib.Probability.PMF

universe u v

variable {ι : Type*} {U : Type u}

/-! ### Zero-extension of partial assignments -/

open Classical in
/-- Extend a partial assignment `a : X → U` to `ι → U` by padding with `0` outside `X`. -/
noncomputable def zeroPad [Zero U] (X : Set ι) (a : X → U) (i : ι) : U :=
  if h : i ∈ X then a ⟨i, h⟩ else 0

@[simp]
theorem zeroPad_apply_of_mem [Zero U] {X : Set ι} (a : X → U) {i : ι} (hi : i ∈ X) :
    zeroPad X a i = a ⟨i, hi⟩ := by
  classical exact dite_eq_left hi

@[simp]
theorem zeroPad_apply_of_notMem [Zero U] {X : Set ι} (a : X → U) {i : ι} (hi : i ∉ X) :
    zeroPad X a i = 0 := by
  classical exact dite_eq_right hi

/-- Restricting `zeroPad X a` back to `X` recovers `a`. -/
@[simp]
theorem domRestrict_zeroPad [Zero U] (X : Set ι) (a : X → U) :
    X.domRestrict (zeroPad X a) = a := by
  ext ⟨i, hi⟩
  simp [Set.domRestrict, hi]

/-- Zero-padding outside `X` is injective. -/
theorem zeroPad_injective [Zero U] (X : Set ι) :
    Function.Injective (zeroPad (U := U) X) :=
  Function.LeftInverse.injective (domRestrict_zeroPad (U := U) X)

@[simp]
theorem ncard_image_zeroPad [Zero U] (X : Set ι) (A : Set (X → U)) :
    (zeroPad X '' A).ncard = A.ncard :=
  Set.ncard_image_of_injective A (zeroPad_injective X)

/-- Restricting `zeroPad X a + zeroPad Xᶜ b` to `X` yields `a`. -/
@[simp]
theorem domRestrict_zeroPad_add_zeroPad_compl_self [AddZeroClass U] (X : Set ι) (a : X → U)
    (b : ↥Xᶜ → U) :
    X.domRestrict (zeroPad X a + zeroPad Xᶜ b) = a := by
  ext ⟨i, hi⟩
  have hic : i ∉ (Xᶜ : Set ι) := fun h => h hi
  simp [Set.domRestrict, Pi.add_apply, hi, hic]

/-- Restricting `zeroPad X a + zeroPad Xᶜ b` to `Xᶜ` yields `b`. -/
@[simp]
theorem domRestrict_zeroPad_add_zeroPad_compl_compl [AddZeroClass U] (X : Set ι) (a : X → U)
    (b : ↥Xᶜ → U) :
    Xᶜ.domRestrict (zeroPad X a + zeroPad Xᶜ b) = b := by
  ext ⟨i, hic⟩
  have hi : i ∉ X := hic
  simp [Set.domRestrict, Pi.add_apply, hi, hic]

/-- Every assignment `z : ι → U` decomposes as the sum of its restrictions to `X` and `Xᶜ`
zero-padded outside their domains. -/
theorem zeroPad_domRestrict_add_zeroPad_compl_domRestrict [AddZeroClass U] (X : Set ι)
    (z : ι → U) :
    zeroPad X (X.domRestrict z) + zeroPad Xᶜ (Xᶜ.domRestrict z) = z := by
  ext i
  by_cases hi : i ∈ X
  · have hic : i ∉ (Xᶜ : Set ι) := fun h => h hi
    simp [Set.domRestrict, Pi.add_apply, hi, hic]
  · have hic : i ∈ (Xᶜ : Set ι) := hi
    simp [Set.domRestrict, Pi.add_apply, hi, hic]

/-- The sumset of `zeroPad X '' A` and `zeroPad Xᶜ '' B` is the combinatorial rectangle
`rectangle X A B`. -/
theorem image2_add_image_zeroPad_eq_rectangle [AddZeroClass U] (X : Set ι) (A : Set (X → U))
    (B : Set (↥Xᶜ → U)) :
    Set.image2 (· + ·) (zeroPad X '' A) (zeroPad Xᶜ '' B) = rectangle X A B := by
  ext z
  simp only [Set.mem_image2, Set.mem_image, exists_exists_and_eq_and, mem_rectangle]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    simp [ha, hb]
  · rintro ⟨ha, hb⟩
    exact ⟨X.domRestrict z, ha, Xᶜ.domRestrict z, hb,
      zeroPad_domRestrict_add_zeroPad_compl_domRestrict X z⟩

/-- The pairs in `(zeroPad X '' A) ×ˢ (zeroPad Xᶜ '' B)` whose sum lies in `S` are in bijection
with `rectangle X A B ∩ S`. -/
theorem ncard_sep_add_mem_image_zeroPad [AddZeroClass U] (X : Set ι) (A : Set (X → U))
    (B : Set (↥Xᶜ → U)) (S : Set (ι → U)) :
    {p ∈ (zeroPad X '' A) ×ˢ (zeroPad Xᶜ '' B) | p.1 + p.2 ∈ S}.ncard =
      (rectangle X A B ∩ S).ncard := by
  symm
  refine Set.ncard_congr
    (fun z _ => (zeroPad X (X.domRestrict z), zeroPad Xᶜ (Xᶜ.domRestrict z))) ?_ ?_ ?_
  · rintro z ⟨hzR, hzS⟩
    rw [mem_rectangle] at hzR
    exact ⟨⟨⟨X.domRestrict z, hzR.1, rfl⟩, ⟨Xᶜ.domRestrict z, hzR.2, rfl⟩⟩,
      by rwa [zeroPad_domRestrict_add_zeroPad_compl_domRestrict]⟩
  · intro z₁ z₂ _ _ h
    have hsum := congrArg (fun p : (ι → U) × (ι → U) => p.1 + p.2) h
    simpa only [zeroPad_domRestrict_add_zeroPad_compl_domRestrict] using hsum
  · rintro ⟨x, y⟩ ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, hxy⟩
    refine ⟨zeroPad X a + zeroPad Xᶜ b, ⟨?_, hxy⟩, ?_⟩
    · rw [mem_rectangle, domRestrict_zeroPad_add_zeroPad_compl_self,
        domRestrict_zeroPad_add_zeroPad_compl_compl]
      exact ⟨ha, hb⟩
    · simp only [domRestrict_zeroPad_add_zeroPad_compl_self,
        domRestrict_zeroPad_add_zeroPad_compl_compl]

/-! ### Sumset dispersers and sumset bias -/

variable {G : Type*}

/-- `S` is a sumset disperser at threshold `K` if neither `S` nor `Sᶜ` contains the sumset of two
sets of cardinality at least `K`. -/
def SumsetDisperser [Add G] (S : Set G) (K : ℕ) : Prop :=
  ∀ A B : Set G, K ≤ A.ncard → K ≤ B.ncard →
    (∃ a ∈ A, ∃ b ∈ B, a + b ∈ S) ∧ (∃ a ∈ A, ∃ b ∈ B, a + b ∉ S)

theorem SumsetDisperser.compl [Add G] {S : Set G} {K : ℕ} (h : SumsetDisperser S K) :
    SumsetDisperser Sᶜ K := fun A B hA hB => by
  simpa only [Set.mem_compl_iff, not_not] using (h A B hA hB).symm

theorem SumsetDisperser.mono [Add G] {S : Set G} {K K' : ℕ} (h : SumsetDisperser S K)
    (hK : K ≤ K') : SumsetDisperser S K' :=
  fun A B hA hB => h A B (hK.trans hA) (hK.trans hB)

/-- Every sumset disperser on `ι → U` is rectangle-free at the same threshold. -/
theorem SumsetDisperser.rectangleFree [AddZeroClass U] [Finite ι] [Finite U] {S : Set (ι → U)}
    {K : ℕ} (h : SumsetDisperser S K) : RectangleFree S K := by
  rw [rectangleFree_iff]
  intro X A B hsub
  by_contra! hge
  have hA' : K ≤ (zeroPad X '' A).ncard := by
    rw [ncard_image_zeroPad]
    exact hge.1
  have hB' : K ≤ (zeroPad Xᶜ '' B).ncard := by
    rw [ncard_image_zeroPad]
    exact hge.2
  obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hnot⟩ := (h _ _ hA' hB').2
  apply hnot
  apply hsub
  rw [mem_rectangle, domRestrict_zeroPad_add_zeroPad_compl_self,
    domRestrict_zeroPad_add_zeroPad_compl_compl]
  exact ⟨ha, hb⟩

/-- The complement of a sumset disperser on `ι → U` is also rectangle-free. -/
theorem SumsetDisperser.rectangleFree_compl [AddZeroClass U] [Finite ι] [Finite U]
    {S : Set (ι → U)} {K : ℕ} (h : SumsetDisperser S K) : RectangleFree Sᶜ K :=
  h.compl.rectangleFree

/-- `S` has sumset bias at most `b` above threshold `K` if for every `A, B ⊆ G` with
`K ≤ A.ncard` and `K ≤ B.ncard`, the fraction of pairs `(a, b) ∈ A ×ˢ B` with `a + b ∈ S` is
within `b` of `1 / 2`. -/
def SumsetBias [Add G] (S : Set G) (K : ℕ) (b : ℝ) : Prop :=
  ∀ A B : Set G, K ≤ A.ncard → K ≤ B.ncard →
    |((({p ∈ A ×ˢ B | p.1 + p.2 ∈ S}.ncard : ℝ)) - (A.ncard : ℝ) * (B.ncard : ℝ) / 2)| ≤
      b * ((A.ncard : ℝ) * (B.ncard : ℝ))

theorem SumsetBias.mono [Add G] {S : Set G} {K K' : ℕ} {b b' : ℝ} (h : SumsetBias S K b)
    (hK : K ≤ K') (hb : b ≤ b') : SumsetBias S K' b' := by
  intro A B hA hB
  refine (h A B (hK.trans hA) (hK.trans hB)).trans ?_
  exact mul_le_mul_of_nonneg_right hb (by positivity)

theorem SumsetBias.compl [Add G] [Finite G] {S : Set G} {K : ℕ} {b : ℝ} (h : SumsetBias S K b) :
    SumsetBias Sᶜ K b := by
  intro A B hA hB
  have hpart :
      {p ∈ A ×ˢ B | p.1 + p.2 ∈ Sᶜ}.ncard + {p ∈ A ×ˢ B | p.1 + p.2 ∈ S}.ncard =
        A.ncard * B.ncard := by
    have hdisj :
        Disjoint {p ∈ A ×ˢ B | p.1 + p.2 ∈ Sᶜ} {p ∈ A ×ˢ B | p.1 + p.2 ∈ S} :=
      Set.disjoint_left.mpr fun _ hp₁ hp₂ => hp₁.2 hp₂.2
    have hunion :
        {p ∈ A ×ˢ B | p.1 + p.2 ∈ Sᶜ} ∪ {p ∈ A ×ˢ B | p.1 + p.2 ∈ S} = A ×ˢ B := by
      ext p
      simp only [Set.mem_union, Set.mem_sep_iff, Set.mem_compl_iff]
      tauto
    rw [← Set.ncard_union_eq hdisj, hunion, Set.ncard_prod]
  have hcast :
      ({p ∈ A ×ˢ B | p.1 + p.2 ∈ Sᶜ}.ncard : ℝ) =
        (A.ncard : ℝ) * (B.ncard : ℝ) - ({p ∈ A ×ˢ B | p.1 + p.2 ∈ S}.ncard : ℝ) := by
    linarith [show ({p ∈ A ×ˢ B | p.1 + p.2 ∈ Sᶜ}.ncard : ℝ) +
      ({p ∈ A ×ˢ B | p.1 + p.2 ∈ S}.ncard : ℝ) = (A.ncard : ℝ) * (B.ncard : ℝ) by
      exact_mod_cast hpart]
  rw [hcast, show (A.ncard : ℝ) * (B.ncard : ℝ) - ({p ∈ A ×ˢ B | p.1 + p.2 ∈ S}.ncard : ℝ) -
      (A.ncard : ℝ) * (B.ncard : ℝ) / 2 =
    -((({p ∈ A ×ˢ B | p.1 + p.2 ∈ S}.ncard : ℝ)) - (A.ncard : ℝ) * (B.ncard : ℝ) / 2) by ring,
    abs_neg]
  exact h A B hA hB

/-- Sumset bias on `ι → U` implies rectangle bias with the same threshold and bias bound. -/
theorem SumsetBias.rectangleBias [AddZeroClass U] {S : Set (ι → U)} {K : ℕ} {b : ℝ}
    (h : SumsetBias S K b) : RectangleBias S K b := by
  intro X A B hA hB
  have hA' : K ≤ (zeroPad X '' A).ncard := by rwa [ncard_image_zeroPad]
  have hB' : K ≤ (zeroPad Xᶜ '' B).ncard := by rwa [ncard_image_zeroPad]
  have hbias := h (zeroPad X '' A) (zeroPad Xᶜ '' B) hA' hB'
  rw [ncard_sep_add_mem_image_zeroPad, ncard_image_zeroPad, ncard_image_zeroPad] at hbias
  rwa [ncard_rectangle, Nat.cast_mul]

/-- A set with sumset bias strictly below `1 / 2` at a positive threshold `K` is a sumset
disperser at threshold `K`. -/
theorem SumsetBias.sumsetDisperser [Add G] {S : Set G} {K : ℕ} {b : ℝ}
    (h : SumsetBias S K b) (hK : 0 < K) (hb : b < 1 / 2) : SumsetDisperser S K := by
  intro A B hA hB
  have hAB : 0 < (A.ncard : ℝ) * (B.ncard : ℝ) := by
    have : 0 < A.ncard := lt_of_lt_of_le hK hA
    have : 0 < B.ncard := lt_of_lt_of_le hK hB
    positivity
  have hbias := h A B hA hB
  constructor
  · by_contra! hnone
    have hempty : {p ∈ A ×ˢ B | p.1 + p.2 ∈ S} = ∅ := by
      ext ⟨a, b⟩
      simp only [Set.mem_prod, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨ha, hb⟩, hS⟩
      exact hnone a ha b hb hS
    rw [hempty, Set.ncard_empty, Nat.cast_zero, zero_sub, abs_neg,
      abs_of_pos (by positivity)] at hbias
    nlinarith
  · by_contra! hall
    have hfull : {p ∈ A ×ˢ B | p.1 + p.2 ∈ S} = A ×ˢ B := by
      ext ⟨a, b⟩
      simp only [Set.mem_prod]
      exact ⟨fun h => h.1, fun h => ⟨h, hall a h.1 b h.2⟩⟩
    rw [hfull, Set.ncard_prod, Nat.cast_mul,
      show (A.ncard : ℝ) * (B.ncard : ℝ) - (A.ncard : ℝ) * (B.ncard : ℝ) / 2 =
        (A.ncard : ℝ) * (B.ncard : ℝ) / 2 by ring,
      abs_of_pos (by positivity)] at hbias
    nlinarith

/-- A set on `ι → U` with sumset bias strictly below `1 / 2` at a positive threshold `K` is
`K`-rectangle-free. -/
theorem SumsetBias.rectangleFree [AddZeroClass U] [Finite ι] [Finite U] {S : Set (ι → U)} {K : ℕ}
    {b : ℝ} (h : SumsetBias S K b) (hK : 0 < K) (hb : b < 1 / 2) : RectangleFree S K :=
  (h.sumsetDisperser hK hb).rectangleFree

/-- In an additive group `G`, the number of pairs `(x, y) ∈ G × G` with `x + y ∈ S` is
`Nat.card G * S.ncard`. -/
theorem ncard_univ_prod_univ_add_mem [AddGroup G] (S : Set G) :
    {p ∈ (Set.univ : Set G) ×ˢ Set.univ | p.1 + p.2 ∈ S}.ncard = Nat.card G * S.ncard := by
  rw [← Set.ncard_univ G, ← Set.ncard_prod]
  refine Set.ncard_congr (fun p _ => (p.1, p.1 + p.2)) ?_ ?_ ?_
  · intro p hp
    exact ⟨trivial, hp.2⟩
  · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ _ _ h
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨rfl, hsum⟩
    exact Prod.ext rfl (add_left_cancel hsum)
  · rintro ⟨x, z⟩ ⟨_, hz⟩
    exact ⟨(x, -x + z), ⟨⟨trivial, trivial⟩, by simpa using hz⟩, by simp⟩

/-- In a finite additive group `G`, sumset bias at threshold `K ≤ Nat.card G` bounds the global
density bias of `S`. -/
theorem SumsetBias.abs_ncard_sub_half_le [AddGroup G] [Finite G] {S : Set G} {K : ℕ} {b : ℝ}
    (h : SumsetBias S K b) (hK : K ≤ Nat.card G) :
    |(S.ncard : ℝ) - (Nat.card G : ℝ) / 2| ≤ b * (Nat.card G : ℝ) := by
  have huniv : K ≤ (Set.univ : Set G).ncard := by rwa [Set.ncard_univ]
  have hbias := h Set.univ Set.univ huniv huniv
  rw [ncard_univ_prod_univ_add_mem, Set.ncard_univ, Nat.cast_mul] at hbias
  have hG : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos
  have hfac :
      |(Nat.card G : ℝ) * (S.ncard : ℝ) - (Nat.card G : ℝ) * (Nat.card G : ℝ) / 2| =
        (Nat.card G : ℝ) * |(S.ncard : ℝ) - (Nat.card G : ℝ) / 2| := by
    rw [show (Nat.card G : ℝ) * (S.ncard : ℝ) - (Nat.card G : ℝ) * (Nat.card G : ℝ) / 2 =
        (Nat.card G : ℝ) * ((S.ncard : ℝ) - (Nat.card G : ℝ) / 2) by ring,
      abs_mul, abs_of_pos hG]
  rw [hfac, show b * ((Nat.card G : ℝ) * (Nat.card G : ℝ)) =
      (Nat.card G : ℝ) * (b * (Nat.card G : ℝ)) by ring] at hbias
  exact le_of_mul_le_mul_left hbias hG

/-- In a finite additive group `G`, sumset bias at threshold `K ≤ Nat.card G` implies
`(1 / 2 - b) * Nat.card G ≤ S.ncard`. -/
theorem SumsetBias.ncard_ge [AddGroup G] [Finite G] {S : Set G} {K : ℕ} {b : ℝ}
    (h : SumsetBias S K b) (hK : K ≤ Nat.card G) :
    (1 / 2 - b) * (Nat.card G : ℝ) ≤ (S.ncard : ℝ) := by
  have hle := (abs_sub_le_iff.mp (h.abs_ncard_sub_half_le hK)).2
  linarith

/-! ### Distributional two-source sumset extractors -/

variable {β γ : Type*}

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

/-! ### Conditional frontier circuit lower bounds from sumset extractors -/

/-- **Conditional Gaussian frontier average-case lower bound from a sumset-extractor family.**
If `E_n : (Fin n → U) → Bool` is a `(k_n, δ_n)`-sumset extractor with `k_n = o(n)`, then for every
`ε > 0` there is `γ > 0` such that eventually every fan-in-two circuit `c` of inner size at most
`(L - ε) n` agrees with `{z | E_n z = true}` on at most a
`1 / 2 + δ_n + exp (-γ n)` fraction of the inputs, where
`L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625`. -/
theorem eventually_agreement_le_of_isSumsetExtractor [AddZeroClass U] [Finite U] [Nontrivial U]
    {E : ∀ n, (Fin n → U) → Bool} {k δ : ℕ → ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ > 0, ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 →
        (c.innerSize : ℝ) ≤ (1 + π / (3 * arccos ((1 + 2 * √2) / 4)) - ε) * n →
        agreement {z | E n z = true} {x | c.eval I x 0 ∈ Acc} ≤
          1 / 2 + δ n + Real.exp (-(γ * n)) := by
  have hbias : ∀ᶠ n in atTop, RectangleBias {z | E n z = true} ⌈(2 : ℝ) ^ k n⌉₊ (δ n) :=
    hE.mono fun n hn => hn.rectangleBias_ceil
  obtain ⟨γ, hγ, H⟩ := averageCaseBound_gaussian.{u, v} ε hε
  exact ⟨γ, hγ, H U (fun n => {z | E n z = true}) _ δ hbias (isLittleO_log_ceil_two_rpow hk)⟩

/-- **Conditional `(4.56249 - ε) n` average-case lower bound over `fullSignature 2 Bool`.**
If `E_n : (Fin n → Bool) → Bool` is a `(k_n, δ_n)`-sumset extractor with `k_n = o(n)`, then for
every `ε > 0` there is `γ > 0` such that eventually every circuit `c` over `fullSignature 2 Bool`
of size at most `(456249 / 100000 - ε) n` agrees with `{z | E_n z = true}` on at most a
`1 / 2 + δ_n + exp (-γ n)` fraction of the inputs. -/
theorem eventually_agreement_le_of_isSumsetExtractor_fullSignature
    {E : ∀ n, (Fin n → Bool) → Bool} {k δ : ℕ → ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ > 0, ∀ᶠ n in atTop, ∀ (I : Interpretation (fullSignature 2 Bool) Bool) (Acc : Set Bool)
      (c : Circuit (fullSignature 2 Bool) n 1),
        (c.size : ℝ) ≤ (456249 / 100000 - ε) * n →
        agreement {z | E n z = true} {x | c.eval I x 0 ∈ Acc} ≤
          1 / 2 + δ n + Real.exp (-(γ * n)) := by
  obtain ⟨γ, hγ, hbound⟩ := eventually_agreement_le_of_isSumsetExtractor.{0, 0} hE hk hε
  refine ⟨γ, hγ, hbound.mono fun n hn I Acc c hsize => ?_⟩
  have hinner : (c.innerSize : ℝ) ≤ (1 + π / (3 * arccos ((1 + 2 * √2) / 4)) - ε) * n := by
    calc (c.innerSize : ℝ) ≤ c.size := by exact_mod_cast c.innerSize_le_size
      _ ≤ (456249 / 100000 - ε) * n := hsize
      _ ≤ (1 + π / (3 * arccos ((1 + 2 * √2) / 4)) - ε) * n :=
        mul_le_mul_of_nonneg_right (by linarith [Gaussian.circuitCoefficient_ge_456249])
          (Nat.cast_nonneg n)
  exact hn (fullSignature 2 Bool) I Acc c c.fanInAtMost_fullSignature hinner

/-- **Conditional Gaussian frontier worst-case lower bound from a sumset-extractor family.**
If `E_n : (Fin n → U) → Bool` is a `(k_n, δ_n)`-sumset extractor with `k_n = o(n)` and
`δ_n ≤ δ₀ < 1 / 2` eventually, then for every `ε > 0` and all large `n`, every fan-in-two circuit
deciding `{z | E_n z = true}` has more than `(L - ε) n` inner gates. -/
theorem eventually_gaussian_sub_mul_lt_innerSize_of_isSumsetExtractor [AddGroup U] [Finite U]
    [Nontrivial U] {E : ∀ n, (Fin n → U) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc {z | E n z = true} →
        (1 + π / (3 * arccos ((1 + 2 * √2) / 4)) - ε) * n < c.innerSize := by
  have hsumset : ∀ᶠ n in atTop, SumsetBias {z | E n z = true} ⌈(2 : ℝ) ^ k n⌉₊ (δ n) :=
    hE.mono fun n hn => hn.sumsetBias_ceil
  have hfree : ∀ᶠ n in atTop, RectangleFree {z | E n z = true} ⌈(2 : ℝ) ^ k n⌉₊ := by
    filter_upwards [hsumset, hδ] with n hsn hδn
    exact hsn.rectangleFree (Nat.ceil_pos.mpr (by positivity)) (hδn.trans_lt hδ₀)
  have hK := isLittleO_log_ceil_two_rpow hk
  have hdense := isLittleO_sub_log_ncard_of_sumsetBias hsumset hK hδ hδ₀
  exact eventually_gaussian_sub_mul_lt_innerSize.{u, v} hfree hK hdense hε

/-- **Conditional `(4.56249 - ε) n` worst-case lower bound from a sumset-extractor family.** -/
theorem eventually_456249_div_100000_sub_mul_lt_innerSize_of_isSumsetExtractor [AddGroup U]
    [Finite U] [Nontrivial U] {E : ∀ n, (Fin n → U) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc {z | E n z = true} →
        (456249 / 100000 - ε) * n < c.innerSize := by
  filter_upwards [eventually_gaussian_sub_mul_lt_innerSize_of_isSumsetExtractor.{u, v}
    hE hk hδ hδ₀ hε] with n hn σ I Acc c hfan hdec
  refine lt_of_le_of_lt ?_ (hn σ I Acc c hfan hdec)
  exact mul_le_mul_of_nonneg_right (by linarith [Gaussian.circuitCoefficient_ge_456249])
    (Nat.cast_nonneg n)

/-- **Conditional `(4.56249 - ε) n` worst-case circuit size lower bound over
`fullSignature 2 Bool`.** -/
theorem eventually_456249_div_100000_sub_mul_lt_size_of_isSumsetExtractor
    {E : ∀ n, (Fin n → Bool) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (I : Interpretation (fullSignature 2 Bool) Bool) (Acc : Set Bool)
      (c : Circuit (fullSignature 2 Bool) n 1), c.Decides I Acc {z | E n z = true} →
        (456249 / 100000 - ε) * n < c.size := by
  filter_upwards [eventually_456249_div_100000_sub_mul_lt_innerSize_of_isSumsetExtractor.{0, 0}
    hE hk hδ hδ₀ hε] with n hn I Acc c hdec
  exact (hn (fullSignature 2 Bool) I Acc c c.fanInAtMost_fullSignature hdec).trans_le
    (by exact_mod_cast c.innerSize_le_size)

/-- **Conditional `(4.56249 - ε) n` worst-case circuit size lower bound for circuits computing
`single (E n)` over `fullSignature 2 Bool`.** -/
theorem eventually_456249_div_100000_sub_mul_lt_size_of_isSumsetExtractor_computes
    {E : ∀ n, (Fin n → Bool) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (I : Interpretation (fullSignature 2 Bool) Bool)
      (c : Circuit (fullSignature 2 Bool) n 1), c.Computes I (single (E n)) →
        (456249 / 100000 - ε) * n < c.size := by
  filter_upwards [eventually_456249_div_100000_sub_mul_lt_size_of_isSumsetExtractor
    hE hk hδ hδ₀ hε] with n hn I c hc
  exact hn I {true} c (hc.decides {true})

/-- **Conditional `(r - 1) s > (2 - ε) n` frontier lower bound for general fan-in `r ≥ 2` from a
sumset-extractor family.** -/
theorem eventually_two_sub_mul_lt_mul_innerSize_of_isSumsetExtractor [AddGroup U] [Finite U]
    [Nontrivial U] {E : ∀ n, (Fin n → U) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {r : ℕ} (hr : 2 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc {z | E n z = true} →
        (2 - ε) * n < (r - 1) * c.innerSize := by
  have hsumset : ∀ᶠ n in atTop, SumsetBias {z | E n z = true} ⌈(2 : ℝ) ^ k n⌉₊ (δ n) :=
    hE.mono fun n hn => hn.sumsetBias_ceil
  have hfree : ∀ᶠ n in atTop, RectangleFree {z | E n z = true} ⌈(2 : ℝ) ^ k n⌉₊ := by
    filter_upwards [hsumset, hδ] with n hsn hδn
    exact hsn.rectangleFree (Nat.ceil_pos.mpr (by positivity)) (hδn.trans_lt hδ₀)
  have hK := isLittleO_log_ceil_two_rpow hk
  have hdense := isLittleO_sub_log_ncard_of_sumsetBias hsumset hK hδ hδ₀
  exact eventually_two_sub_mul_lt_mul_innerSize.{u, v} hr hfree hK hdense hε

/-- **Conditional Gaussian vertex-score frontier lower bound for fan-in at most `r ≥ 2` from a
sumset-extractor family.** -/
theorem eventually_degreeCoefficient_lt_mul_innerSize_of_isSumsetExtractor [AddGroup U] [Finite U]
    [Nontrivial U] {E : ∀ n, (Fin n → U) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {r : ℕ} (hr : 2 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc {z | E n z = true} →
        (1 + 1 / Gaussian.degreeCoefficient (r + 1) - ε) * n < (r - 1) * c.innerSize := by
  have hsumset : ∀ᶠ n in atTop, SumsetBias {z | E n z = true} ⌈(2 : ℝ) ^ k n⌉₊ (δ n) :=
    hE.mono fun n hn => hn.sumsetBias_ceil
  have hfree : ∀ᶠ n in atTop, RectangleFree {z | E n z = true} ⌈(2 : ℝ) ^ k n⌉₊ := by
    filter_upwards [hsumset, hδ] with n hsn hδn
    exact hsn.rectangleFree (Nat.ceil_pos.mpr (by positivity)) (hδn.trans_lt hδ₀)
  have hK := isLittleO_log_ceil_two_rpow hk
  have hdense := isLittleO_sub_log_ncard_of_sumsetBias hsumset hK hδ hδ₀
  exact eventually_degreeCoefficient_lt_mul_innerSize.{u, v} hr hfree hK hdense hε

/-- **Conditional `(7 / 2 - ε) n < 2 s` frontier lower bound for fan-in at most three from a
sumset-extractor family.** -/
theorem eventually_seven_div_two_lt_two_mul_innerSize_of_isSumsetExtractor [AddGroup U] [Finite U]
    [Nontrivial U] {E : ∀ n, (Fin n → U) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 3 → c.Decides I Acc {z | E n z = true} →
        (7 / 2 - ε) * n < 2 * c.innerSize := by
  have hsumset : ∀ᶠ n in atTop, SumsetBias {z | E n z = true} ⌈(2 : ℝ) ^ k n⌉₊ (δ n) :=
    hE.mono fun n hn => hn.sumsetBias_ceil
  have hfree : ∀ᶠ n in atTop, RectangleFree {z | E n z = true} ⌈(2 : ℝ) ^ k n⌉₊ := by
    filter_upwards [hsumset, hδ] with n hsn hδn
    exact hsn.rectangleFree (Nat.ceil_pos.mpr (by positivity)) (hδn.trans_lt hδ₀)
  have hK := isLittleO_log_ceil_two_rpow hk
  have hdense := isLittleO_sub_log_ncard_of_sumsetBias hsumset hK hδ hδ₀
  exact eventually_seven_div_two_lt_two_mul_innerSize.{u, v} hfree hK hdense hε

/-- **Conditional Gaussian frontier lower bound for nondeterministic circuits of fan-in two from a
sumset-extractor family**, uniformly in the number `k'` of witness inputs. -/
theorem eventually_gaussian_sub_mul_lt_innerSize_nondeterministic_of_isSumsetExtractor
    [AddGroup U] [Finite U] [Nontrivial U] {E : ∀ n, (Fin n → U) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k' : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k') 1), c.FanInAtMost 2 →
        c.NondeterministicDecides I Acc {z | E n z = true} →
          (1 + π / (3 * arccos ((1 + 2 * √2) / 4)) - ε) * n < c.innerSize := by
  have hsumset : ∀ᶠ n in atTop, SumsetBias {z | E n z = true} ⌈(2 : ℝ) ^ k n⌉₊ (δ n) :=
    hE.mono fun n hn => hn.sumsetBias_ceil
  have hfree : ∀ᶠ n in atTop, RectangleFree {z | E n z = true} ⌈(2 : ℝ) ^ k n⌉₊ := by
    filter_upwards [hsumset, hδ] with n hsn hδn
    exact hsn.rectangleFree (Nat.ceil_pos.mpr (by positivity)) (hδn.trans_lt hδ₀)
  have hK := isLittleO_log_ceil_two_rpow hk
  have hdense := isLittleO_sub_log_ncard_of_sumsetBias hsumset hK hδ hδ₀
  exact eventually_gaussian_sub_mul_lt_innerSize_of_nondeterministicDecides.{u, v}
    hfree hK hdense hε

/-- **Conditional `(4.56249 - ε) n` frontier lower bound for nondeterministic circuits of fan-in two
from a sumset-extractor family**, uniformly in the number `k'` of witness inputs. -/
theorem eventually_456249_div_100000_sub_mul_lt_innerSize_nondeterministic_of_isSumsetExtractor
    [AddGroup U] [Finite U] [Nontrivial U] {E : ∀ n, (Fin n → U) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k' : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k') 1), c.FanInAtMost 2 →
        c.NondeterministicDecides I Acc {z | E n z = true} →
          (456249 / 100000 - ε) * n < c.innerSize := by
  have hsumset : ∀ᶠ n in atTop, SumsetBias {z | E n z = true} ⌈(2 : ℝ) ^ k n⌉₊ (δ n) :=
    hE.mono fun n hn => hn.sumsetBias_ceil
  have hfree : ∀ᶠ n in atTop, RectangleFree {z | E n z = true} ⌈(2 : ℝ) ^ k n⌉₊ := by
    filter_upwards [hsumset, hδ] with n hsn hδn
    exact hsn.rectangleFree (Nat.ceil_pos.mpr (by positivity)) (hδn.trans_lt hδ₀)
  have hK := isLittleO_log_ceil_two_rpow hk
  have hdense := isLittleO_sub_log_ncard_of_sumsetBias hsumset hK hδ hδ₀
  exact eventually_456249_div_100000_sub_mul_lt_innerSize_of_nondeterministicDecides.{u, v}
    hfree hK hdense hε

universe w

/-- **Conditional Gaussian frontier lower bound with aggregate gates at ordinary fan-in two from a
sumset-extractor family.** -/
theorem eventually_gaussian_sub_mul_lt_card_of_aggregates_of_isSumsetExtractor
    [AddGroup U] [Finite U] [Nontrivial U] {E : ∀ n, (Fin n → U) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1) (special : Fin c.size → Prop) [DecidablePred special] (T : Type w)
      [CommMonoid T] [Finite T],
        (∀ g, ¬special g → σ.Arity (c.program.lines g).op ≤ 2) →
        (∀ g, special g → Aggregates (I (c.program.lines g).op) T) →
        Nat.card {g // special g} * Real.log (Nat.card T) ≤ β n →
        c.Decides I Acc {z | E n z = true} →
          (1 + π / (3 * arccos ((1 + 2 * √2) / 4)) - ε) * n <
            (c.program.innerGates.filter fun g => ¬special g).card := by
  have hsumset : ∀ᶠ n in atTop, SumsetBias {z | E n z = true} ⌈(2 : ℝ) ^ k n⌉₊ (δ n) :=
    hE.mono fun n hn => hn.sumsetBias_ceil
  have hfree : ∀ᶠ n in atTop, RectangleFree {z | E n z = true} ⌈(2 : ℝ) ^ k n⌉₊ := by
    filter_upwards [hsumset, hδ] with n hsn hδn
    exact hsn.rectangleFree (Nat.ceil_pos.mpr (by positivity)) (hδn.trans_lt hδ₀)
  have hK := isLittleO_log_ceil_two_rpow hk
  have hdense := isLittleO_sub_log_ncard_of_sumsetBias hsumset hK hδ hδ₀
  exact eventually_gaussian_sub_mul_lt_card_of_aggregates.{u, v, w} hfree hK hdense hβ hε

/-- **Conditional `(4.56249 - ε) n` frontier lower bound with aggregate gates at ordinary fan-in two
from a sumset-extractor family.** -/
theorem eventually_456249_div_100000_sub_mul_lt_card_of_aggregates_of_isSumsetExtractor
    [AddGroup U] [Finite U] [Nontrivial U] {E : ∀ n, (Fin n → U) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1) (special : Fin c.size → Prop) [DecidablePred special] (T : Type w)
      [CommMonoid T] [Finite T],
        (∀ g, ¬special g → σ.Arity (c.program.lines g).op ≤ 2) →
        (∀ g, special g → Aggregates (I (c.program.lines g).op) T) →
        Nat.card {g // special g} * Real.log (Nat.card T) ≤ β n →
        c.Decides I Acc {z | E n z = true} →
          (456249 / 100000 - ε) * n <
            (c.program.innerGates.filter fun g => ¬special g).card := by
  have hsumset : ∀ᶠ n in atTop, SumsetBias {z | E n z = true} ⌈(2 : ℝ) ^ k n⌉₊ (δ n) :=
    hE.mono fun n hn => hn.sumsetBias_ceil
  have hfree : ∀ᶠ n in atTop, RectangleFree {z | E n z = true} ⌈(2 : ℝ) ^ k n⌉₊ := by
    filter_upwards [hsumset, hδ] with n hsn hδn
    exact hsn.rectangleFree (Nat.ceil_pos.mpr (by positivity)) (hδn.trans_lt hδ₀)
  have hK := isLittleO_log_ceil_two_rpow hk
  have hdense := isLittleO_sub_log_ncard_of_sumsetBias hsumset hK hδ hδ₀
  exact eventually_456249_div_100000_sub_mul_lt_card_of_aggregates.{u, v, w} hfree hK hdense hβ hε

/-! ### Sumset dispersers are affine dispersers -/

section AffineDisperser

open Cslib.BitString

/-- **Every sumset disperser on the Boolean cube is an affine disperser.** If `{z | f z = true}` is
a `K`-sumset disperser on `BitString n` with `K ≤ 2 ^ d`, then `f` is an affine disperser for
dimension `d` (`IsAffineDisperser f d`). Indeed, for any injective affine map
`g : BitString d → BitString n`, the sets `A = range g` and `B = range (fun y => g y + g 0)` both
have cardinality `2 ^ d ≥ K`, and every sum `g x + (g y + g 0) = g (x + y + 0) = g (x + y)` lies in
`range g`. -/
theorem SumsetDisperser.isAffineDisperser {n K d : ℕ} {f : BitString n → Bool}
    (h : SumsetDisperser {z | f z = true} K) (hK : K ≤ 2 ^ d) :
    IsAffineDisperser f d := by
  intro g hg hinj
  have hcard_d : Nat.card (BitString d) = 2 ^ d := by
    simp [BitString]
  have hA : K ≤ (Set.range g).ncard := by
    rw [Set.ncard_range_of_injective hinj, hcard_d]
    exact hK
  have hinj_shift : Function.Injective (fun y : BitString d => g y + g 0) :=
    fun y₁ y₂ hyeq => hinj (add_right_cancel hyeq)
  have hB : K ≤ (Set.range (fun y : BitString d => g y + g 0)).ncard := by
    rw [Set.ncard_range_of_injective hinj_shift, hcard_d]
    exact hK
  obtain ⟨⟨a₁, ⟨x₁, rfl⟩, b₁, ⟨y₁, rfl⟩, h1⟩, ⟨a₀, ⟨x₀, rfl⟩, b₀, ⟨y₀, rfl⟩, h0⟩⟩ :=
    h (Set.range g) (Set.range (fun y => g y + g 0)) hA hB
  have hsum (x y : BitString d) : g x + (g y + g 0) = g (x + y) := by
    rw [← add_assoc, ← hg x y 0, add_zero]
  simp only [Set.mem_ofPred_eq, hsum] at h1 h0
  exact ⟨x₁ + y₁, x₀ + y₀, fun heq => h0 (heq ▸ h1)⟩

/-- **A Boolean function with sumset bias `< 1 / 2` at threshold `K ≤ 2 ^ d` is an affine disperser
for dimension `d`.** -/
theorem SumsetBias.isAffineDisperser {n K d : ℕ} {f : BitString n → Bool} {b : ℝ}
    (h : SumsetBias {z | f z = true} K b) (hKpos : 0 < K) (hb : b < 1 / 2) (hK : K ≤ 2 ^ d) :
    IsAffineDisperser f d :=
  (h.sumsetDisperser hKpos hb).isAffineDisperser hK

/-- **Every `(k, δ)`-sumset extractor with `δ < 1 / 2` and `k ≤ d` is an affine disperser for
dimension `d`.** -/
theorem IsSumsetExtractor.isAffineDisperser {n d : ℕ} {f : BitString n → Bool} {k δ : ℝ}
    (h : IsSumsetExtractor f k δ) (hδ : δ < 1 / 2) (hk : k ≤ d) :
    IsAffineDisperser f d := by
  refine h.sumsetBias_ceil.isAffineDisperser (Nat.ceil_pos.mpr (by positivity)) hδ ?_
  rw [Nat.ceil_le, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le one_le_two hk

end AffineDisperser

/-! ### Balanced padding of sumset dispersers -/

section BalancePad

/-- **Balanced padding** of an `n`-bit Boolean function to `n + 1` bits by XORing with the first
input bit: `balancePad f x = f (Fin.tail x) ^^ x 0`. One fresh bit makes the function accept
exactly half of the `(n + 1)`-cube while preserving sumset dispersion at twice the threshold. -/
def balancePad {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin (n + 1) → Bool) : Bool :=
  f (Fin.tail x) ^^ x 0

@[simp]
theorem balancePad_apply {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin (n + 1) → Bool) :
    balancePad f x = (f (Fin.tail x) ^^ x 0) :=
  rfl

theorem balancePad_cons {n : ℕ} (f : (Fin n → Bool) → Bool) (b : Bool) (x : Fin n → Bool) :
    balancePad f (Fin.cons b x) = (f x ^^ b) := by
  simp

theorem balancePad_add {n : ℕ} (f : (Fin n → Bool) → Bool) (x y : Fin (n + 1) → Bool) :
    balancePad f (x + y) = (f (Fin.tail x + Fin.tail y) ^^ (x 0 ^^ y 0)) := by
  have htail : Fin.tail (x + y) = Fin.tail x + Fin.tail y := rfl
  have hzero : (x + y) 0 = (x 0 ^^ y 0) := rfl
  rw [balancePad, htail, hzero]

/-- **Balanced padding accepts `2 ^ n` inputs** out of `2 ^ (n + 1)`: for each `y : Fin n → Bool`,
`Fin.cons (!f y) y` is the unique accepting extension. -/
theorem ncard_setOf_balancePad {n : ℕ} (f : (Fin n → Bool) → Bool) :
    {x : Fin (n + 1) → Bool | balancePad f x = true}.ncard = 2 ^ n := by
  have hbij : Set.BijOn (fun y : Fin n → Bool => Fin.cons (!f y) y) Set.univ
      {x : Fin (n + 1) → Bool | balancePad f x = true} := by
    refine ⟨fun y _ => ?_, fun y₁ _ y₂ _ h => ?_, fun x hx => ?_⟩
    · simp only [Set.mem_ofPred_eq, balancePad_cons]
      cases f y <;> rfl
    · simpa only [Fin.tail_cons] using congrArg Fin.tail h
    · refine ⟨Fin.tail x, Set.mem_univ _, ?_⟩
      simp only [Set.mem_ofPred_eq, balancePad] at hx
      have h0 : (!f (Fin.tail x)) = x 0 := by
        revert hx
        cases f (Fin.tail x) <;> cases x 0 <;> decide
      dsimp only
      rw [h0, Fin.cons_self_tail]
  rw [← hbij.ncard_eq, Set.ncard_univ]
  simp

/-- The tail strings in the fiber of `A ⊆ Fin (n + 1) → Bool` where coordinate `0` equals `b`. -/
def tailFiber {n : ℕ} (A : Set (Fin (n + 1) → Bool)) (b : Bool) : Set (Fin n → Bool) :=
  Fin.tail '' {x ∈ A | x 0 = b}

theorem ncard_tailFiber {n : ℕ} (A : Set (Fin (n + 1) → Bool)) (b : Bool) :
    (tailFiber A b).ncard = {x ∈ A | x 0 = b}.ncard := by
  refine Set.InjOn.ncard_image fun x hx y hy htail => ?_
  have h0 : x 0 = y 0 := hx.2.trans hy.2.symm
  rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, h0, htail]

theorem ncard_tailFiber_false_add_true {n : ℕ} (A : Set (Fin (n + 1) → Bool)) :
    (tailFiber A false).ncard + (tailFiber A true).ncard = A.ncard := by
  rw [ncard_tailFiber, ncard_tailFiber]
  have hunion : {x ∈ A | x 0 = false} ∪ {x ∈ A | x 0 = true} = A := by
    ext x
    simp only [Set.mem_union, Set.mem_sep_iff]
    rcases Bool.dichotomy (x 0) with h | h <;> simp [h]
  have hdisj : Disjoint {x ∈ A | x 0 = false} {x ∈ A | x 0 = true} := by
    rw [Set.disjoint_left]
    intro x hxfalse hxtrue
    exact Bool.false_ne_true (hxfalse.2.symm.trans hxtrue.2)
  rw [← Set.ncard_union_eq hdisj, hunion]

theorem exists_le_ncard_tailFiber {n K : ℕ} {A : Set (Fin (n + 1) → Bool)}
    (hA : 2 * K ≤ A.ncard) : ∃ b : Bool, K ≤ (tailFiber A b).ncard := by
  have hsum := ncard_tailFiber_false_add_true A
  by_cases hfalse : K ≤ (tailFiber A false).ncard
  · exact ⟨false, hfalse⟩
  · exact ⟨true, by omega⟩

/-- **Balanced padding preserves sumset dispersion** with a factor-two threshold loss: if
`{z | f z = true}` is a `K`-sumset disperser on `Fin n → Bool`, then `{z | balancePad f z = true}`
is a `(2 * K)`-sumset disperser on `Fin (n + 1) → Bool`. -/
theorem SumsetDisperser.balancePad {n K : ℕ} {f : (Fin n → Bool) → Bool}
    (h : SumsetDisperser {z | f z = true} K) :
    SumsetDisperser {z | Frontier.balancePad f z = true} (2 * K) := by
  intro A B hA hB
  obtain ⟨p, hp⟩ := exists_le_ncard_tailFiber hA
  obtain ⟨q, hq⟩ := exists_le_ncard_tailFiber hB
  obtain ⟨⟨u₁, hu₁, v₁, hv₁, htrue⟩, ⟨u₀, hu₀, v₀, hv₀, hfalse⟩⟩ :=
    h (tailFiber A p) (tailFiber B q) hp hq
  rcases hu₁ with ⟨a₁, ⟨ha₁A, ha₁0⟩, rfl⟩
  rcases hv₁ with ⟨b₁, ⟨hb₁B, hb₁0⟩, rfl⟩
  rcases hu₀ with ⟨a₀, ⟨ha₀A, ha₀0⟩, rfl⟩
  rcases hv₀ with ⟨b₀, ⟨hb₀B, hb₀0⟩, rfl⟩
  simp only [Set.mem_ofPred_eq] at htrue hfalse
  cases hpq : (p ^^ q)
  · refine ⟨⟨a₁, ha₁A, b₁, hb₁B, ?_⟩, ⟨a₀, ha₀A, b₀, hb₀B, ?_⟩⟩
    · simp only [Set.mem_ofPred_eq, balancePad_add, ha₁0, hb₁0, hpq, htrue, Bool.xor_false]
    · simp only [Set.mem_ofPred_eq, balancePad_add, ha₀0, hb₀0, hpq, Bool.xor_false]
      exact hfalse
  · refine ⟨⟨a₀, ha₀A, b₀, hb₀B, ?_⟩, ⟨a₁, ha₁A, b₁, hb₁B, ?_⟩⟩
    · simp only [Set.mem_ofPred_eq, balancePad_add, ha₀0, hb₀0, hpq]
      revert hfalse
      cases f (Fin.tail a₀ + Fin.tail b₀) <;> decide
    · simp only [Set.mem_ofPred_eq, balancePad_add, ha₁0, hb₁0, hpq, htrue]
      decide

/-- **Balanced padding of a `K`-sumset disperser is `(2 * K)`-rectangle-free**, without any
assumption on the accepting density of `f`. -/
theorem SumsetDisperser.balancePad_rectangleFree {n K : ℕ} {f : (Fin n → Bool) → Bool}
    (h : SumsetDisperser {z | f z = true} K) :
    RectangleFree {z | Frontier.balancePad f z = true} (2 * K) :=
  h.balancePad.rectangleFree

/-- **Balanced padding of a `(k, δ)`-sumset extractor (`δ < 1 / 2`) is a `(2 * ⌈2^k⌉₊)`-sumset
disperser.** -/
theorem IsSumsetExtractor.balancePad_sumsetDisperser {n : ℕ} {f : (Fin n → Bool) → Bool}
    {k δ : ℝ} (h : IsSumsetExtractor f k δ) (hδ : δ < 1 / 2) :
    SumsetDisperser {z | Frontier.balancePad f z = true} (2 * ⌈(2 : ℝ) ^ k⌉₊) :=
  (h.sumsetBias_ceil.sumsetDisperser (Nat.ceil_pos.mpr (by positivity)) hδ).balancePad

/-- **Balanced padding of a `(k, δ)`-sumset extractor (`δ < 1 / 2`) is `(2 * ⌈2^k⌉₊)`-rectangle-free
and accepts exactly `2 ^ n` inputs.** -/
theorem IsSumsetExtractor.balancePad_rectangleFree {n : ℕ} {f : (Fin n → Bool) → Bool}
    {k δ : ℝ} (h : IsSumsetExtractor f k δ) (hδ : δ < 1 / 2) :
    RectangleFree {z | Frontier.balancePad f z = true} (2 * ⌈(2 : ℝ) ^ k⌉₊) :=
  (IsSumsetExtractor.balancePad_sumsetDisperser h hδ).rectangleFree

/-- **The balanced-padded Boolean family**: at input length `0` it returns `false`, and at input
length `n + 1` it applies `balancePad` to `f n`. -/
def balancePadFamily (f : ∀ n, (Fin n → Bool) → Bool) : ∀ n, (Fin n → Bool) → Bool
  | 0 => fun _ => false
  | n + 1 => balancePad (f n)

@[simp]
theorem balancePadFamily_zero (f : ∀ n, (Fin n → Bool) → Bool) :
    balancePadFamily f 0 = fun _ => false :=
  rfl

@[simp]
theorem balancePadFamily_succ (f : ∀ n, (Fin n → Bool) → Bool) (n : ℕ) :
    balancePadFamily f (n + 1) = balancePad (f n) :=
  rfl

/-- **Exact logarithmic density of `balancePadFamily`:** its logarithmic density deficit on the
Boolean cube is `log 2` for every `n ≥ 1`, hence `o(n)`. -/
theorem isLittleO_sub_log_ncard_balancePadFamily (f : ∀ n, (Fin n → Bool) → Bool) :
    (fun n : ℕ => n * Real.log (Nat.card Bool) -
      Real.log {z | balancePadFamily f n z = true}.ncard) =o[atTop] fun n : ℕ => (n : ℝ) := by
  have hconst : (fun _ : ℕ => Real.log 2) =o[atTop] fun n : ℕ => (n : ℝ) :=
    (isLittleO_const_id_atTop (Real.log 2)).natCast_atTop
  refine hconst.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [balancePadFamily_succ, ncard_setOf_balancePad, Nat.card_eq_fintype_card, Fintype.card_bool]
  push_cast
  rw [Real.log_pow]
  ring

/-- **Any sumset-disperser family with sublinear log-threshold satisfies all worst-case frontier
hypotheses after one-bit balanced padding**, with no quantitative bias assumption. -/
theorem frontierHypotheses_balancePadFamily {D : ∀ n, (Fin n → Bool) → Bool} {K : ℕ → ℕ}
    (hD : ∀ᶠ n in atTop, SumsetDisperser {z | D n z = true} (K n))
    (hKpos : ∀ᶠ n in atTop, 0 < K n)
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n : ℕ => (n : ℝ)) :
    (∀ᶠ n in atTop,
      RectangleFree {z | balancePadFamily D n z = true} (2 * K (n - 1))) ∧
    ((fun n => Real.log (2 * K (n - 1) : ℕ)) =o[atTop] fun n : ℕ => (n : ℝ)) ∧
    ((fun n => n * Real.log (Nat.card Bool) -
      Real.log {z | balancePadFamily D n z = true}.ncard) =o[atTop] fun n : ℕ => (n : ℝ)) := by
  refine ⟨?_, ?_, isLittleO_sub_log_ncard_balancePadFamily D⟩
  · filter_upwards [(tendsto_sub_atTop_nat 1).eventually hD, eventually_ge_atTop 1] with n hn hn1
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    dsimp only [Nat.add_sub_cancel, balancePadFamily_succ] at hn ⊢
    exact hn.balancePad_rectangleFree
  · have hKshift : (fun n : ℕ => Real.log (K (n - 1))) =o[atTop] fun n : ℕ => (n : ℝ) := by
      refine (hK.comp_tendsto (tendsto_sub_atTop_nat 1)).trans_isBigO (IsBigO.of_bound 1 ?_)
      filter_upwards with n
      simp only [Function.comp_apply, Real.norm_natCast, one_mul, Nat.cast_le]
      omega
    have hconst : (fun _ : ℕ => Real.log 2) =o[atTop] fun n : ℕ => (n : ℝ) :=
      (isLittleO_const_id_atTop (Real.log 2)).natCast_atTop
    refine (hconst.add hKshift).congr' ?_ EventuallyEq.rfl
    filter_upwards [(tendsto_sub_atTop_nat 1).eventually hKpos] with n hn
    have hKn_pos : (0 : ℝ) < K (n - 1) := by exact_mod_cast hn
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.log_mul two_ne_zero hKn_pos.ne']

/-- **Conditional `(4.56249 - ε) n` worst-case circuit size lower bound over `fullSignature 2 Bool`
for `balancePadFamily D` from a sumset-disperser family `D`**, without any quantitative bias
hypothesis. -/
theorem eventually_456249_div_100000_sub_mul_lt_size_balancePadFamily
    {D : ∀ n, (Fin n → Bool) → Bool} {K : ℕ → ℕ}
    (hD : ∀ᶠ n in atTop, SumsetDisperser {z | D n z = true} (K n))
    (hKpos : ∀ᶠ n in atTop, 0 < K n)
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n : ℕ => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (I : Interpretation (fullSignature 2 Bool) Bool) (Acc : Set Bool)
      (c : Circuit (fullSignature 2 Bool) n 1),
        c.Decides I Acc {z | balancePadFamily D n z = true} →
          (456249 / 100000 - ε) * n < c.size := by
  obtain ⟨hfree, hK', hdense⟩ := frontierHypotheses_balancePadFamily hD hKpos hK
  filter_upwards [eventually_456249_div_100000_sub_mul_lt_innerSize.{0, 0} hfree hK' hdense hε]
    with n hn I Acc c hdec
  exact (hn (fullSignature 2 Bool) I Acc c c.fanInAtMost_fullSignature hdec).trans_le
    (by exact_mod_cast c.innerSize_le_size)

end BalancePad

end Cslib.Circuits.Frontier
