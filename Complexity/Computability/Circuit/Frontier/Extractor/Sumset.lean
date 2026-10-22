/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Unconditional
public import Complexity.Foundations.Data.BitString.AffineDisperser
public import Complexity.Foundations.Data.BitString.Basic
public import Complexity.Init

import Mathlib.Data.Set.Card

/-!
# Zero-padding of partial assignments, sumset dispersers, and sumset bias

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
pseudorandomness directly to the rectangle hypotheses of the frontier method and to affine
dispersers on the Boolean cube.

## Main definitions

* `Cslib.Circuits.Frontier.zeroPad`: extend `a : X → U` by `0` outside `X`.
* `Cslib.Circuits.Frontier.SumsetDisperser`: neither `S` nor `Sᶜ` contains `A + B` for
  `|A|, |B| ≥ K`.
* `Cslib.Circuits.Frontier.SumsetBias`: `a + b ∈ S` has bias at most `b` on `A ×ˢ B` for
  `|A|, |B| ≥ K`.

## Main results

* `Cslib.Circuits.Frontier.SumsetDisperser.rectangleFree`: a sumset disperser is rectangle-free.
* `Cslib.Circuits.Frontier.SumsetBias.rectangleBias`: sumset bias bounds rectangle bias.
* `Cslib.Circuits.Frontier.SumsetBias.abs_ncard_sub_half_le`,
  `Cslib.Circuits.Frontier.SumsetBias.ncard_ge`: sumset bias bounds global accepting density in any
  finite additive group.
* `Cslib.Circuits.Frontier.SumsetDisperser.isAffineDisperser`,
  `Cslib.Circuits.Frontier.SumsetBias.isAffineDisperser`: every sumset disperser at threshold
  `K ≤ 2 ^ d` is an affine disperser for dimension `d`.

## References

* [B. Chor and O. Goldreich, *Unbiased bits from sources of weak randomness and probabilistic
  communication complexity*][ChorGoldreich1988]
* [E. Chattopadhyay and J.-J. Liao, *Extractors for Sum of Two Sources*][ChattopadhyayLiao2022]
* [S. Schlesinger, *Frontier circuit lower bounds and two-source sumset extractors in
  Complexitylib*][Schlesinger2026FrontierExtractor]
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

universe u

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

end AffineDisperser

end Cslib.Circuits.Frontier
