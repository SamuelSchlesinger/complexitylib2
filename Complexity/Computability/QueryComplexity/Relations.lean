/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Certificate

/-!
# Relations between block sensitivity, certificate and decision tree complexity

Block sensitivity bounds certificate and decision tree complexity polynomially, so that the three
are polynomially related [BuhrmanDeWolf2002].

* `C(f) ≤ s(f) bs(f)`, due to Nisan [Nisan1991]
  (`QueryComplexity.certificateComplexity_le_sensitivity_mul_blockSensitivity`). Take a largest
  family of pairwise disjoint minimal sensitive blocks at `x`. Every block of it has at most `s(f)`
  coordinates (`IsMinimalSensitiveBlock.card_le_sensitivity`), and their union is a certificate for
  `x`: an input agreeing with `x` on it but with a different value differs from `x` on a sensitive
  block disjoint from the family, which contains a minimal one and would enlarge the family.
* `D(f) ≤ bs₀(f) C₁(f) ≤ C(f) bs(f)`, where `bs_b(f)` and `C_b(f)` are the largest block
  sensitivity and certificate complexity at an input of value `b`
  (`DecisionTree.complexity_le_blockSensitivityFor_mul_certificateComplexityFor`). This is a
  one-sided form of the bound `D(f) ≤ C₁(f) bs(f)` of Beals, Buhrman, Cleve, Mosca and de Wolf
  [BealsBuhrmanCleveMoscaDeWolf2001] ([BuhrmanDeWolf2002], Theorem 11). Query a smallest
  certificate of an input of value `1`. Every input of value `0` of the function restricted by the
  answers has one more sensitive block in the original function, the coordinates of the
  certificate on which it differs from the input of value `1`, so its block sensitivity has
  dropped.

With `C(f) ≤ s(f) bs(f) ≤ bs(f)²` this gives `D(f) ≤ bs(f)³`
(`DecisionTree.complexity_le_blockSensitivity_pow_three`; [BuhrmanDeWolf2002], Corollary 1).

## Main definitions

* `Cslib.QueryComplexity.blockSensitivityFor`: the block sensitivity `bs_b(f)` of the inputs
  where `f` has value `b`.

## Main results

* `Cslib.QueryComplexity.certificateComplexityAt_le_sensitivity_mul_blockSensitivityAt`:
  `C(f, x) ≤ s(f) bs(f, x)`.
* `Cslib.QueryComplexity.certificateComplexity_le_sensitivity_mul_blockSensitivity`:
  `C(f) ≤ s(f) bs(f)`.
* `Cslib.QueryComplexity.certificateComplexity_le_blockSensitivity_sq`: `C(f) ≤ bs(f)²`.
* `Cslib.DecisionTree.complexity_le_blockSensitivityFor_mul_certificateComplexityFor`:
  `D(f) ≤ bs₀(f) C₁(f)`.
* `Cslib.DecisionTree.complexity_le_certificateComplexity_mul_blockSensitivity`:
  `D(f) ≤ C(f) bs(f)`.
* `Cslib.DecisionTree.complexity_le_blockSensitivity_pow_three`: `D(f) ≤ bs(f)³`.

## References

* [N. Nisan, *CREW PRAMs and decision trees*][Nisan1991]
* [R. Beals, H. Buhrman, R. Cleve, M. Mosca, R. de Wolf, *Quantum lower bounds by
  polynomials*][BealsBuhrmanCleveMoscaDeWolf2001]
* [H. Buhrman, R. de Wolf, *Complexity measures and decision tree complexity:
  a survey*][BuhrmanDeWolf2002]
-/

@[expose] public section

namespace Cslib

open Finset BitString

variable {n : ℕ}

/-- Flipping the coordinates on which `y` differs from `x` turns `x` into `y`. -/
theorem BitString.flipBlock_filter_ne (x y : BitString n) : flipBlock {i | y i ≠ x i} x = y := by
  funext i
  by_cases h : y i = x i
  · rw [flipBlock_apply_of_notMem (by simpa using h), h]
  · rw [flipBlock_apply_of_mem (by simpa using h)]
    cases hx : x i <;> cases hy : y i <;> simp_all

namespace QueryComplexity

variable {f : BooleanFunction n} {x : BitString n}

/-! ### `C(f) ≤ s(f) bs(f)` -/

/-- A sensitive block contains a minimal sensitive block. -/
theorem IsSensitiveBlock.exists_isMinimalSensitiveBlock_subset {B : Block n}
    (hB : IsSensitiveBlock f x B) : ∃ C ⊆ B, IsMinimalSensitiveBlock f x C := by
  obtain ⟨C, hC, hmin⟩ := exists_min_image (B.powerset.filter (IsSensitiveBlock f x)) card
    ⟨B, mem_filter.2 ⟨mem_powerset_self B, hB⟩⟩
  obtain ⟨hCB, hCs⟩ := mem_filter.1 hC
  refine ⟨C, mem_powerset.1 hCB, hCs, fun D hDC hD => ?_⟩
  have := hmin D (mem_filter.2 ⟨mem_powerset.2 (hDC.subset.trans (mem_powerset.1 hCB)), hD⟩)
  exact absurd (card_lt_card hDC) (not_lt.2 this)

/-- A sensitive block is nonempty. -/
theorem IsSensitiveBlock.nonempty {B : Block n} (hB : IsSensitiveBlock f x B) : B.Nonempty :=
  nonempty_iff_ne_empty.2 fun h => hB (by rw [h, flipBlock_empty])

/-- The union of a largest family of pairwise disjoint minimal sensitive blocks is a
certificate. -/
private theorem isCertificate_biUnion_of_maximal {F : Finset (Block n)}
    (hF : IsSensitiveFamily f x F) (hmin : ∀ B ∈ F, IsMinimalSensitiveBlock f x B)
    (hmax : ∀ G : Finset (Block n), IsSensitiveFamily f x G →
      (∀ B ∈ G, IsMinimalSensitiveBlock f x B) → #G ≤ #F) :
    IsCertificate f x (F.biUnion id) := by
  intro y hy
  by_contra hne
  -- the coordinates on which `y` differs from `x` form a sensitive block outside the family
  have hB : IsSensitiveBlock f x ({i | y i ≠ x i} : Finset (Fin n)) := by
    rw [IsSensitiveBlock, flipBlock_filter_ne]
    exact hne
  obtain ⟨C, hCsub, hC⟩ := hB.exists_isMinimalSensitiveBlock_subset
  have hdisj : ∀ B ∈ F, Disjoint C B := fun B hBF => disjoint_left.2 fun i hiC hiB =>
    (mem_filter.1 (hCsub hiC)).2 (hy i (mem_biUnion.2 ⟨B, hBF, hiB⟩))
  have hCF : C ∉ F := fun hCF => by
    obtain ⟨i, hi⟩ := hC.1.nonempty
    exact disjoint_left.1 (hdisj C hCF) hi hi
  -- adding it gives a larger family
  have hG : IsSensitiveFamily f x (insert C F) := by
    refine ⟨fun B hB => ?_, ?_⟩
    · rcases mem_insert.1 hB with rfl | hB
      · exact hC.1
      · exact hF.1 B hB
    · rw [coe_insert]
      exact hF.2.insert fun B hB _ => hdisj B hB
  have := hmax _ hG fun B hB => by
    rcases mem_insert.1 hB with rfl | hB
    · exact hC
    · exact hmin B hB
  rw [card_insert_of_notMem hCF] at this
  omega

/-- **Nisan's bound at an input**: `C(f, x) ≤ s(f) bs(f, x)`. -/
theorem certificateComplexityAt_le_sensitivity_mul_blockSensitivityAt (f : BooleanFunction n)
    (x : BitString n) : certificateComplexityAt f x ≤ sensitivity f * blockSensitivityAt f x := by
  classical
  -- a largest family of pairwise disjoint minimal sensitive blocks
  obtain ⟨F, hF, hmax⟩ := exists_max_image
    ((sensitiveFamilies f x).filter fun F => ∀ B ∈ F, IsMinimalSensitiveBlock f x B) card
    ⟨∅, mem_filter.2 ⟨mem_sensitiveFamilies.2 ⟨by simp, by simp⟩, by simp⟩⟩
  obtain ⟨hFs, hFmin⟩ := mem_filter.1 hF
  rw [mem_sensitiveFamilies] at hFs
  have hcert := isCertificate_biUnion_of_maximal hFs hFmin fun G hG hGmin =>
    hmax G (mem_filter.2 ⟨mem_sensitiveFamilies.2 hG, hGmin⟩)
  calc certificateComplexityAt f x ≤ #(F.biUnion id) := certificateComplexityAt_le hcert
    _ ≤ ∑ B ∈ F, #B := card_biUnion_le
    _ ≤ #F * sensitivity f :=
      sum_le_card_nsmul _ _ _ fun B hB => (hFmin B hB).card_le_sensitivity
    _ ≤ sensitivity f * blockSensitivityAt f x := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left _ (card_le_blockSensitivityAt hFs)

/-- **Nisan's bound**: `C(f) ≤ s(f) bs(f)`. -/
theorem certificateComplexity_le_sensitivity_mul_blockSensitivity (f : BooleanFunction n) :
    certificateComplexity f ≤ sensitivity f * blockSensitivity f :=
  Finset.sup_le fun x _ => (certificateComplexityAt_le_sensitivity_mul_blockSensitivityAt f x).trans
    (Nat.mul_le_mul_left _ (blockSensitivityAt_le_blockSensitivity f x))

/-- `C(f) ≤ bs(f)²`. -/
theorem certificateComplexity_le_blockSensitivity_sq (f : BooleanFunction n) :
    certificateComplexity f ≤ blockSensitivity f ^ 2 :=
  (certificateComplexity_le_sensitivity_mul_blockSensitivity f).trans (by
    rw [sq]
    exact Nat.mul_le_mul_right _ (sensitivity_le_blockSensitivity f))

/-! ### Block sensitivity for a value -/

/-- `bs_b(f)`: the largest block sensitivity of `f` at an input where it has value `b`. -/
def blockSensitivityFor (f : BooleanFunction n) (b : Bool) : ℕ :=
  (univ.filter fun x => f x = b).sup (blockSensitivityAt f)

theorem blockSensitivityAt_le_blockSensitivityFor {b : Bool} (h : f x = b) :
    blockSensitivityAt f x ≤ blockSensitivityFor f b :=
  le_sup (f := blockSensitivityAt f) (mem_filter.2 ⟨mem_univ x, h⟩)

theorem blockSensitivityFor_le_blockSensitivity (f : BooleanFunction n) (b : Bool) :
    blockSensitivityFor f b ≤ blockSensitivity f :=
  sup_mono (filter_subset _ _)

/-! ### Restricting by the answers to a certificate -/

/-- Restricting by answers on `S` does not raise `C_b(f)`. -/
theorem certificateComplexityFor_comp_piecewise_le (f : BooleanFunction n) (S : Finset (Fin n))
    (a : BitString n) (b : Bool) :
    certificateComplexityFor (fun y => f (S.piecewise a y)) b ≤ certificateComplexityFor f b :=
  Finset.sup_le fun z hz => by
    obtain ⟨T, hT, hcard⟩ := exists_isCertificate_card_eq f (S.piecewise a z)
    exact (certificateComplexityAt_le hT.restrict).trans ((card_le_card sdiff_subset).trans
      (hcard.trans_le (certificateComplexityAt_le_certificateComplexityFor (mem_filter.1 hz).2)))

/-- Flipping a block in the free coordinates commutes with filling in `S`. -/
private theorem piecewise_flipBlock (S B : Finset (Fin n)) (a z : BitString n) :
    S.piecewise a (flipBlock B z) = flipBlock (B \ S) (S.piecewise a z) := by
  funext i
  by_cases hiS : i ∈ S
  · simp [hiS]
  · by_cases hiB : i ∈ B <;> simp [hiS, hiB]

/-- After restricting by the answers `a` to a certificate `S` of an input `w` of value `1`, every
input `z` of value `0` has one sensitive block fewer than the filled input in the original
function: the coordinates of `S` on which the filled input differs from `w`. -/
theorem blockSensitivityAt_comp_piecewise_add_one_le {w : BitString n} {S : Finset (Fin n)}
    (hS : IsCertificate f w S) (hw : f w = true) (a z : BitString n)
    (hz : f (S.piecewise a z) = false) :
    blockSensitivityAt (fun y => f (S.piecewise a y)) z + 1 ≤
      blockSensitivityAt f (S.piecewise a z) := by
  obtain ⟨F, hF, hFcard⟩ := exists_mem_eq_sup (sensitiveFamilies (fun y => f (S.piecewise a y)) z)
    ⟨∅, mem_sensitiveFamilies.2 ⟨by simp, by simp⟩⟩ card
  rw [mem_sensitiveFamilies] at hF
  -- the blocks of `F` keep their free coordinates
  have hsens (B : Block n) (hB : B ∈ F) : IsSensitiveBlock f (S.piecewise a z) (B \ S) := by
    have : f (S.piecewise a (flipBlock B z)) ≠ f (S.piecewise a z) := hF.1 B hB
    rwa [piecewise_flipBlock] at this
  have hfree (B : Block n) (hB : B ∈ F) : (B \ S).Nonempty := (hsens B hB).nonempty
  have hinj : Set.InjOn (· \ S) (F : Set (Block n)) := fun B₁ hB₁ B₂ hB₂ h => by
    by_contra hne
    obtain ⟨i, hi⟩ := hfree B₁ hB₁
    have hi' : i ∈ B₂ \ S := by
      change B₁ \ S = B₂ \ S at h
      rwa [← h]
    exact disjoint_left.1 (hF.2 hB₁ hB₂ hne) (mem_sdiff.1 hi).1 (mem_sdiff.1 hi').1
  -- the coordinates of `S` where the filled input differs from `w`
  set x' := S.piecewise a z
  set B₀ : Block n := {i ∈ S | x' i ≠ w i}
  have hB₀ : IsSensitiveBlock f x' B₀ := by
    rw [IsSensitiveBlock, hS _ fun i hi => ?_, hw, hz]
    · decide
    by_cases h : x' i = w i
    · rw [flipBlock_apply_of_notMem (by simp [B₀, h]), h]
    · rw [flipBlock_apply_of_mem (by simp [B₀, hi, h])]
      cases hx : x' i <;> cases hw' : w i <;> simp_all
  have hB₀F : B₀ ∉ F.image (· \ S) := fun h => by
    obtain ⟨B, hB, hBeq⟩ := mem_image.1 h
    obtain ⟨i, hi⟩ := hfree B hB
    have hi₀ : i ∈ B₀ := by
      rw [← show B \ S = B₀ from hBeq]
      exact hi
    exact (mem_sdiff.1 hi).2 (mem_filter.1 hi₀).1
  have hG : IsSensitiveFamily f x' (insert B₀ (F.image (· \ S))) := by
    refine ⟨fun B hB => ?_, ?_⟩
    · rcases mem_insert.1 hB with rfl | hB
      · exact hB₀
      · obtain ⟨B', hB', rfl⟩ := mem_image.1 hB
        exact hsens B' hB'
    · rw [coe_insert, coe_image]
      refine (hF.2.image_of_le fun B => show B \ S ≤ B from sdiff_subset).insert
        fun B hB _ => ?_
      obtain ⟨B', -, rfl⟩ := hB
      exact disjoint_left.2 fun i hi hi' => (mem_sdiff.1 hi').2 (mem_filter.1 hi).1
  have := card_le_blockSensitivityAt hG
  rwa [card_insert_of_notMem hB₀F, card_image_of_injOn hinj, ← hFcard] at this

/-- Restricting by the answers to a certificate of an input of value `1` lowers `bs₀(f)`. -/
theorem blockSensitivityFor_comp_piecewise_false_le {w : BitString n} {S : Finset (Fin n)}
    (hS : IsCertificate f w S) (hw : f w = true) (a : BitString n) {m : ℕ}
    (hm : blockSensitivityFor f false ≤ m + 1) :
    blockSensitivityFor (fun y => f (S.piecewise a y)) false ≤ m :=
  Finset.sup_le fun z hz => by
    have hz : f (S.piecewise a z) = false := (mem_filter.1 hz).2
    have := (blockSensitivityAt_comp_piecewise_add_one_le hS hw a z hz).trans
      ((blockSensitivityAt_le_blockSensitivityFor hz).trans hm)
    omega

end QueryComplexity

namespace DecisionTree

open QueryComplexity

/-- **Decision tree complexity from block sensitivity and certificates**: `D(f) ≤ bs₀(f) C₁(f)`, a
one-sided form of the bound `D(f) ≤ C₁(f) bs(f)` of Beals, Buhrman, Cleve, Mosca and de Wolf
[BealsBuhrmanCleveMoscaDeWolf2001]. -/
theorem complexity_le_blockSensitivityFor_mul_certificateComplexityFor (f : BooleanFunction n) :
    complexity f ≤ blockSensitivityFor f false * certificateComplexityFor f true := by
  suffices ∀ m (f : BooleanFunction n), blockSensitivityFor f false ≤ m →
      complexity f ≤ m * certificateComplexityFor f true from this _ f le_rfl
  intro m
  induction m with
  | zero =>
    intro f hf
    refine (complexity_eq_zero_iff.2 fun x y => ?_).trans_le (Nat.zero_le _)
    -- with `bs₀(f) = 0`, no block is sensitive at an input of value `0`
    by_contra hxy
    wlog hx : f x = false generalizing x y
    · exact this y x (Ne.symm hxy) (by simpa [hx] using hxy)
    have hB : IsSensitiveBlock f x ({i | y i ≠ x i} : Finset (Fin n)) := by
      rw [IsSensitiveBlock, flipBlock_filter_ne]
      exact Ne.symm hxy
    have h1 := card_le_blockSensitivityAt (F := {({i | y i ≠ x i} : Finset (Fin n))})
      ⟨fun B hB' => by rw [mem_singleton.1 hB']; exact hB, by simp⟩
    rw [card_singleton] at h1
    have := (blockSensitivityAt_le_blockSensitivityFor hx).trans hf
    omega
  | succ m ih =>
    intro f hf
    by_cases h1 : ∃ x, f x = true
    swap
    · push Not at h1
      exact (complexity_eq_zero_iff.2 fun x y => by simp [h1 x, h1 y]).trans_le (Nat.zero_le _)
    obtain ⟨w, hw⟩ := h1
    obtain ⟨S, hS, hScard⟩ := exists_isCertificate_card_eq f w
    -- query the certificate of `w`, then continue with a tree for the restricted function
    refine (complexity_le_card_add S (d := m * certificateComplexityFor f true) fun a =>
      (ih _ (blockSensitivityFor_comp_piecewise_false_le hS hw a hf)).trans
        (Nat.mul_le_mul_left m (certificateComplexityFor_comp_piecewise_le f S a true))).trans ?_
    rw [hScard, Nat.succ_mul, add_comm]
    exact Nat.add_le_add_left (certificateComplexityAt_le_certificateComplexityFor hw) _

/-- `D(f) ≤ C(f) bs(f)` [BealsBuhrmanCleveMoscaDeWolf2001]. -/
theorem complexity_le_certificateComplexity_mul_blockSensitivity (f : BooleanFunction n) :
    complexity f ≤ certificateComplexity f * blockSensitivity f :=
  (complexity_le_blockSensitivityFor_mul_certificateComplexityFor f).trans (by
    rw [mul_comm]
    exact Nat.mul_le_mul (certificateComplexityFor_le_certificateComplexity f true)
      (blockSensitivityFor_le_blockSensitivity f false))

/-- **Decision tree complexity is at most the cube of block sensitivity**: `D(f) ≤ bs(f)³`
[BealsBuhrmanCleveMoscaDeWolf2001]. -/
theorem complexity_le_blockSensitivity_pow_three (f : BooleanFunction n) :
    complexity f ≤ blockSensitivity f ^ 3 :=
  (complexity_le_certificateComplexity_mul_blockSensitivity f).trans (by
    rw [pow_succ]
    exact Nat.mul_le_mul_right _ (certificateComplexity_le_blockSensitivity_sq f))

end DecisionTree

end Cslib
