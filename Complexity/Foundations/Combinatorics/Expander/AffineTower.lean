/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.AffinePlane
public import Complexity.Foundations.Combinatorics.Expander.Tower

/-!
# A zig-zag tower with an arithmetic base

Tensor two affine-plane graphs, then zig-zag twice with the same affine-plane graph. This gives
a graph on `|K|⁸` vertices of degree `|K|²`, with spectral expansion at most `3r + 2r²`, where
`r = sqrt (1 / |K|)`. For `|K| ≥ 256` the bound is at most `1 / 5`, as the existing zig-zag tower
requires. All rotations are computed by field arithmetic and graph combinators, without search
or a nonconstructive choice of a base graph. A concrete field is `ZMod 257`.

This is the affine-plane base construction of [Reingold, Vadhan and Wigderson,
Section 5.1][ReingoldVadhanWigderson2002], adapted to the simpler tower of their Section 1.2.
It supplies particular vertex counts; `AffineFamily` contracts this tower to arbitrary sizes.
Complete rotation tables have uniform polynomial-time certificates in
`Computability/Machines/Turing/MultiTape/Complexity/PolyTime/RotationMap/Tower`. Practically small
degree and time polynomial in the bit length of a vertex name remain separate targets.

## Main definitions

* `Cslib.RotationMap.AffinePlaneTowerBaseVertex`: the eight field coordinates of a vertex of the
  arithmetic base.
* `Cslib.RotationMap.affinePlaneTowerBase`: the arithmetic base on eight field coordinates.
* `Cslib.RotationMap.affinePlaneTowerBaseEquiv`: the regrouping of the base's coordinates into
  pairs of pairs of its edge labels.
* `Cslib.RotationMap.affinePlaneTower`: the tower built from it.

## Main results

* `Cslib.RotationMap.spectralExpansion_affinePlaneTowerBase_le_one_div_five`: the base meets
  the tower's spectral hypothesis whenever `|K| ≥ 256`.
* `Cslib.RotationMap.spectralExpansion_affinePlaneTower_le`: every tower graph has expansion
  at most `2 / 5` under that same condition.

## References

* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002]
-/

@[expose] public section

namespace Cslib.RotationMap

variable (K : Type*) [Field K]

/-- The eight coordinates of the arithmetic base, grouped as the graph products produce them. -/
abbrev AffinePlaneTowerBaseVertex : Type _ :=
  (((K × K) × (K × K)) × (K × K)) × (K × K)

/-- Tensor two affine planes and zig-zag twice, giving degree `|K|²` on `|K|⁸` vertices. -/
def affinePlaneTowerBase : RotationMap (AffinePlaneTowerBaseVertex K) (K × K) :=
  (((affinePlane K).tensor (affinePlane K)).zigzag (affinePlane K)).zigzag (affinePlane K)

/-- Regroup the base's coordinates into pairs of pairs of its edge labels. -/
def affinePlaneTowerBaseEquiv :
    AffinePlaneTowerBaseVertex K ≃ (Fin 2 → (K × K) × (K × K)) :=
  (Equiv.prodAssoc ((K × K) × (K × K)) (K × K) (K × K)).trans
    (finTwoArrowEquiv ((K × K) × (K × K))).symm

/-- The ordinary zig-zag tower with an arithmetic base instead of a chosen expander. -/
def affinePlaneTower (n : ℕ) :
    RotationMap (ZigzagTowerVertex (AffinePlaneTowerBaseVertex K) n) ((K × K) × (K × K)) :=
  zigzagTower (affinePlaneTowerBase K) (affinePlaneTowerBaseEquiv K) n

variable [Fintype K]

/-- The base's expansion is at most `3r + 2r²`, where `r = sqrt (1 / |K|)`. -/
theorem spectralExpansion_affinePlaneTowerBase_le :
    (affinePlaneTowerBase K).spectralExpansion ≤
      3 * Real.sqrt (1 / Fintype.card K) + 2 * Real.sqrt (1 / Fintype.card K) ^ 2 := by
  have ht := (affinePlane K).spectralExpansion_tensor_le (affinePlane K)
  rw [max_self] at ht
  have h₁ := ((affinePlane K).tensor (affinePlane K)).spectralExpansion_zigzag_le (affinePlane K)
  have h₂ := (((affinePlane K).tensor (affinePlane K)).zigzag
    (affinePlane K)).spectralExpansion_zigzag_le (affinePlane K)
  have hr := spectralExpansion_affinePlane_le K
  have hs := pow_le_pow_left₀ (affinePlane K).spectralExpansion_nonneg hr 2
  dsimp only [affinePlaneTowerBase]
  linarith

/-- A field with at least 256 elements gives a valid base for the existing zig-zag tower. -/
theorem spectralExpansion_affinePlaneTowerBase_le_one_div_five
    (hK : 256 ≤ Fintype.card K) : (affinePlaneTowerBase K).spectralExpansion ≤ 1 / 5 := by
  have hc : (256 : ℝ) ≤ Fintype.card K := by exact_mod_cast hK
  have hr : Real.sqrt (1 / Fintype.card K) ≤ (1 : ℝ) / 16 := by
    rw [Real.sqrt_le_left (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg (1 / Fintype.card K)) hr 2
  have h := spectralExpansion_affinePlaneTowerBase_le K
  nlinarith

omit [Field K] in
/-- The `(n + 1)`-st arithmetic tower graph has `|K|^(8(n + 1))` vertices. -/
theorem card_affinePlaneTowerVertex (n : ℕ) :
    Fintype.card (ZigzagTowerVertex (AffinePlaneTowerBaseVertex K) n) =
      Fintype.card K ^ (8 * (n + 1)) := by
  rw [card_zigzagTowerVertex]
  simp only [AffinePlaneTowerBaseVertex, Fintype.card_prod]
  ring

/-- Every graph of the arithmetic tower has spectral expansion at most `2 / 5`. -/
theorem spectralExpansion_affinePlaneTower_le (hK : 256 ≤ Fintype.card K) (n : ℕ) :
    (affinePlaneTower K n).spectralExpansion ≤ 2 / 5 :=
  spectralExpansion_zigzagTower_le_two_div_five _ _
    (spectralExpansion_affinePlaneTowerBase_le_one_div_five K hK) n

end Cslib.RotationMap
