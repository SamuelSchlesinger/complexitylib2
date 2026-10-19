/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.BitString.AffineDisperser
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Affine dispersers from nonconstancy on affine subspaces

An affine disperser for dimension `d` (`Cslib.BitString.IsAffineDisperser`) is nonconstant on the
image of every injective map `g : BitString d → BitString n` that preserves sums of three points
(`Cslib.BitString.IsAffine`). Such an image is an affine subspace of dimension `d` in Mathlib's
sense over `𝔽₂ = Bool`: `g` is a Mathlib affine map with linear part `x ↦ g x + g 0`
(`Cslib.BitString.IsAffine.toAffineMap`), the image is the affine subspace `⊤.map g`, and its
direction, the range of the injective linear part, has dimension `d`
(`Cslib.BitString.IsAffine.finrank_direction_map_top`).

Hence a function nonconstant on every affine subspace of dimension `d` is an affine disperser for
dimension `d` (`Cslib.BitString.isAffineDisperser_of_forall_exists_ne`). This turns nonconstancy
theorems stated with `AffineSubspace`, such as Ben-Sasson and Kopparty's, into affine dispersers.
The converse, that every affine subspace of dimension `d` contains such an image, is not
formalized here: Mathlib has no `Field Bool` instance, so a basis of the direction is not
available over `Bool`.

## Main definitions

* `Cslib.BitString.IsAffine.linearMap`: the linear part `x ↦ g x + g 0` of an affine map over
  `𝔽₂`.
* `Cslib.BitString.IsAffine.toAffineMap`: an affine map over `𝔽₂` as a Mathlib affine map.

## Main results

* `Cslib.BitString.IsAffine.finrank_direction_map_top`: the image of an injective affine map
  from `V` is an affine subspace whose direction has dimension `finrank Bool V`.
* `Cslib.BitString.isAffineDisperser_of_forall_exists_ne`: a function nonconstant on every affine
  subspace of dimension `d` is an affine disperser for dimension `d`.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*, Definition 2.1][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.BitString

open Module

variable {V W : Type*} [AddCommGroup V] [Module Bool V] [AddCommGroup W] [Module Bool W]

/-- In a vector space over `𝔽₂ = Bool` every vector is its own negative. -/
private theorem add_self_eq_zero_of_module_bool (w : W) : w + w = 0 := by
  rw [← one_smul Bool w, ← add_smul, show (1 + 1 : Bool) = 0 from rfl, zero_smul]

/-- The linear part `x ↦ g x + g 0` of a map `g` that is affine over `𝔽₂`. -/
def IsAffine.linearMap {g : V → W} (hg : IsAffine g) : V →ₗ[Bool] W where
  toFun x := g x + g 0
  map_add' x y := by
    have h := hg x y 0
    rw [add_zero] at h
    rw [h]
    abel
  map_smul' c x := by
    cases c
    · change g ((0 : Bool) • x) + g 0 = (0 : Bool) • (g x + g 0)
      rw [zero_smul, zero_smul, add_self_eq_zero_of_module_bool]
    · change g ((1 : Bool) • x) + g 0 = (1 : Bool) • (g x + g 0)
      rw [one_smul, one_smul]

@[simp]
theorem IsAffine.linearMap_apply {g : V → W} (hg : IsAffine g) (x : V) :
    hg.linearMap x = g x + g 0 :=
  rfl

theorem IsAffine.linearMap_injective {g : V → W} (hg : IsAffine g)
    (hinj : Function.Injective g) : Function.Injective hg.linearMap := fun x y h => by
  rw [hg.linearMap_apply, hg.linearMap_apply, add_left_inj] at h
  exact hinj h

/-- A map that is affine over `𝔽₂` (`IsAffine`) as a Mathlib affine map over `Bool`, with linear
part `x ↦ g x + g 0`. -/
def IsAffine.toAffineMap {g : V → W} (hg : IsAffine g) : V →ᵃ[Bool] W where
  toFun := g
  linear := hg.linearMap
  map_vadd' p v := by
    have h := hg v p 0
    rw [add_zero] at h
    rw [vadd_eq_add, vadd_eq_add, h, hg.linearMap_apply]
    abel

@[simp]
theorem IsAffine.coe_toAffineMap {g : V → W} (hg : IsAffine g) : ⇑hg.toAffineMap = g :=
  rfl

/-- The image of an injective map from `V` that is affine over `𝔽₂` is an affine subspace whose
direction has the dimension of `V`. -/
theorem IsAffine.finrank_direction_map_top {g : V → W} (hg : IsAffine g)
    (hinj : Function.Injective g) :
    finrank Bool ((⊤ : AffineSubspace Bool V).map hg.toAffineMap).direction = finrank Bool V := by
  rw [AffineSubspace.map_direction, AffineSubspace.direction_top, Submodule.map_top]
  exact LinearMap.finrank_range_of_inj (hg.linearMap_injective hinj)

/-- A function nonconstant on every affine subspace of `BitString n` of dimension `d` is an affine
disperser for dimension `d`: the image of an injective affine map from `BitString d` is such a
subspace. -/
theorem isAffineDisperser_of_forall_exists_ne {n d : ℕ} {f : BitString n → Bool}
    (h : ∀ A : AffineSubspace Bool (BitString n), finrank Bool A.direction = d →
      ∃ x ∈ A, ∃ y ∈ A, f x ≠ f y) :
    IsAffineDisperser f d := by
  intro g hg hinj
  obtain ⟨_, hx, _, hy, hne⟩ := h _
    ((hg.finrank_direction_map_top hinj).trans (Module.finrank_fin_fun Bool))
  obtain ⟨x, -, rfl⟩ := AffineSubspace.mem_map.1 hx
  obtain ⟨y, -, rfl⟩ := AffineSubspace.mem_map.1 hy
  exact ⟨x, y, hne⟩

end Cslib.BitString
