/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Foundations.Data.BitString
public import Mathlib.Algebra.Ring.BooleanRing

/-!
# Affine dispersers

Over `𝔽₂`, a map between additive groups is *affine* when it preserves sums of three points:
`g (x + y + z) = g x + g y + g z` (`Cslib.BitString.IsAffine`). For maps between `𝔽₂`-vector
spaces this is exactly the usual notion, a translate of a linear map, since `b + b + b = b`.
The affine subspaces of dimension `d` of the cube `BitString n` are exactly the images of the
injective affine maps from `BitString d`.

A Boolean function `f` on `n` bits is an *affine disperser for dimension `d`* when it is
nonconstant on every affine subspace of dimension `d`
(`Cslib.BitString.IsAffineDisperser`): composed with any injective affine map from
`BitString d`, it takes both values. Dispersers for dimension `d` are dispersers for every larger
dimension (`IsAffineDisperser.mono`), and no function is a disperser for dimension `0`
(`not_isAffineDisperser_zero`).

## Main definitions

* `Cslib.BitString.IsAffine`: affine maps over `𝔽₂`.
* `Cslib.BitString.IsAffineDisperser`: affine dispersers.

## Main results

* `Cslib.BitString.IsAffine.comp`: affine maps compose.
* `Cslib.BitString.IsAffineDisperser.mono`: dispersers for smaller dimension are dispersers for
  larger dimension.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*, Definition 2.1][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.BitString

/-- A map is affine over `𝔽₂` when it preserves sums of three points. -/
def IsAffine {α β : Type*} [Add α] [Add β] (g : α → β) : Prop :=
  ∀ x y z, g (x + y + z) = g x + g y + g z

theorem IsAffine.comp {α β γ : Type*} [Add α] [Add β] [Add γ] {g : β → γ} {h : α → β}
    (hg : IsAffine g) (hh : IsAffine h) : IsAffine (g ∘ h) := fun x y z => by
  simp only [Function.comp_apply, hh x y z, hg (h x) (h y) (h z)]

theorem isAffine_const {α β : Type*} [Add α] [AddGroup β] (h : ∀ b : β, b + b = 0) (c : β) :
    IsAffine (fun _ : α => c) := fun _ _ _ => by rw [h, zero_add]

/-- `f` is an affine disperser for dimension `d`: it is nonconstant on the image of every
injective affine map from `BitString d`, that is, on every affine subspace of dimension `d`. -/
def IsAffineDisperser {n : ℕ} (f : BitString n → Bool) (d : ℕ) : Prop :=
  ∀ g : BitString d → BitString n, IsAffine g → Function.Injective g → ∃ x y, f (g x) ≠ f (g y)

/-- The extension of a point of `BitString d` by zeros to `BitString d'`, for `d ≤ d'`. -/
def zeroExtend {d d' : ℕ} (x : BitString d) : BitString d' :=
  fun i => if h : i.val < d then x ⟨i.val, h⟩ else false

theorem isAffine_zeroExtend {d d' : ℕ} : IsAffine (zeroExtend (d := d) (d' := d')) := by
  intro x y z
  funext i
  simp only [zeroExtend, Pi.add_apply]
  split_ifs <;> rfl

theorem zeroExtend_injective {d d' : ℕ} (h : d ≤ d') :
    Function.Injective (zeroExtend (d := d) (d' := d')) := by
  intro x y hxy
  funext i
  have := congrFun hxy ⟨i.val, by omega⟩
  simpa [zeroExtend, i.isLt] using this

/-- Dispersers for dimension `d` are dispersers for every larger dimension. -/
theorem IsAffineDisperser.mono {n d d' : ℕ} {f : BitString n → Bool}
    (hf : IsAffineDisperser f d) (h : d ≤ d') : IsAffineDisperser f d' := by
  intro g hg hinj
  obtain ⟨x, y, hxy⟩ := hf (g ∘ zeroExtend) (hg.comp isAffine_zeroExtend)
    (hinj.comp (zeroExtend_injective h))
  exact ⟨_, _, hxy⟩

/-- No function is an affine disperser for dimension `0`: it is constant on every point. -/
theorem not_isAffineDisperser_zero {n : ℕ} (f : BitString n → Bool) :
    ¬ IsAffineDisperser f 0 := by
  intro hf
  obtain ⟨x, y, hxy⟩ := hf (fun _ => 0) (isAffine_const (β := BitString n)
    (fun b => funext fun i => BooleanRing.add_self (b i)) 0)
    (fun x y _ => Subsingleton.elim x y)
  exact hxy rfl

end Cslib.BitString
