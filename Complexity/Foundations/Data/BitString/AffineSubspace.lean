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
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Option
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Affine maps and affine subspaces over `𝔽₂`

Over `𝔽₂`, a map between additive groups is *affine* when it preserves sums of three points:
`g (x + y + z) = g x + g y + g z` (`Cslib.BitString.IsAffine`). For maps between `𝔽₂`-vector
spaces this is the usual notion (`Cslib.BitString.isAffine_iff_exists_affineMap`): `g` is a Mathlib
affine map over `Bool` with linear part `x ↦ g x + g 0` (`Cslib.BitString.IsAffine.linearMap`,
`Cslib.BitString.IsAffine.toAffineMap`). The image of an injective affine map from `V` is an
affine subspace whose direction has the dimension of `V`
(`Cslib.BitString.IsAffine.finrank_direction_map_top`).

An affine map from `BitString d` is determined by its values at `0` and at the unit vectors
(`Cslib.BitString.IsAffine.ext_single`), so there are at most `2 ^ (n (d + 1))` affine maps from
`BitString d` to `BitString n` (`Cslib.BitString.card_isAffine_le`).

## Main definitions

* `Cslib.BitString.IsAffine`: affine maps over `𝔽₂`.
* `Cslib.BitString.zeroExtend`: extension of a bit string by zeros to a longer length.
* `Cslib.BitString.IsAffine.linearMap`: the linear part `x ↦ g x + g 0` of an affine map over
  `𝔽₂`.
* `Cslib.BitString.IsAffine.toAffineMap`: an affine map over `𝔽₂` as a Mathlib affine map.

## Main results

* `Cslib.BitString.IsAffine.comp`: affine maps compose.
* `Cslib.BitString.IsAffine.ext_single`: an affine map from `BitString d` is determined by its
  values at `0` and at the unit vectors.
* `Cslib.BitString.card_isAffine_le`: at most `2 ^ (n (d + 1))` maps from `BitString d` to
  `BitString n` are affine.
* `Cslib.BitString.isAffine_iff_exists_affineMap`: a map between `𝔽₂`-vector spaces is `IsAffine`
  if and only if it is a Mathlib affine map over `Bool`.
* `Cslib.BitString.IsAffine.finrank_direction_map_top`: the image of an injective affine map
  from `V` is an affine subspace whose direction has dimension `finrank Bool V`.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*, Definition 2.1][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.BitString

/-- A map is affine over `𝔽₂` when it preserves sums of three points. -/
def IsAffine {α β : Type*} [Add α] [Add β] (g : α → β) : Prop :=
  ∀ x y z, g (x + y + z) = g x + g y + g z

/-- The composition of affine maps is affine. -/
theorem IsAffine.comp {α β γ : Type*} [Add α] [Add β] [Add γ] {g : β → γ} {h : α → β}
    (hg : IsAffine g) (hh : IsAffine h) : IsAffine (g ∘ h) := fun x y z => by
  simp only [Function.comp_apply, hh x y z, hg (h x) (h y) (h z)]

/-- Constant maps into a group in which every element is its own negative (`b + b = 0`) are
affine. -/
theorem isAffine_const {α β : Type*} [Add α] [AddGroup β] (h : ∀ b : β, b + b = 0) (c : β) :
    IsAffine (fun _ : α => c) := fun _ _ _ => by rw [h, zero_add]

/-- The extension of a point of `BitString d` by zeros to `BitString d'`, for `d ≤ d'`. -/
def zeroExtend {d d' : ℕ} (x : BitString d) : BitString d' :=
  fun i => if h : i.val < d then x ⟨i.val, h⟩ else false

/-- Extension by zeros is affine. -/
theorem isAffine_zeroExtend {d d' : ℕ} : IsAffine (zeroExtend (d := d) (d' := d')) := by
  intro x y z
  funext i
  simp only [zeroExtend, Pi.add_apply]
  split_ifs <;> rfl

/-- Extension by zeros from `BitString d` to `BitString d'` is injective when `d ≤ d'`. -/
theorem zeroExtend_injective {d d' : ℕ} (h : d ≤ d') :
    Function.Injective (zeroExtend (d := d) (d' := d')) := by
  intro x y hxy
  funext i
  have := congrFun hxy ⟨i.val, by omega⟩
  simpa [zeroExtend, i.isLt] using this

/-! ### Counting affine maps -/

section Counting

open Finset

/-- Affinity of a map between finite types is decidable. -/
instance {α β : Type*} [Fintype α] [DecidableEq β] [Add α] [Add β] (g : α → β) :
    Decidable (IsAffine g) :=
  inferInstanceAs (Decidable (∀ _ _ _, _))

/-- Affine maps from `BitString d` agreeing at `0` and at the unit vectors are equal. -/
theorem IsAffine.ext_single {d n : ℕ} {g g' : BitString d → BitString n} (hg : IsAffine g)
    (hg' : IsAffine g') (h0 : g 0 = g' 0) (hi : ∀ i, g (Pi.single i true) = g' (Pi.single i true)) :
    g = g' := by
  have key : ∀ s : Finset (Fin d), g (fun i => decide (i ∈ s)) = g' (fun i => decide (i ∈ s)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : (fun i : Fin d => decide (i ∈ (∅ : Finset (Fin d)))) = 0 := by
        funext i; simp [Bool.zero_eq_false]
      rw [this, h0]
    | insert j s hj ih =>
      have hsplit : (fun i => decide (i ∈ insert j s)) =
          (fun i => decide (i ∈ s)) + Pi.single j true + 0 := by
        funext i
        by_cases hij : i = j
        · subst hij
          simp only [Finset.mem_insert, true_or, decide_true, hj, decide_false, Pi.single_eq_same,
            Pi.add_apply, Pi.zero_apply, Bool.zero_eq_false]
          rfl
        · simp only [Finset.mem_insert, hij, false_or, Pi.add_apply, Pi.single_eq_of_ne hij,
            Pi.zero_apply, Bool.zero_eq_false]
          cases decide (i ∈ s) <;> rfl
      rw [hsplit, hg, hg', ih, hi, h0]
  funext x
  have hx : x = fun i => decide (i ∈ Finset.univ.filter fun i => x i = true) := by
    funext i; simp
  rw [hx, key]

/-- At most `2 ^ (n (d + 1))` maps from `BitString d` to `BitString n` are affine. -/
theorem card_isAffine_le (d n : ℕ) :
    (univ.filter fun g : BitString d → BitString n => IsAffine g).card ≤ 2 ^ (n * (d + 1)) := by
  classical
  calc _ ≤ (univ : Finset (Option (Fin d) → BitString n)).card :=
        card_le_card_of_injOn (fun g o => g (o.elim 0 fun i => Pi.single i true))
          (fun _ _ => mem_univ _) fun g hg g' hg' h =>
            IsAffine.ext_single (mem_filter.1 hg).2 (mem_filter.1 hg').2 (congrFun h none)
              fun i => congrFun h (some i)
    _ = 2 ^ (n * (d + 1)) := by
      rw [card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_option, Fintype.card_fin,
        Fintype.card_bool, Fintype.card_fin, ← pow_mul]

end Counting

/-! ### Bridge to Mathlib affine maps and subspaces -/

section AffineSubspace

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

/-- The linear part of `g` sends `x` to `g x + g 0`. -/
@[simp]
theorem IsAffine.linearMap_apply {g : V → W} (hg : IsAffine g) (x : V) :
    hg.linearMap x = g x + g 0 :=
  rfl

/-- The linear part of an injective map that is affine over `𝔽₂` is injective. -/
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

/-- As a function, the Mathlib affine map of `g` is `g` itself. -/
@[simp]
theorem IsAffine.coe_toAffineMap {g : V → W} (hg : IsAffine g) : ⇑hg.toAffineMap = g :=
  rfl

/-- A map between `𝔽₂`-vector spaces is affine (`IsAffine`) if and only if it is a Mathlib
affine map over `Bool`. -/
theorem isAffine_iff_exists_affineMap {g : V → W} :
    IsAffine g ↔ ∃ f : V →ᵃ[Bool] W, ⇑f = g := by
  refine ⟨fun hg => ⟨hg.toAffineMap, rfl⟩, ?_⟩
  rintro ⟨f, rfl⟩ x y z
  have hv (v p : V) : f (v + p) = f.linear v + f p := by
    simpa only [vadd_eq_add] using f.map_vadd p v
  have h0 (v : V) : f v = f.linear v + f 0 := by
    simpa only [add_zero] using hv v 0
  calc f (x + y + z)
      = f.linear x + f.linear y + f z + (f 0 + f 0) := by
        rw [hv (x + y) z, f.linear.map_add, add_self_eq_zero_of_module_bool, add_zero]
    _ = (f.linear x + f 0) + (f.linear y + f 0) + f z := by abel
    _ = f x + f y + f z := by rw [← h0 x, ← h0 y]

/-- The image of an injective map from `V` that is affine over `𝔽₂` is an affine subspace whose
direction has the dimension of `V`. -/
theorem IsAffine.finrank_direction_map_top {g : V → W} (hg : IsAffine g)
    (hinj : Function.Injective g) :
    finrank Bool ((⊤ : AffineSubspace Bool V).map hg.toAffineMap).direction = finrank Bool V := by
  rw [AffineSubspace.map_direction, AffineSubspace.direction_top, Submodule.map_top]
  exact LinearMap.finrank_range_of_inj (hg.linearMap_injective hinj)

end AffineSubspace

end Cslib.BitString
