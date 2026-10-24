/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Pi
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Logic.Equiv.Fintype

/-!
# `L^p` norms on finite types and the Boolean cube

The *`L^p` norm* of a real function `f` on a finite type `α`, for the uniform distribution,
is `‖f‖_p = (𝔼_x |f x| ^ p) ^ (1 / p)` (`BitString.lpNorm`) [O'Donnell, Section 1.3][ODonnell2014].
Its `p`-th power is the `p`-th absolute moment (`BitString.lpNorm_rpow`), and `‖f‖_2` is the square
root of the second moment (`BitString.lpNorm_two`). See
`Complexity.Foundations.BooleanAnalysis.Hypercontractivity.LpNormMeasure` for its agreement with
Mathlib's `MeasureTheory.lpNorm`.

The norm is invariant under equivalences (`BitString.lpNorm_equiv`) and on a product `α × β` it is
the iterated norm (`BitString.lpNorm_prod`). In particular, on the Boolean cube `ι → Bool` it does
not see how the coordinates are named (`BitString.lpNorm_comp_arrowCongr`), and on the cube over a
disjoint union `ι ⊕ κ` it is the norm, over the bits in `ι`, of the norms over the bits in `κ`
(`BitString.lpNorm_sumElim`): the `p`-th moment over the product of two cubes is the iterated
`p`-th moment. On a subsingleton type, such as the cube over no coordinates, it is the absolute
value (`BitString.lpNorm_subsingleton`, `BitString.lpNorm_of_isEmpty`).

## Main definitions

* `Cslib.BitString.lpNorm`: the `L^p` norm `‖f‖_p` of a real function on a finite type.

## Main results

* `Cslib.BitString.lpNorm_rpow`, `Cslib.BitString.lpNorm_two`: the `p`-th power of `‖f‖_p` is
  the `p`-th absolute moment, and `‖f‖_2` is the root mean square.
* `Cslib.BitString.lpNorm_equiv`, `Cslib.BitString.lpNorm_prod`: invariance under equivalence and
  iterated norm on a product.
* `Cslib.BitString.lpNorm_sumElim`: the norm over a disjoint union of coordinates is the
  iterated norm.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The **`L^p` norm** `‖f‖_p = (𝔼_x |f x| ^ p) ^ (1 / p)` of a real function on a finite type, for
the uniform distribution. -/
noncomputable def lpNorm (p : ℝ) (f : α → ℝ) : ℝ :=
  (𝔼 x, |f x| ^ p) ^ p⁻¹

/-- The `p`-th absolute moment is nonnegative. -/
theorem expect_abs_rpow_nonneg (p : ℝ) (f : α → ℝ) : 0 ≤ 𝔼 x, |f x| ^ p :=
  expect_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) p

/-- The `L^p` norm is nonnegative. -/
theorem lpNorm_nonneg (p : ℝ) (f : α → ℝ) : 0 ≤ lpNorm p f :=
  Real.rpow_nonneg (expect_abs_rpow_nonneg p f) _

/-- The `p`-th power of `‖f‖_p` is the `p`-th absolute moment. -/
theorem lpNorm_rpow {p : ℝ} (hp : p ≠ 0) (f : α → ℝ) :
    lpNorm p f ^ p = 𝔼 x, |f x| ^ p :=
  Real.rpow_inv_rpow (expect_abs_rpow_nonneg p f) hp

/-- `‖f‖_2` is the root mean square of `f`. -/
theorem lpNorm_two (f : α → ℝ) : lpNorm 2 f = √(𝔼 x, f x ^ 2) := by
  have h (x : α) : |f x| ^ (2 : ℝ) = f x ^ 2 := by
    rw [Real.rpow_two, sq_abs]
  simp only [lpNorm, h, Real.sqrt_eq_rpow, one_div]

/-- The square of `‖f‖_2` is the second moment of `f`. -/
theorem lpNorm_two_sq (f : α → ℝ) : lpNorm 2 f ^ 2 = 𝔼 x, f x ^ 2 := by
  rw [lpNorm_two, Real.sq_sqrt (expect_nonneg fun _ _ => sq_nonneg _)]

/-! ### Equivalences, products, and subsingletons -/

/-- An equivalence of finite domains preserves the `L^p` norm. -/
theorem lpNorm_equiv (e : α ≃ β) (p : ℝ) (f : β → ℝ) :
    lpNorm p (f ∘ e) = lpNorm p f := by
  rw [lpNorm, Fintype.expect_equiv e (fun x => |(f ∘ e) x| ^ p) (fun y => |f y| ^ p) fun _ => rfl,
    lpNorm]

/-- **The `L^p` norm on a product is the iterated norm**: the norm over `α` of the norms over
`β`. -/
theorem lpNorm_prod (p : ℝ) (f : α × β → ℝ) :
    lpNorm p f = lpNorm p fun a => lpNorm p fun b => f (a, b) := by
  by_cases hp : p = 0
  · simp [lpNorm, hp]
  · rw [lpNorm, Fintype.expect_prod_type, lpNorm]
    congr 1
    refine expect_congr rfl fun a _ => ?_
    rw [abs_of_nonneg (lpNorm_nonneg _ _), lpNorm_rpow hp]

/-- On a type with at most one element, the `L^p` norm at a point is the absolute value. -/
theorem lpNorm_subsingleton [Subsingleton α] {p : ℝ} (hp : p ≠ 0) (f : α → ℝ) (x : α) :
    lpNorm p f = |f x| := by
  have : Nonempty α := ⟨x⟩
  have h : (fun y : α => |f y| ^ p) = fun _ => |f x| ^ p :=
    funext fun y => by rw [Subsingleton.elim y x]
  rw [lpNorm, h, Fintype.expect_const, Real.rpow_rpow_inv (abs_nonneg _) hp]

/-! ### Renaming and splitting the coordinates -/

/-- Renaming the coordinates preserves the `L^p` norm. -/
theorem lpNorm_comp_arrowCongr (e : ι ≃ κ) (p : ℝ) (f : (κ → Bool) → ℝ) :
    lpNorm p (fun x : ι → Bool => f fun j => x (e.symm j)) = lpNorm p f :=
  lpNorm_equiv (e.arrowCongr (Equiv.refl Bool)) p f

/-- **The `L^p` norm over a disjoint union of coordinates is the iterated norm**: the norm over
the bits in `ι` of the norms over the bits in `κ`. -/
theorem lpNorm_sumElim (p : ℝ) (f : (ι ⊕ κ → Bool) → ℝ) :
    lpNorm p f = lpNorm p fun x₁ => lpNorm p fun x₂ => f (Sum.elim x₁ x₂) := by
  rw [← lpNorm_equiv (Equiv.sumArrowEquivProdArrow ι κ Bool).symm p f, lpNorm_prod]
  rfl

/-- On the cube over no coordinates, a single point, the `L^p` norm is the absolute value. -/
theorem lpNorm_of_isEmpty [IsEmpty ι] {p : ℝ} (hp : p ≠ 0) (f : (ι → Bool) → ℝ)
    (x : ι → Bool) : lpNorm p f = |f x| :=
  lpNorm_subsingleton hp f x

end Cslib.BitString
