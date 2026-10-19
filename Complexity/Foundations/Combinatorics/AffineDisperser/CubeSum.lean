/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.Data.ZMod.Basic
import Mathlib

/-!
# Sums of products of affine forms over the Boolean cube

Let `R` be a commutative `𝔽₂`-algebra. For affine forms `Lₚ(c) = aₚ + ∑ᵥ cᵥ • bₚᵥ` in Boolean
variables `c : κ → 𝔽₂`, the sum of `∏ₚ Lₚ(c)` over the whole cube is the `|κ|`-th mixed finite
difference of the product. Expanding the product, a monomial survives the summation exactly when
it involves every variable, since a missing variable doubles its contribution. Hence the sum is
a sum over the assignments `ℓ : P → Option κ` of factors to variables (or to their constant term)
that cover every variable.

Two consequences are used for affine dispersers. If every covering assignment meets a vanishing
coefficient, the sum is zero. If there are as many factors as variables, the covering
assignments are the bijections, and the sum is the permanent of the coefficient matrix.

## Main results

* `Cslib.sum_cube_prod_affine`: the expansion over covering assignments.
* `Cslib.sum_cube_prod_affine_eq_zero`: vanishing when every covering assignment meets a zero
  coefficient.
* `Cslib.sum_cube_prod_affine_eq_permanent`: with as many factors as variables, the sum is the
  permanent of the coefficient matrix.

## References

* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
-/

@[expose] public section

namespace Cslib

variable {R : Type*} [CommRing R] [Algebra (ZMod 2) R] {κ P : Type*} [Fintype κ] [DecidableEq κ]
  [Fintype P]

/-- **Cube sum of a product of affine forms**: summing `∏ₚ (aₚ + ∑ᵥ cᵥ • bₚᵥ)` over the Boolean
cube leaves the assignments `ℓ` of factors to variables, or to the constant term (`none`), that
cover every variable; each contributes the product of the chosen coefficients. -/
theorem sum_cube_prod_affine [DecidableEq P] (a : P → R) (b : P → κ → R) :
    ∑ c : κ → ZMod 2, ∏ p, (a p + ∑ v, c v • b p v) =
      ∑ ℓ ∈ Finset.univ.filter (fun ℓ : P → Option κ => ∀ v, ∃ p, ℓ p = some v),
        ∏ p, (ℓ p).elim (a p) (b p) := by
  sorry

/-- If every assignment covering all variables uses a vanishing coefficient, the cube sum of the
product of affine forms is zero. -/
theorem sum_cube_prod_affine_eq_zero (a : P → R) (b : P → κ → R)
    (h : ∀ ℓ : P → Option κ, (∀ v, ∃ p, ℓ p = some v) → ∃ p v, ℓ p = some v ∧ b p v = 0) :
    ∑ c : κ → ZMod 2, ∏ p, (a p + ∑ v, c v • b p v) = 0 := by
  sorry

/-- With as many affine factors as Boolean variables, the cube sum of their product is the
permanent of the matrix of linear coefficients: the constant terms do not contribute. -/
theorem sum_cube_prod_affine_eq_permanent (a : κ → R) (b : κ → κ → R) :
    ∑ c : κ → ZMod 2, ∏ p, (a p + ∑ v, c v • b p v) = (Matrix.of b).permanent := by
  sorry

end Cslib
