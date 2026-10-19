/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.AffineDisperser.CubeSum
public import Complexity.Foundations.Combinatorics.AffineDisperser.SubspacePolynomial
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib

/-!
# Moore determinants in characteristic two

The *Moore matrix* of `u : Fin k → F` is `(u l ^ 2 ^ m)_{l, m}`; its determinant is the Moore
determinant of `u` over `𝔽₂`. In characteristic two determinants and permanents agree.

The Moore determinant is the `k`-th finite difference of `x ↦ x ^ (2 ^ k - 1)`: since
`x ^ (2 ^ k - 1) = ∏_{m < k} x ^ 2 ^ m` is a product of `k` additive functions,
`∑_{c ∈ 𝔽₂ᵏ} (a + ∑ cₗ uₗ) ^ (2 ^ k - 1) = det (u l ^ 2 ^ m)` for every base point `a`.

For a linearized function `Q x = ∑_{j ∈ ℤ/n} a j * x ^ 2 ^ j` on a field with `2 ^ n` elements,
the Moore permanent of `Q ∘ w` expands in the monomials `∏ₗ wₗ ^ 2 ^ τₗ`, `τ : Fin k → ℤ/n`,
with coefficient the permanent of `(a (τ l - m) ^ 2 ^ m)_{l, m}`
[BenSassonKopparty2012, Lemma 3.13].

## Main definitions

* `Cslib.FiniteField.mooreMatrix`: the matrix `(u l ^ 2 ^ m)`.

## Main results

* `Cslib.FiniteField.det_eq_permanent`: determinant and permanent agree in characteristic two.
* `Cslib.FiniteField.sum_cube_pow_eq_det_mooreMatrix`: the Moore determinant as a finite
  difference.
* `Cslib.FiniteField.permanent_mooreMatrix_linearizedEval`: the monomial expansion of the Moore
  permanent of a composition with a linearized function.

## References

* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
-/

@[expose] public section

namespace Cslib.FiniteField

open Module

variable {F : Type*} [Field F]

/-- The Moore matrix `(u l ^ 2 ^ m)_{l, m}` of a family `u : Fin k → F`. -/
def mooreMatrix {k : ℕ} (u : Fin k → F) : Matrix (Fin k) (Fin k) F :=
  Matrix.of fun l m => u l ^ 2 ^ (m : ℕ)

@[simp]
theorem mooreMatrix_apply {k : ℕ} (u : Fin k → F) (l m : Fin k) :
    mooreMatrix u l m = u l ^ 2 ^ (m : ℕ) :=
  rfl

/-- In characteristic two the determinant of a matrix is its permanent. -/
theorem det_eq_permanent {R ι : Type*} [CommRing R] [CharP R 2] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) : M.det = M.permanent := by
  sorry

variable [Algebra (ZMod 2) F]

/-- **The Moore determinant is a finite difference**: for every base point `a`,
`∑_{c ∈ 𝔽₂ᵏ} (a + ∑ cₗ uₗ) ^ (2 ^ k - 1)` is the Moore determinant of `u`. -/
theorem sum_cube_pow_eq_det_mooreMatrix {k : ℕ} (a : F) (u : Fin k → F) :
    ∑ c : Fin k → ZMod 2, (a + ∑ l, c l • u l) ^ (2 ^ k - 1) = (mooreMatrix u).det := by
  sorry

/-- **Monomial expansion of a Moore permanent** [BenSassonKopparty2012, Lemma 3.13]: for the
linearized function `Q = linearizedEval a` on a field with `2 ^ n` elements,
`per (Q (w l) ^ 2 ^ m) = ∑_τ per (a (τ l - m) ^ 2 ^ m) * ∏ₗ w l ^ 2 ^ τ l`, the sum ranging over
all `τ : Fin k → ZMod n`. -/
theorem permanent_mooreMatrix_linearizedEval [Finite F] {n : ℕ} [NeZero n]
    (hn : finrank (ZMod 2) F = n) (a : ZMod n → F) {k : ℕ} (w : Fin k → F) :
    (mooreMatrix fun l => linearizedEval a (w l)).permanent =
      ∑ τ : Fin k → ZMod n,
        (Matrix.of fun l m : Fin k => a (τ l - (m : ℕ)) ^ 2 ^ (m : ℕ)).permanent *
          ∏ l, w l ^ 2 ^ (τ l).val := by
  sorry

end Cslib.FiniteField
