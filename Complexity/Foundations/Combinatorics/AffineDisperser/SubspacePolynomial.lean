/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Data.ZMod.Basic
import Mathlib

/-!
# Linearized and subspace polynomials over fields of characteristic two

A polynomial over a field of characteristic two is *linearized* when every exponent occurring in it
is a power of two. Such a polynomial evaluates to an additive, hence `𝔽₂`-linear, function. The
*subspace polynomial* `∏_{c ∈ 𝔽₂ᵐ} (X - ∑ cₗ bₗ)` of a family `b` is linearized, monic of degree
`2 ^ m`, and its roots are the `𝔽₂`-span of `b` [Ore1933].

Over a finite field `F` with `2 ^ n` elements every `𝔽₂`-subspace `W` of dimension `d` is the image
of a monic linearized polynomial of degree `2 ^ (n - d)`, its *image-subspace polynomial*
[BenSassonKopparty2012, Lemma 3.7]. Writing that polynomial as `∑_{j ∈ ℤ/n} a j X ^ 2 ^ j`, the
coefficients vanish at the `d - 1` positions above the leading one; the *structural lemma*
[BenSassonKopparty2012, Lemma 3.10] says that, apart from this canonical run, no `d - 1`
consecutive coefficients vanish unless `W` lies in a multiple of a proper subfield. We record it
for subspaces of dimension larger than every proper subfield, which is how it is used for
composite-degree fields.

## Main definitions

* `Cslib.FiniteField.IsLinearized`: every exponent of a polynomial is a power of two.
* `Cslib.FiniteField.subspacePoly`: the subspace polynomial of a finite family.
* `Cslib.FiniteField.linearizedEval`: evaluation of a coefficient vector indexed by `ZMod n`.
* `Cslib.FiniteField.CoeffPattern`: the zero pattern of an image-subspace polynomial.

## Main results

* `Cslib.FiniteField.isLinearized_subspacePoly`, `Cslib.FiniteField.eval_subspacePoly_eq_zero_iff`:
  subspace polynomials are linearized and vanish exactly on the span.
* `Cslib.FiniteField.exists_isLinearized_range_eq`: the image-subspace polynomial.
* `Cslib.FiniteField.eq_zero_of_linearizedEval_eq_zero`: a nonzero linearized function of
  `2`-degree below `m` has fewer than `2 ^ m` roots.
* `Cslib.FiniteField.exists_coeffPattern`: the structural lemma, for subspaces of dimension larger
  than every proper subfield.

## References

* [O. Ore, *On a special class of polynomials*][Ore1933]
* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
-/

@[expose] public section

namespace Cslib.FiniteField

open Polynomial Module

variable {F : Type*} [Field F]

/-! ### Linearized polynomials -/

/-- A polynomial is *linearized* (over `𝔽₂`) when every exponent with a nonzero coefficient is a
power of two. Over a field of characteristic two it evaluates to an additive function. -/
def IsLinearized (P : F[X]) : Prop :=
  ∀ i ∈ P.support, ∃ j, i = 2 ^ j

namespace IsLinearized

variable {P Q : F[X]}

theorem zero : IsLinearized (0 : F[X]) := by
  sorry

theorem add (hP : IsLinearized P) (hQ : IsLinearized Q) : IsLinearized (P + Q) := by
  sorry

theorem C_mul (hP : IsLinearized P) (c : F) : IsLinearized (C c * P) := by
  sorry

theorem X_pow_two_pow (j : ℕ) : IsLinearized (X ^ 2 ^ j : F[X]) := by
  sorry

theorem sq [CharP F 2] (hP : IsLinearized P) : IsLinearized (P ^ 2) := by
  sorry

theorem coeff_zero (hP : IsLinearized P) : P.coeff 0 = 0 := by
  sorry

/-- A linearized polynomial composes additively. -/
theorem comp_add [CharP F 2] (hP : IsLinearized P) (f g : F[X]) :
    P.comp (f + g) = P.comp f + P.comp g := by
  sorry

theorem eval_add [CharP F 2] (hP : IsLinearized P) (x y : F) :
    P.eval (x + y) = P.eval x + P.eval y := by
  sorry

end IsLinearized

/-- A field with a `ZMod 2`-algebra structure has characteristic two. -/
theorem charP_two [Algebra (ZMod 2) F] : CharP F 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2

/-- The `𝔽₂`-linear map given by evaluating a linearized polynomial. -/
noncomputable def IsLinearized.toLinearMap [Algebra (ZMod 2) F] {P : F[X]} (hP : IsLinearized P) :
    F →ₗ[ZMod 2] F :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := P.eval
      map_zero' := by
        sorry
      map_add' := by
        sorry }

@[simp]
theorem IsLinearized.toLinearMap_apply [Algebra (ZMod 2) F] {P : F[X]} (hP : IsLinearized P)
    (x : F) : hP.toLinearMap x = P.eval x :=
  rfl

/-! ### Subspace polynomials -/

variable [Algebra (ZMod 2) F]

/-- The *subspace polynomial* `∏_{c ∈ 𝔽₂ᵐ} (X - ∑ₗ cₗ bₗ)` of a family `b` of `m` elements. -/
noncomputable def subspacePoly {m : ℕ} (b : Fin m → F) : F[X] :=
  ∏ c : Fin m → ZMod 2, (X - C (∑ l, c l • b l))

theorem subspacePoly_monic {m : ℕ} (b : Fin m → F) : (subspacePoly b).Monic := by
  sorry

theorem natDegree_subspacePoly {m : ℕ} (b : Fin m → F) :
    (subspacePoly b).natDegree = 2 ^ m := by
  sorry

/-- Subspace polynomials are linearized [Ore1933]. -/
theorem isLinearized_subspacePoly {m : ℕ} (b : Fin m → F) : IsLinearized (subspacePoly b) := by
  sorry

/-- The roots of the subspace polynomial of `b` are the `𝔽₂`-span of `b`. -/
theorem eval_subspacePoly_eq_zero_iff {m : ℕ} (b : Fin m → F) (x : F) :
    (subspacePoly b).eval x = 0 ↔ x ∈ Submodule.span (ZMod 2) (Set.range b) := by
  sorry

/-- **Image-subspace polynomial** [BenSassonKopparty2012, Lemma 3.7]: every `𝔽₂`-subspace `W` of a
finite field `F` is the image of a monic linearized polynomial of degree
`2 ^ (dim F - dim W)`. -/
theorem exists_isLinearized_range_eq [Finite F] (W : Submodule (ZMod 2) F) :
    ∃ Q : F[X], IsLinearized Q ∧ Q.Monic ∧
      Q.natDegree = 2 ^ (finrank (ZMod 2) F - finrank (ZMod 2) W) ∧
      ∀ y, y ∈ W ↔ ∃ x, Q.eval x = y := by
  sorry

/-! ### Coefficient vectors indexed by `ZMod n` -/

/-- Evaluation of the linearized function `x ↦ ∑_{j ∈ ℤ/n} a j * x ^ 2 ^ j`. Over a field with
`2 ^ n` elements every linearized polynomial function has this form. -/
def linearizedEval {n : ℕ} [NeZero n] (a : ZMod n → F) (x : F) : F :=
  ∑ j, a j * x ^ 2 ^ j.val

/-- Frobenius periodicity: in a field with `2 ^ n` elements, `x ^ 2 ^ m` depends only on
`m % n`. -/
theorem pow_two_pow_mod [Finite F] {n : ℕ} (hn : finrank (ZMod 2) F = n) (x : F) (m : ℕ) :
    x ^ 2 ^ m = x ^ 2 ^ (m % n) := by
  sorry

/-- Raising a linearized function to the power `2 ^ k` rotates its coefficient vector. -/
theorem linearizedEval_pow_two_pow [Finite F] {n : ℕ} [NeZero n] (hn : finrank (ZMod 2) F = n)
    (a : ZMod n → F) (k : ℕ) (x : F) :
    linearizedEval a x ^ 2 ^ k = linearizedEval (fun j => a (j - (k : ZMod n)) ^ 2 ^ k) x := by
  sorry

/-- **Root bound for linearized functions**: if the coefficients of `b` vanish from position `m`
on and the function vanishes on at least `2 ^ m` points, then `b = 0`. -/
theorem eq_zero_of_linearizedEval_eq_zero {n : ℕ} [NeZero n] {b : ZMod n → F} {m : ℕ}
    (hb : ∀ j, m ≤ j.val → b j = 0) (S : Finset F) (hS : 2 ^ m ≤ S.card)
    (h : ∀ x ∈ S, linearizedEval b x = 0) : b = 0 := by
  sorry

/-- The zero pattern of the coefficient vector `a` of an image-subspace polynomial of a
`d`-dimensional subspace that lies in no multiple of a proper subfield
[BenSassonKopparty2012, Lemma 3.10]: the leading coefficient sits at `n - d`, the `d - 1`
positions above it vanish, the constant coefficient is nonzero, and every other window of
`d - 1` consecutive positions starting in `[1, n - d]` meets a nonzero coefficient. -/
structure CoeffPattern (n d : ℕ) [NeZero n] (a : ZMod n → F) : Prop where
  le : d ≤ n
  lead : a ((n - d : ℕ) : ZMod n) ≠ 0
  canonical : ∀ c, 1 ≤ c → c < d → a ((n - d + c : ℕ) : ZMod n) = 0
  zero_ne : a 0 ≠ 0
  gap : ∀ ρ : ℕ, 1 ≤ ρ → ρ + d ≤ n → ∃ c < d - 1, a ((ρ + c : ℕ) : ZMod n) ≠ 0

/-- **Structural lemma** [BenSassonKopparty2012, Lemma 3.10], for subspaces larger than every
proper subfield: a nonzero subspace `W` of dimension greater than `s`, where every proper subfield
has at most `2 ^ s` elements, is the image of a linearized function whose coefficient vector has
the zero pattern `CoeffPattern`. -/
theorem exists_coeffPattern [Finite F] {n s : ℕ} [NeZero n] (hn : finrank (ZMod 2) F = n)
    (hs : ∀ K : Subfield F, K ≠ ⊤ → Nat.card K ≤ 2 ^ s) (W : Submodule (ZMod 2) F)
    (hW : 0 < finrank (ZMod 2) W) (hsW : s < finrank (ZMod 2) W) :
    ∃ a : ZMod n → F, (∀ x, linearizedEval a x ∈ W) ∧ CoeffPattern n (finrank (ZMod 2) W) a := by
  sorry

end Cslib.FiniteField
