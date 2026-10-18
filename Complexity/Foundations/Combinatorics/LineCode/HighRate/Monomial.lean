/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Polynomial

/-!
# Monomials on lines of a finite field

Over a finite field `K` with `q` elements, the values of a polynomial of degree below `q - 1`
sum to zero (`sum_eval_eq_zero_of_natDegree_lt`). The restriction of a monomial
`∏ i, X i ^ e i` to an affine line can have degree up to `∑ i, e i`, but in characteristic two a
Frobenius twist lowers it. For `q = 2 ^ (r + s)`, substitute `x = y ^ 2 ^ r` and split
`e = e % 2 ^ s + 2 ^ s * (e / 2 ^ s)`; since `y ^ q = y`, the restriction becomes a polynomial in
`y` of degree at most `∑ i, (2 ^ r * (e i % 2 ^ s) + e i / 2 ^ s)`; for `e i < q` this is the
total of the `(r + s)`-digit binary exponents rotated cyclically by `s` digits. When it is below
`q - 1` the line sum vanishes (`sum_prod_add_mul_pow_eq_zero`). No form of Lucas's theorem is
used.

Monomials with exponents below `q` are linearly independent as functions on `K ^ σ`
(`linearIndependent_prod_pow`), by the combinatorial Nullstellensatz.

## Main results

* `Cslib.LineCode.HighRate.sum_eval_eq_zero_of_natDegree_lt`: low-degree polynomials sum to zero.
* `Cslib.LineCode.HighRate.sum_prod_add_mul_pow_eq_zero`: monomials with small rotated degree sum
  to zero on every affine line.
* `Cslib.LineCode.HighRate.linearIndependent_prod_pow`: distinct reduced monomials are linearly
  independent functions.

## References

* Adapted from `MassProduction/HighRate/LineParity.lean`,
  `MassProduction/HighRate/PolynomialSupport.lean`, `MassProduction/HighRate/Independence.lean`
  and `MassProduction/LowDegree.lean` in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.LineCode.HighRate

open Finset Polynomial

variable {K : Type*} [Field K] [Fintype K]

/-- The values of a polynomial of degree below `Fintype.card K - 1` sum to zero over the finite
field `K`. -/
theorem sum_eval_eq_zero_of_natDegree_lt (p : K[X]) (hp : p.natDegree < Fintype.card K - 1) :
    ∑ x : K, p.eval x = 0 := by
  simp only [eval_eq_sum_range]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← Finset.mul_sum, FiniteField.sum_pow_lt_card_sub_one K i
    ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans_lt hp), mul_zero]

/-- **Frobenius twist.** Let `K` have `2 ^ (r + s)` elements. If the exponents `e i`, rotated by
`s` binary digits, have total `∑ i, (2 ^ r * (e i % 2 ^ s) + e i / 2 ^ s)` below
`Fintype.card K - 1`, then the values of the monomial `∏ i, X i ^ e i` on the affine line
`x ↦ u + x • v` sum to zero. -/
theorem sum_prod_add_mul_pow_eq_zero [CharP K 2] {ι : Type*} [Fintype ι] {r s : ℕ}
    (hK : Fintype.card K = 2 ^ (r + s)) (u v : ι → K) (e : ι → ℕ)
    (he : ∑ i, (2 ^ r * (e i % 2 ^ s) + e i / 2 ^ s) < Fintype.card K - 1) :
    ∑ x : K, ∏ i, (u i + x * v i) ^ e i = 0 := by
  -- Substitute `x = y ^ 2 ^ r`, a bijection with inverse `x ↦ x ^ 2 ^ s`.
  have hbij : Function.Bijective fun y : K => y ^ 2 ^ r := by
    refine Finite.injective_iff_bijective.mp
      (Function.LeftInverse.injective (g := fun y : K => y ^ 2 ^ s) fun y => ?_)
    change (y ^ 2 ^ r) ^ 2 ^ s = y
    rw [← pow_mul, ← pow_add, ← hK, FiniteField.pow_card]
  let P : K[X] := ∏ i, (C (u i) + C (v i) * X ^ 2 ^ r) ^ (e i % 2 ^ s) *
    (C (u i ^ 2 ^ s) + C (v i ^ 2 ^ s) * X) ^ (e i / 2 ^ s)
  have hP (y : K) : ∏ i, (u i + y ^ 2 ^ r * v i) ^ e i = P.eval y := by
    simp only [P, eval_prod, eval_mul, eval_pow, eval_add, eval_C, eval_X]
    refine Finset.prod_congr rfl fun i _ => ?_
    conv_lhs => rw [← Nat.mod_add_div (e i) (2 ^ s), pow_add, pow_mul, add_pow_char_pow,
      mul_pow, ← pow_mul, ← pow_add, ← hK, FiniteField.pow_card]
    ring
  have hdeg : P.natDegree ≤ ∑ i, (2 ^ r * (e i % 2 ^ s) + e i / 2 ^ s) := by
    refine (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine natDegree_mul_le.trans (add_le_add ?_ ?_)
    · refine (natDegree_pow_le_of_le _ ?_).trans (mul_comm _ _).le
      rw [natDegree_C_add]
      exact natDegree_C_mul_X_pow_le _ _
    · refine (natDegree_pow_le_of_le _ ?_).trans (mul_one _).le
      rw [natDegree_C_add]
      exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  rw [← hbij.sum_comp]
  simp only [hP]
  exact sum_eval_eq_zero_of_natDegree_lt P (hdeg.trans_lt he)

/-- Monomials `∏ j, X j ^ e i j` with distinct exponent vectors, all of whose exponents are below
`Fintype.card K`, are linearly independent as functions on `σ → K`. -/
theorem linearIndependent_prod_pow {ι σ : Type*} [Fintype σ] (e : ι → σ → ℕ)
    (he : Function.Injective e) (hlt : ∀ i j, e i j < Fintype.card K) :
    LinearIndependent K fun i (x : σ → K) => ∏ j, x j ^ e i j := by
  classical
  let d : ι → σ →₀ ℕ := fun i => Finsupp.equivFunOnFinite.symm (e i)
  have hd : LinearIndependent K fun i => MvPolynomial.monomial (d i) (1 : K) :=
    (MvPolynomial.basisMonomials σ K).linearIndependent.comp d
      (Finsupp.equivFunOnFinite.symm.injective.comp he)
  have hspan : Submodule.span K (Set.range fun i => MvPolynomial.monomial (d i) (1 : K)) ≤
      MvPolynomial.restrictDegree σ K (Fintype.card K - 1) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, MvPolynomial.mem_restrictDegree]
    intro t ht j
    obtain rfl := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
    exact Nat.le_sub_one_of_lt (hlt i j)
  -- Evaluation is injective on polynomials of degree below `Fintype.card K` in each variable.
  convert hd.map (f := MvPolynomial.evalₗ K σ) ?_ using 1
  · funext i x
    simp [d, MvPolynomial.eval_monomial, Finsupp.prod_fintype]
  · rw [Submodule.disjoint_def]
    intro p hp hker
    refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset p (fun _ => Finset.univ)
      (fun j => ?_) fun x _ => by simpa using congrFun (LinearMap.mem_ker.mp hker) x
    rw [Finset.card_univ, MvPolynomial.degreeOf_lt_iff Fintype.card_pos]
    intro t ht
    exact ((MvPolynomial.mem_restrictDegree _ _ _).mp (hspan hp) t ht j).trans_lt
      (Nat.sub_lt Fintype.card_pos one_pos)

end Cslib.LineCode.HighRate
