/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.LowDegree
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Multilinear extensions of functions on the cube

Every function `g : (ι → Bool) → R` on a finite cube is the restriction of a multilinear
polynomial: the sum over the points `a` of the cube of `g a` times the indicator polynomial of `a`,
the product of `X i` over the coordinates where `a i` is true and of `1 - X i` over the others.
Its total degree is at most the dimension.

## Main definitions

* `Cslib.BitString.indicatorPoly`: the multilinear polynomial that is `1` at a point of the cube
  and `0` at every other point.
* `Cslib.BitString.multilinearExtension`: the multilinear extension of a function on the cube.

## Main results

* `Cslib.BitString.eval_multilinearExtension`: the extension agrees with the function on the cube.
* `Cslib.BitString.totalDegree_multilinearExtension_le`: its total degree is at most the
  dimension.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Section 1.2 for the indicator
  polynomials.
-/

@[expose] public section

open MvPolynomial

namespace Cslib.BitString

variable {ι R : Type*} [CommRing R]

/-- The indicator polynomial of a point `a` of the cube: the product of `X i` where `a i` is true
and of `1 - X i` where it is false. -/
noncomputable def indicatorPoly [Fintype ι] (a : ι → Bool) : MvPolynomial ι R :=
  ∏ i, if a i then X i else 1 - X i

/-- The multilinear extension of a function on the cube. -/
noncomputable def multilinearExtension [Fintype ι] [DecidableEq ι] (g : (ι → Bool) → R) :
    MvPolynomial ι R :=
  ∑ a, C (g a) * indicatorPoly a

/-- On the cube, the indicator polynomial of `a` is `1` at `a` and `0` elsewhere. -/
theorem eval_indicatorPoly [Fintype ι] (a x : ι → Bool) :
    eval (fun i => bitVal R (x i)) (indicatorPoly a : MvPolynomial ι R) =
      if a = x then 1 else 0 := by
  simp only [indicatorPoly, map_prod]
  split_ifs with h
  · subst h
    exact Finset.prod_eq_one fun i _ => by cases h : a i <;> simp [h]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    cases ha : a i <;> cases hx : x i <;> simp_all

/-- The multilinear extension agrees with the function on the cube. -/
theorem eval_multilinearExtension [Fintype ι] [DecidableEq ι] (g : (ι → Bool) → R)
    (x : ι → Bool) : eval (fun i => bitVal R (x i)) (multilinearExtension g) = g x := by
  simp only [multilinearExtension, map_sum, map_mul, eval_C, eval_indicatorPoly, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- An indicator polynomial has total degree at most the dimension. -/
theorem totalDegree_indicatorPoly_le [Fintype ι] (a : ι → Bool) :
    (indicatorPoly a : MvPolynomial ι R).totalDegree ≤ Fintype.card ι := by
  have hX (i : ι) : (X i : MvPolynomial ι R).totalDegree ≤ 1 :=
    (totalDegree_monomial_le _ _).trans (by simp)
  refine (totalDegree_finsetProd _ _).trans ?_
  rw [Finset.card_univ.symm, Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs
  · exact hX i
  · exact (totalDegree_sub _ _).trans (max_le (by simp) (hX i))

/-- The multilinear extension has total degree at most the dimension. -/
theorem totalDegree_multilinearExtension_le [Fintype ι] [DecidableEq ι] (g : (ι → Bool) → R) :
    (multilinearExtension g).totalDegree ≤ Fintype.card ι := by
  refine (totalDegree_finsetSum _ _).trans <| Finset.sup_le fun a _ => ?_
  exact (totalDegree_mul _ _).trans <| by
    simpa using totalDegree_indicatorPoly_le (R := R) a

end Cslib.BitString
