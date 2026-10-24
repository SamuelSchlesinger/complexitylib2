/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Polynomial.CoeffList
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.List.GetD

/-!
# Polynomials as lists of their low coefficients

Mathlib's `Polynomial.ofCoeffList` builds a polynomial from its coefficients, the constant
coefficient first. This file evaluates such a polynomial by Horner's rule on the list
(`Polynomial.evalCoeffList`), bounds its degree by the length of the list less one, lists the first
`n` coefficients of a polynomial (`Polynomial.coeffsBelow`), which give the polynomial back when
its degree is less than `n`. An interactive verifier receives polynomials in this form.

## Main definitions

* `Polynomial.evalCoeffList`: Horner evaluation of a coefficient list.
* `Polynomial.coeffsBelow`: the coefficients of `X ^ 0`, …, `X ^ (n - 1)`.

## Main results

* `Polynomial.eval_ofCoeffList`: evaluation is Horner's rule.
* `Polynomial.natDegree_ofCoeffList_le`: the degree is at most the length of the list less one.
* `Polynomial.ofCoeffList_coeffsBelow`: low coefficients determine a polynomial of small degree.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [Semiring R]

/-- The value at `z` of the polynomial with coefficient list `l`, the constant coefficient first,
by Horner's rule. -/
def evalCoeffList (z : R) (l : List R) : R := l.foldr (fun a acc => a + z * acc) 0

/-- The empty coefficient list evaluates to `0`. -/
@[simp] theorem evalCoeffList_nil (z : R) : evalCoeffList z [] = 0 := rfl

/-- Horner's step: `a :: l` evaluates to `a + z * evalCoeffList z l`. -/
@[simp] theorem evalCoeffList_cons (z a : R) (l : List R) :
    evalCoeffList z (a :: l) = a + z * evalCoeffList z l := rfl

/-- The value of the polynomial with coefficient list `l` is given by Horner's rule. -/
theorem eval_ofCoeffList {R : Type*} [CommSemiring R] (z : R) (l : List R) :
    (ofCoeffList l).eval z = evalCoeffList z l := by
  induction l with
  | nil => simp
  | cons a l ih => rw [ofCoeffList_cons, eval_add, eval_C, eval_mul, eval_X, ih,
      evalCoeffList_cons]

/-- The polynomial with coefficient list `l` has degree at most `l.length - 1`. -/
theorem natDegree_ofCoeffList_le (l : List R) : (ofCoeffList l).natDegree ≤ l.length - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_ofCoeffList, List.getD_eq_default _ _ (by omega)]

/-- The coefficients of `X ^ 0`, …, `X ^ (n - 1)` of a polynomial, in this order. -/
def coeffsBelow (P : R[X]) (n : ℕ) : List R := (List.range n).map P.coeff

/-- `coeffsBelow P n` has length `n`. -/
@[simp] theorem length_coeffsBelow (P : R[X]) (n : ℕ) : (P.coeffsBelow n).length = n := by
  simp only [coeffsBelow, List.length_map, List.length_range]

/-- The first `n` coefficients of a polynomial of degree less than `n` give the polynomial back. -/
theorem ofCoeffList_coeffsBelow {P : R[X]} {n : ℕ} (hP : P.natDegree < n) :
    ofCoeffList (P.coeffsBelow n) = P := by
  ext i
  rw [coeff_ofCoeffList, coeffsBelow]
  by_cases hi : i < n
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
      Option.getD_some]
  · rw [List.getD_eq_default _ _ (by simp only [List.length_map, List.length_range]; omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

end Polynomial
