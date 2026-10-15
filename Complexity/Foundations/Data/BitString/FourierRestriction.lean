/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Fourier
public import Mathlib.Data.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Fourier coefficients of restrictions

Fixing the coordinates outside a set `J` to the bits of `z` turns `f` into the function
`x ↦ f (J.piecewise x z)` of the coordinates in `J`. Its Fourier coefficient on `S` collects the
coefficients of `f` on the sets `U` with `U ∩ J = S`, twisted by the characters of `U \ J` at `z`
(`BitString.fourierCoeff_piecewise`). Averaged over a uniformly random `z`, the twists are
orthogonal, so the expected squared coefficient on `S` is the weight of `f` on the sets meeting
`J` in `S` (`BitString.expect_fourierCoeff_piecewise_sq`), and the expected weight of the
restriction on sets of at least `m` coordinates is the weight of `f` on the sets meeting `J` in at
least `m` coordinates (`BitString.expect_sum_fourierCoeff_piecewise_sq`)
[O'Donnell, Section 3.3][ODonnell2014].

## Main results

* `Cslib.BitString.fourierCoeff_piecewise`: the coefficients of a restriction.
* `Cslib.BitString.expect_sum_fourierCoeff_piecewise_sq`: the expected weight of a restriction
  above a degree.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {n : ℕ}

/-- A character at a point with the coordinates outside `J` replaced splits into the characters
of the parts of `U` inside and outside `J`. -/
theorem chi_piecewise (U J : Finset (Fin n)) (x z : BitString n) :
    chi U (J.piecewise x z) = chi (U ∩ J) x * chi (U \ J) z := by
  rw [chi, ← prod_filter_mul_prod_filter_not U (· ∈ J), filter_mem_eq_inter, ← sdiff_eq_filter,
    chi, chi]
  congr 1
  · exact prod_congr rfl fun i hi => by rw [piecewise_eq_of_mem _ _ _ (mem_inter.1 hi).2]
  · exact prod_congr rfl fun i hi => by rw [piecewise_eq_of_notMem _ _ _ (mem_sdiff.1 hi).2]

/-- **The Fourier coefficients of a restriction**: the coefficient on `S` sums the coefficients
of `f` on the sets meeting `J` in `S`, each multiplied by the character of its part outside `J`
at `z`. -/
theorem fourierCoeff_piecewise (f : BitString n → ℝ) (J : Finset (Fin n)) (z : BitString n)
    (S : Finset (Fin n)) :
    fourierCoeff (fun x => f (J.piecewise x z)) S =
      ∑ U with U ∩ J = S, fourierCoeff f U * chi (U \ J) z := by
  have h (x : BitString n) : f (J.piecewise x z) =
      ∑ U, (fourierCoeff f U * chi (U \ J) z) * chi (U ∩ J) x := by
    rw [← sum_fourierCoeff_mul_chi f (J.piecewise x z)]
    exact sum_congr rfl fun U _ => by rw [chi_piecewise]; ring
  rw [fourierCoeff]
  simp only [h, sum_mul, mul_assoc]
  rw [expect_sum_comm, sum_filter]
  refine sum_congr rfl fun U _ => ?_
  simp only [← mul_expect, expect_chi_mul_chi]
  split_ifs <;> simp

/-- Averaged over the fixed bits, the squared coefficient of a restriction on `S` is the weight of
`f` on the sets meeting `J` in `S`. -/
theorem expect_fourierCoeff_piecewise_sq (f : BitString n → ℝ) (J S : Finset (Fin n)) :
    𝔼 z, fourierCoeff (fun x => f (J.piecewise x z)) S ^ 2 =
      ∑ U with U ∩ J = S, fourierCoeff f U ^ 2 := by
  have key (U V : Finset (Fin n)) :
      𝔼 z, fourierCoeff f U * chi (U \ J) z * (fourierCoeff f V * chi (V \ J) z) =
        fourierCoeff f U * fourierCoeff f V * if U \ J = V \ J then 1 else 0 := by
    rw [← expect_chi_mul_chi, mul_expect]
    exact expect_congr rfl fun z _ => by ring
  simp only [fourierCoeff_piecewise, sq, sum_mul_sum, expect_sum_comm, key]
  refine sum_congr rfl fun U hU => ?_
  rw [sum_eq_single_of_mem U hU fun V hV hVU => ?_]
  · simp
  · -- two sets meeting `J` in the same part differ outside `J`
    rw [mem_filter] at hU hV
    have hne : U \ J ≠ V \ J := fun h => hVU (by
      rw [← sdiff_union_inter V J, ← sdiff_union_inter U J, h, hU.2, hV.2])
    simp [hne]

/-- **The expected weight of a restriction above a degree**: averaged over the fixed bits, the
Fourier weight of the restriction on sets of at least `m` coordinates is the weight of `f` on the
sets meeting `J` in at least `m` coordinates. -/
theorem expect_sum_fourierCoeff_piecewise_sq (f : BitString n → ℝ) (J : Finset (Fin n)) (m : ℕ) :
    𝔼 z, ∑ S with m ≤ #S, fourierCoeff (fun x => f (J.piecewise x z)) S ^ 2 =
      ∑ U with m ≤ #(U ∩ J), fourierCoeff f U ^ 2 := by
  rw [expect_sum_comm]
  simp only [expect_fourierCoeff_piecewise_sq]
  calc ∑ S with m ≤ #S, ∑ U with U ∩ J = S, fourierCoeff f U ^ 2
      = ∑ S with m ≤ #S, ∑ U, if U ∩ J = S then fourierCoeff f U ^ 2 else 0 := by
        simp only [sum_filter]
    _ = ∑ U, ∑ S with m ≤ #S, if U ∩ J = S then fourierCoeff f U ^ 2 else 0 := sum_comm
    _ = ∑ U with m ≤ #(U ∩ J), fourierCoeff f U ^ 2 := by
        rw [sum_filter]
        refine sum_congr rfl fun U _ => ?_
        rw [sum_ite_eq]
        simp

end Cslib.BitString
