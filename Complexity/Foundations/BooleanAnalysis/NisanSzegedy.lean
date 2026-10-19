/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Influence
public import Mathlib.Data.Finset.Density
import Complexity.Foundations.BooleanAnalysis.FourierDegree
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Tactic.NormNum

/-!
# The Nisan–Szegedy bound on relevant variables

A coordinate `i` is *relevant* to a Boolean function `f` when flipping bit `i` changes the value of
`f` on some input, that is when the influence of `i` on `f`, read as signs, is nonzero
(`BitString.influence_signVal`). A Boolean function of Fourier degree at most `d` has at most
`d * 2 ^ (d - 1)` relevant coordinates (`BitString.card_filter_influence_ne_zero_le`)
[NisanSzegedy1994] [O'Donnell, Chapter 3][ODonnell2014].

The influence of `i` is the density of the points where the derivative in `i` is nonzero
(`BitString.influence_signVal_eq_dens`), and this derivative has degree at most `d - 1`. By
Schwartz–Zippel on the cube, a nonzero influence is therefore at least `2 ^ (1 - d)`
(`BitString.one_le_two_pow_mul_influence_of_degree`), while the influences sum to at most `d`
(`BitString.totalInfluence_signVal_le_of_degree`).

## Main results

* `Cslib.BitString.influence_signVal_eq_dens`: the influence on a Boolean function is the density
  of the points where the derivative is nonzero.
* `Cslib.BitString.one_le_two_pow_mul_influence_of_degree`: granularity of the influences of a
  low-degree Boolean function.
* `Cslib.BitString.card_filter_influence_ne_zero_le`: the Nisan–Szegedy bound.

## References

* [N. Nisan and M. Szegedy, *On the Degree of Boolean Functions as Real
  Polynomials*][NisanSzegedy1994]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

open Finset Function
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The influence of `i` on a Boolean function read as signs is the density of the points where
its derivative in `i` is nonzero. -/
theorem influence_signVal_eq_dens (f : (ι → Bool) → Bool) (i : ι) :
    influence i (fun x => signVal (f x)) =
      (dens {x | derivative i (fun x => signVal (f x)) x ≠ 0} : ℝ) := by
  rw [← Fintype.expect_boole, influence]
  refine expect_congr rfl fun x _ => ?_
  split_ifs with h
  · simp only [derivative] at h ⊢
    revert h
    cases f (update x i false) <;> cases f (update x i true) <;> norm_num
  · rw [not_not.1 h, sq, mul_zero]

/-- **Granularity of influences**: a nonzero influence of a Boolean function of Fourier degree at
most `d`, read as signs, is at least `2 ^ (1 - d)`. -/
theorem one_le_two_pow_mul_influence_of_degree (f : (ι → Bool) → Bool) {d : ℕ}
    (hdeg : ∀ S : Finset ι, d < #S → fourierCoeff (fun x => signVal (f x)) S = 0) (i : ι)
    (hi : influence i (fun x => signVal (f x)) ≠ 0) :
    1 ≤ 2 ^ (d - 1) * influence i (fun x => signVal (f x)) := by
  have hdeg' (T : Finset ι) (hT : d - 1 < #T) :
      fourierCoeff (derivative i fun x => signVal (f x)) T = 0 := by
    rw [fourierCoeff_derivative]
    split_ifs with hiT
    · rfl
    · exact hdeg _ (by rw [card_insert_of_notMem hiT]; omega)
  have hne : derivative i (fun x => signVal (f x)) ≠ 0 := by
    intro h0
    apply hi
    simp [influence, h0]
  rw [influence_signVal_eq_dens]
  exact one_le_two_pow_mul_dens_ne_zero _ hdeg' hne

/-- **The Nisan–Szegedy bound**: a Boolean function of Fourier degree at most `d` has at most
`d * 2 ^ (d - 1)` relevant coordinates, the coordinates of nonzero influence
[NisanSzegedy1994]. -/
theorem card_filter_influence_ne_zero_le (f : (ι → Bool) → Bool) {d : ℕ}
    (hdeg : ∀ S : Finset ι, d < #S → fourierCoeff (fun x => signVal (f x)) S = 0) :
    #{i | influence i (fun x => signVal (f x)) ≠ 0} ≤ d * 2 ^ (d - 1) := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  set R : Finset ι := {i | influence i F ≠ 0}
  have hpow : (0 : ℝ) ≤ 2 ^ (d - 1) := by positivity
  have h : (#R : ℝ) ≤ d * 2 ^ (d - 1) :=
    calc (#R : ℝ) = ∑ i ∈ R, (1 : ℝ) := by rw [sum_const, nsmul_one]
      _ ≤ ∑ i ∈ R, 2 ^ (d - 1) * influence i F :=
          sum_le_sum fun i hi => one_le_two_pow_mul_influence_of_degree f hdeg i (mem_filter.1 hi).2
      _ ≤ ∑ i, 2 ^ (d - 1) * influence i F :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ =>
            mul_nonneg hpow (influence_nonneg i F)
      _ = 2 ^ (d - 1) * totalInfluence F := by rw [totalInfluence, mul_sum]
      _ ≤ 2 ^ (d - 1) * d :=
          mul_le_mul_of_nonneg_left (totalInfluence_signVal_le_of_degree f hdeg) hpow
      _ = d * 2 ^ (d - 1) := mul_comm _ _
  exact_mod_cast h

end Cslib.BitString
