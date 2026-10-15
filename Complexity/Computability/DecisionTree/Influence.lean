/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Fourier
public import Complexity.Computability.DecisionTree.Sensitivity
public import Complexity.Foundations.BooleanAnalysis.Influence
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Influence and sensitivity

The total influence of a Boolean function, read as signs, is its *average sensitivity*: the
expected number of bits whose flip changes the value
(`DecisionTree.totalInfluence_eq_expect_sensitivityAt`) [O'Donnell, Section 2.3][ODonnell2014], so
it is at most the sensitivity. A function computed by a decision tree of depth `d` has Fourier
degree at most `d`, so its total influence is at most `d` (`DecisionTree.totalInfluence_le_depth`).

## Main results

* `Cslib.DecisionTree.totalInfluence_eq_expect_sensitivityAt`: total influence is average
  sensitivity.
* `Cslib.DecisionTree.totalInfluence_le_sensitivity`: it is at most the sensitivity.
* `Cslib.DecisionTree.totalInfluence_le_depth`: functions of decision trees of depth `d` have
  total influence at most `d`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.DecisionTree

open Finset BitString
open scoped BigOperators

variable {n : ℕ}

/-- **Total influence is average sensitivity**: the total influence of a Boolean function, read as
signs, is the expected number of bits whose flip changes its value. -/
theorem totalInfluence_eq_expect_sensitivityAt (f : BitString n → Bool) :
    totalInfluence (fun x => signVal (f x)) = 𝔼 x, (sensitivityAt f x : ℝ) :=
  totalInfluence_signVal f

/-- The total influence of a Boolean function, read as signs, is at most its sensitivity. -/
theorem totalInfluence_le_sensitivity (f : BitString n → Bool) :
    totalInfluence (fun x => signVal (f x)) ≤ sensitivity f := by
  rw [totalInfluence_eq_expect_sensitivityAt]
  exact expect_le univ_nonempty fun x _ => by exact_mod_cast sensitivityAt_le_sensitivity f x

/-- **Decision trees of depth `d` have total influence at most `d`**: a Boolean function of the
output of a decision tree of depth `d`, read as signs, has Fourier weight only on sets of at most
`d` coordinates, and its squared coefficients sum to one. -/
theorem totalInfluence_le_depth (g : β → Bool) (t : DecisionTree (Fin n) β) :
    totalInfluence (fun x => signVal (g (t.eval x))) ≤ t.depth := by
  rw [totalInfluence_eq_sum_card_mul_fourierCoeff_sq]
  calc ∑ S, (#S : ℝ) * fourierCoeff (fun x => signVal (g (t.eval x))) S ^ 2
      ≤ ∑ S, (t.depth : ℝ) * fourierCoeff (fun x => signVal (g (t.eval x))) S ^ 2 := by
        refine sum_le_sum fun S _ => ?_
        rcases le_or_gt #S t.depth with h | h
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) (sq_nonneg _)
        · rw [fourierCoeff_eq_zero_of_depth_lt (fun b => signVal (g b)) t h]
          simp
    _ = t.depth := by
        rw [← mul_sum, sum_fourierCoeff_sq_signVal fun x => g (t.eval x), mul_one]

end Cslib.DecisionTree
