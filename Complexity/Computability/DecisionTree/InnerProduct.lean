/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Separable
public import Complexity.Foundations.BooleanAnalysis.Hadamard
import Complexity.Foundations.BooleanAnalysis.HadamardRectangles
import Mathlib.Tactic.Positivity

/-!
# Inner-product lower bound for separable comparison trees

A separable-comparison tree computing the inner product modulo two on `ι → Bool` has leaf count
`L` satisfying `2 ^ Fintype.card ι ≤ L ^ 2`. This division-free form of
`L ≥ 2 ^ (Fintype.card ι / 2)` follows from the generic leaf-rectangle theorem and the Hadamard
rectangle bound. Query scores are arbitrary real functions; the result imposes no restriction
on their magnitudes or on the tree depth, and does not require a threshold circuit model.

## Main results

* `Cslib.DecisionTree.two_pow_le_leafCount_sq_of_hadamardCode`: the inner-product leaf bound.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Corollary 2.5]
  [ThresholdCircuitRepresentations2026]
-/

@[expose] public section

open Cslib.BitString

namespace Cslib.DecisionTree

/-- Computing inner product modulo two requires the square of the leaf count to be at least
the cardinality of the Boolean cube. The statement includes zero coordinates. -/
theorem two_pow_le_leafCount_sq_of_hadamardCode {ι : Type*} [Fintype ι]
    (t : DecisionTree (SeparableComparison (ι → Bool) (ι → Bool)) Bool)
    (ht : ∀ x y, t.eval (fun q => q.eval x y) = hadamardCode x y) :
    2 ^ Fintype.card ι ≤ t.leafCount ^ 2 := by
  classical
  have h := t.card_mul_le_mul_leafCount_sq Finset.univ Finset.univ (by simp) (by simp)
    (R := 2 ^ Fintype.card ι) (fun A _ B _ b hb =>
      card_mul_le_two_pow_of_hadamardCode_eq A B b fun x hx y hy =>
        (ht x y).symm.trans (hb x hx y hy))
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool] at h
  exact Nat.le_of_mul_le_mul_left h (by positivity)

end Cslib.DecisionTree
