/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Basic

/-!
# Leaves and paths of decision trees

The Boolean answers along a root-to-leaf path identify the reached leaf, even when different
leaves have the same label. The structural leaf count includes unreachable leaves; a tree of depth
`d` has at most `2 ^ d` leaves.

## Main definitions

* `Cslib.DecisionTree.leafCount`: the number of leaves.
* `Cslib.DecisionTree.path`: the answers along the path taken by an input.

## Main results

* `Cslib.DecisionTree.eval_eq_of_path_eq`: a common path gives a common output.
* `Cslib.DecisionTree.leafCount_le_two_pow_depth`: a tree of depth `d` has at most `2 ^ d` leaves.
-/

@[expose] public section

namespace Cslib.DecisionTree

variable {ι β : Type*}

/-- The number of structural leaves, including any unreachable leaves. -/
def leafCount : DecisionTree ι β → ℕ
  | .leaf _ => 1
  | .node _ left right => left.leafCount + right.leafCount

/-- The answers along the path to the reached leaf. -/
def path : DecisionTree ι β → (ι → Bool) → List Bool
  | .leaf _, _ => []
  | .node i left right, x => x i :: cond (x i) (right.path x) (left.path x)

/-- Every decision tree has at least one structural leaf. -/
theorem leafCount_pos (t : DecisionTree ι β) : 0 < t.leafCount := by
  induction t with
  | leaf => exact Nat.zero_lt_one
  | node _ _ _ ih _ => exact Nat.add_pos_left ih _

/-- A decision tree of depth `d` has at most `2 ^ d` structural leaves. -/
theorem leafCount_le_two_pow_depth (t : DecisionTree ι β) : t.leafCount ≤ 2 ^ t.depth := by
  induction t with
  | leaf => exact le_refl 1
  | node i t₀ t₁ ih₀ ih₁ =>
    rw [leafCount, depth_node, Nat.pow_succ, Nat.mul_two]
    exact Nat.add_le_add (ih₀.trans (Nat.pow_le_pow_right Nat.two_pos (Nat.le_max_left _ _)))
      (ih₁.trans (Nat.pow_le_pow_right Nat.two_pos (Nat.le_max_right _ _)))

/-- Inputs following the same path reach the same leaf label. -/
theorem eval_eq_of_path_eq (t : DecisionTree ι β) {x y : ι → Bool}
    (h : t.path x = t.path y) : t.eval x = t.eval y := by
  induction t with
  | leaf => rfl
  | node i left right ihl ihr =>
    simp only [path, List.cons.injEq] at h
    simp only [eval_node, h.1]
    cases hy : y i
    · apply ihl
      simpa only [h.1, hy, Bool.cond_false] using h.2
    · apply ihr
      simpa only [h.1, hy, Bool.cond_true] using h.2

/-- Relabelling queries preserves the structural leaf count, including unreachable leaves. -/
@[simp]
theorem leafCount_mapQueries {κ : Type*} (f : ι → κ) (t : DecisionTree ι β) :
    (t.mapQueries f).leafCount = t.leafCount := by
  induction t with
  | leaf => rfl
  | node i left right ihl ihr => simp [mapQueries, leafCount, ihl, ihr]

end Cslib.DecisionTree
