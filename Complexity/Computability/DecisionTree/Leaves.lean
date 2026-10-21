/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Basic
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Leaves, rank, decision lists, and energy of decision trees

The Boolean answers along a root-to-leaf path identify the reached leaf, even when different
leaves have the same label. The structural leaf count includes unreachable leaves and exceeds the
internal node count by one. A tree of depth `d` has at most `2 ^ d` leaves; refined by
Ehrenfeucht–Haussler rank `r` or by right-branch energy `e`, it has at most
`∑ j ∈ Finset.range (r + 1), d.choose j` or `∑ j ∈ Finset.range (e + 1), d.choose j` leaves.
Decision lists have rank at most `1`, hence at most `d + 1` leaves and `d` internal nodes.

## Main definitions

* `Cslib.DecisionTree.leafCount`: the number of structural leaves.
* `Cslib.DecisionTree.nodeCount`: the number of internal query nodes.
* `Cslib.DecisionTree.path`: the answers along the path taken by an input.
* `Cslib.DecisionTree.rank`: the Ehrenfeucht–Haussler rank of a binary decision tree.
* `Cslib.DecisionTree.IsDecisionList`: trees in which every internal node has a leaf child.
* `Cslib.DecisionTree.energy`: the maximum number of `true` branches on a root-to-leaf path.

## Main results

* `Cslib.DecisionTree.eval_eq_of_path_eq`: a common path gives a common output.
* `Cslib.DecisionTree.leafCount_eq_nodeCount_add_one`: a binary tree has one more leaf than
  internal nodes.
* `Cslib.DecisionTree.leafCount_le_two_pow_depth`: a tree of depth `d` has at most `2 ^ d` leaves.
* `Cslib.DecisionTree.leafCount_le_sum_choose_rank`: a tree of depth `d` and rank `r` has at most
  `∑ j ≤ r, d.choose j` leaves.
* `Cslib.DecisionTree.IsDecisionList.rank_le_one`: every decision list has rank at most `1`.
* `Cslib.DecisionTree.leafCount_le_sum_choose_energy`: a tree of depth `d` and energy `e` has at
  most `∑ j ≤ e, d.choose j` leaves.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Section 2.2]
  [ThresholdCircuitRepresentations2026]
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

/-- Relabelling queries preserves the path taken by an input. -/
@[simp]
theorem path_mapQueries {κ : Type*} (f : ι → κ) (t : DecisionTree ι β) (x : κ → Bool) :
    (t.mapQueries f).path x = t.path (x ∘ f) := by
  induction t with
  | leaf => rfl
  | node i left right ihl ihr => simp [mapQueries, path, ihl, ihr]

/-- The number of internal query nodes, including any unreachable subtrees. -/
def nodeCount : DecisionTree ι β → ℕ
  | .leaf _ => 0
  | .node _ left right => left.nodeCount + right.nodeCount + 1

@[simp]
theorem nodeCount_leaf (b : β) : (leaf b : DecisionTree ι β).nodeCount = 0 :=
  rfl

@[simp]
theorem nodeCount_node (i : ι) (left right : DecisionTree ι β) :
    (node i left right).nodeCount = left.nodeCount + right.nodeCount + 1 :=
  rfl

/-- The structural leaf count exceeds the internal node count by one. -/
theorem leafCount_eq_nodeCount_add_one (t : DecisionTree ι β) :
    t.leafCount = t.nodeCount + 1 := by
  induction t with
  | leaf => rfl
  | node _ left right ihl ihr =>
    simp only [leafCount, nodeCount_node, ihl, ihr]
    omega

/-- Relabelling queries preserves the internal node count. -/
@[simp]
theorem nodeCount_mapQueries {κ : Type*} (f : ι → κ) (t : DecisionTree ι β) :
    (t.mapQueries f).nodeCount = t.nodeCount := by
  induction t with
  | leaf => rfl
  | node i left right ihl ihr => simp [mapQueries, nodeCount, ihl, ihr]

private theorem sum_choose_succ_add (r d : ℕ) :
    (∑ j ∈ Finset.range (r + 1 + 1), d.choose j) + (∑ j ∈ Finset.range (r + 1), d.choose j) =
      ∑ j ∈ Finset.range (r + 1 + 1), (d + 1).choose j := by
  rw [Finset.sum_range_succ' (fun j => (d + 1).choose j) (r + 1),
    Finset.sum_range_succ' (fun j => d.choose j) (r + 1)]
  simp only [Nat.choose_succ_succ, Nat.succ_eq_add_one, Nat.choose_zero_right,
    Finset.sum_add_distrib]
  omega

/-- The Ehrenfeucht–Haussler rank of a binary decision tree: leaves have rank zero, a node
with unequal child ranks has their maximum, and equal child ranks `r` give rank `r + 1`. -/
def rank : DecisionTree ι β → ℕ
  | .leaf _ => 0
  | .node _ left right =>
    if left.rank = right.rank then left.rank + 1 else max left.rank right.rank

@[simp]
theorem rank_leaf (b : β) : (leaf b : DecisionTree ι β).rank = 0 :=
  rfl

theorem rank_node (i : ι) (left right : DecisionTree ι β) :
    (node i left right).rank =
      if left.rank = right.rank then left.rank + 1 else max left.rank right.rank :=
  rfl

/-- Relabelling queries preserves the rank. -/
@[simp]
theorem rank_mapQueries {κ : Type*} (f : ι → κ) (t : DecisionTree ι β) :
    (t.mapQueries f).rank = t.rank := by
  induction t with
  | leaf => rfl
  | node i left right ihl ihr => simp [mapQueries, rank, ihl, ihr]

/-- The rank of a decision tree is at most its depth. -/
theorem rank_le_depth (t : DecisionTree ι β) : t.rank ≤ t.depth := by
  induction t with
  | leaf => rfl
  | node _ left right ihl ihr =>
    simp only [rank, depth_node]
    split_ifs <;> omega

/-- A decision tree of rank at most `r` and depth at most `d` has at most
`∑ j ∈ Finset.range (r + 1), d.choose j` structural leaves. -/
theorem leafCount_le_sum_choose_of_rank_le (t : DecisionTree ι β) {r d : ℕ}
    (hr : t.rank ≤ r) (hd : t.depth ≤ d) :
    t.leafCount ≤ ∑ j ∈ Finset.range (r + 1), d.choose j := by
  induction t generalizing r d with
  | leaf =>
    rw [Finset.sum_range_succ']
    simp [leafCount]
  | node _ left right ihl ihr =>
    simp only [depth_node] at hd
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have hld : left.depth ≤ d' := by omega
    have hrd : right.depth ≤ d' := by omega
    simp only [rank] at hr
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by split_ifs at hr <;> omega⟩
    by_cases hle : left.rank ≤ right.rank
    · have hlr : left.rank ≤ r' := by split_ifs at hr <;> omega
      have hrr : right.rank ≤ r' + 1 := by split_ifs at hr <;> omega
      have hl := ihl hlr hld
      have hr' := ihr hrr hrd
      simp only [leafCount, ← sum_choose_succ_add]
      omega
    · have hlr : left.rank ≤ r' + 1 := by split_ifs at hr <;> omega
      have hrr : right.rank ≤ r' := by split_ifs at hr <;> omega
      have hl := ihl hlr hld
      have hr' := ihr hrr hrd
      simp only [leafCount, ← sum_choose_succ_add]
      omega

/-- A decision tree of depth `d` and rank `r` has at most
`∑ j ∈ Finset.range (r + 1), d.choose j` structural leaves. -/
theorem leafCount_le_sum_choose_rank (t : DecisionTree ι β) :
    t.leafCount ≤ ∑ j ∈ Finset.range (t.rank + 1), t.depth.choose j :=
  t.leafCount_le_sum_choose_of_rank_le le_rfl le_rfl

/-- A decision tree of rank at most `1` has at most `depth + 1` structural leaves. -/
theorem leafCount_le_depth_add_one_of_rank_le_one (t : DecisionTree ι β) (hr : t.rank ≤ 1) :
    t.leafCount ≤ t.depth + 1 := by
  have h := t.leafCount_le_sum_choose_of_rank_le hr le_rfl
  rw [Finset.sum_range_succ, Finset.sum_range_one, Nat.choose_zero_right,
    Nat.choose_one_right] at h
  omega

/-- A decision tree of rank at most `1` has at most `depth` internal nodes. -/
theorem nodeCount_le_depth_of_rank_le_one (t : DecisionTree ι β) (hr : t.rank ≤ 1) :
    t.nodeCount ≤ t.depth := by
  have h := t.leafCount_le_depth_add_one_of_rank_le_one hr
  have hleaf := t.leafCount_eq_nodeCount_add_one
  omega

/-- A binary decision tree is a decision list when every internal node has at least one leaf
child (`leafCount = 1`). -/
def IsDecisionList : DecisionTree ι β → Prop
  | .leaf _ => True
  | .node _ left right =>
    (left.leafCount = 1 ∧ right.IsDecisionList) ∨ (right.leafCount = 1 ∧ left.IsDecisionList)

/-- A tree with a single structural leaf has rank zero. -/
theorem rank_eq_zero_of_leafCount_eq_one {t : DecisionTree ι β} (h : t.leafCount = 1) :
    t.rank = 0 := by
  cases t with
  | leaf => rfl
  | node _ left right =>
    have hl := left.leafCount_pos
    have hr := right.leafCount_pos
    simp only [leafCount] at h
    omega

/-- Every decision list has Ehrenfeucht–Haussler rank at most `1`. -/
theorem IsDecisionList.rank_le_one {t : DecisionTree ι β} (h : t.IsDecisionList) :
    t.rank ≤ 1 := by
  induction t with
  | leaf => exact Nat.zero_le 1
  | node _ left right ihl ihr =>
    simp only [rank]
    rcases h with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · have hl0 := rank_eq_zero_of_leafCount_eq_one hl
      have hr1 := ihr hr
      split_ifs <;> omega
    · have hr0 := rank_eq_zero_of_leafCount_eq_one hr
      have hl1 := ihl hl
      split_ifs <;> omega

/-- A decision list has at most `depth + 1` structural leaves. -/
theorem IsDecisionList.leafCount_le_depth_add_one {t : DecisionTree ι β} (h : t.IsDecisionList) :
    t.leafCount ≤ t.depth + 1 :=
  t.leafCount_le_depth_add_one_of_rank_le_one h.rank_le_one

/-- A decision list has at most `depth` internal nodes. -/
theorem IsDecisionList.nodeCount_le_depth {t : DecisionTree ι β} (h : t.IsDecisionList) :
    t.nodeCount ≤ t.depth :=
  t.nodeCount_le_depth_of_rank_le_one h.rank_le_one

/-- Relabelling queries preserves decision-list structure. -/
theorem IsDecisionList.mapQueries {κ : Type*} (f : ι → κ) {t : DecisionTree ι β}
    (h : t.IsDecisionList) : (t.mapQueries f).IsDecisionList := by
  induction t with
  | leaf => trivial
  | node _ left right ihl ihr =>
    rcases h with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · exact Or.inl ⟨by simpa using hl, ihr hr⟩
    · exact Or.inr ⟨by simpa using hr, ihl hl⟩

/-- The energy of a binary decision tree: the maximum number of `true` (right) branches on a
root-to-leaf path. -/
def energy : DecisionTree ι β → ℕ
  | .leaf _ => 0
  | .node _ left right => max left.energy (right.energy + 1)

@[simp]
theorem energy_leaf (b : β) : (leaf b : DecisionTree ι β).energy = 0 :=
  rfl

theorem energy_node (i : ι) (left right : DecisionTree ι β) :
    (node i left right).energy = max left.energy (right.energy + 1) :=
  rfl

/-- Relabelling queries preserves the energy. -/
@[simp]
theorem energy_mapQueries {κ : Type*} (f : ι → κ) (t : DecisionTree ι β) :
    (t.mapQueries f).energy = t.energy := by
  induction t with
  | leaf => rfl
  | node i left right ihl ihr => simp [mapQueries, energy, ihl, ihr]

/-- The energy of a decision tree is at most its depth. -/
theorem energy_le_depth (t : DecisionTree ι β) : t.energy ≤ t.depth := by
  induction t with
  | leaf => rfl
  | node _ left right ihl ihr =>
    simp only [energy, depth_node]
    omega

/-- A decision tree of energy at most `e` and depth at most `d` has at most
`∑ j ∈ Finset.range (e + 1), d.choose j` structural leaves. -/
theorem leafCount_le_sum_choose_of_energy_le (t : DecisionTree ι β) {e d : ℕ}
    (he : t.energy ≤ e) (hd : t.depth ≤ d) :
    t.leafCount ≤ ∑ j ∈ Finset.range (e + 1), d.choose j := by
  induction t generalizing e d with
  | leaf =>
    rw [Finset.sum_range_succ']
    simp [leafCount]
  | node _ left right ihl ihr =>
    simp only [depth_node] at hd
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have hld : left.depth ≤ d' := by omega
    have hrd : right.depth ≤ d' := by omega
    simp only [energy] at he
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have hle : left.energy ≤ e' + 1 := by omega
    have hre : right.energy ≤ e' := by omega
    have hl := ihl hle hld
    have hr := ihr hre hrd
    simp only [leafCount, ← sum_choose_succ_add]
    omega

/-- A decision tree of depth `d` and energy `e` has at most
`∑ j ∈ Finset.range (e + 1), d.choose j` structural leaves. -/
theorem leafCount_le_sum_choose_energy (t : DecisionTree ι β) :
    t.leafCount ≤ ∑ j ∈ Finset.range (t.energy + 1), t.depth.choose j :=
  t.leafCount_le_sum_choose_of_energy_le le_rfl le_rfl

end Cslib.DecisionTree
