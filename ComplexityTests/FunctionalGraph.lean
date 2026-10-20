/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.FunctionalGraph.CheckpointForest
import Complexity.Foundations.Combinatorics.FunctionalGraph.ForestIntervals
import Complexity.Foundations.Combinatorics.FunctionalGraph.ForestNavigation
import Complexity.Foundations.Combinatorics.FunctionalGraph.ForestSegments

/-!
# Checkpoint forest, interval label, segment, and navigation tests

Exercise `checkpointHull`, `forestMarks`, `forestPath`, `exists_forest_intervals`, `IsForestEdge`,
`ForestAnchor`, `ForestEdgeTable`, and `forest_navigation_spec` on concrete finite functional
graphs, and guard the axioms of all headline declarations.
-/

namespace ComplexityTests.FunctionalGraph

open Cslib Cslib.FunctionalGraph Function

/-! ### Concrete functional graph: `toZero` on `Fin 2` -/

/-- Constant map `x ↦ 0` on `Fin 2`: `0` is periodic (`transientDepth = 0`) and `1` is transient
(`transientDepth = 1`). -/
private def toZero : Fin 2 → Fin 2 := fun _ => 0

private theorem transientDepth_toZero_zero : transientDepth toZero 0 = 0 := by
  have h0 : (0 : Fin 2) ∈ periodicPts toZero := mk_mem_periodicPts one_pos rfl
  exact (transientDepth_eq_zero_iff toZero 0).mpr h0

private theorem transientDepth_toZero_one : transientDepth toZero 1 = 1 := by
  have h0 : toZero^[1] 1 ∈ periodicPts toZero := mk_mem_periodicPts one_pos rfl
  have h1 : (1 : Fin 2) ∉ periodicPts toZero := by
    rintro ⟨p, hp, hper⟩
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    have hstep : toZero^[k + 1] 1 = 0 := by rw [iterate_succ_apply']; rfl
    exact absurd (hstep.symm.trans hper.eq) (by decide)
  have hle := (iterate_mem_periodicPts_iff toZero 1 1).mp h0
  have hpos : transientDepth toZero 1 ≠ 0 := fun h => h1 ((transientDepth_eq_zero_iff _ _).mp h)
  omega

-- Refine checkpoint `{1}`: the hull contains `0` and `1`, and `forestMarks` has size at most `2`.
example : (1 : Fin 2) ∈ checkpointHull toZero {1} ∧ (0 : Fin 2) ∈ checkpointHull toZero {1} ∧
    (forestMarks toZero {1}).card ≤ 2 := by
  have h1 : (1 : Fin 2) ∈ checkpointHull toZero {1} :=
    subset_checkpointHull toZero {1} (Finset.mem_singleton_self 1)
  refine ⟨h1, ?_, ?_⟩
  · have h := checkpointHull_iterate toZero {1} h1 (t := 1) (by rw [transientDepth_toZero_one])
    simpa [toZero] using h
  · simpa using forestMarks_card toZero {1}

-- Concrete `IsForestEdge` instance from `1` to `0` of length `1`.
example : IsForestEdge toZero {1} 1 1 where
  start_mem := subset_forestMarks toZero {1} (by simp)
  pos := one_pos
  le_depth := by rw [transientDepth_toZero_one]
  end_mem := by
    have h1 : (1 : Fin 2) ∈ checkpointHull toZero {1} := subset_checkpointHull toZero {1} (by simp)
    have h := forest_cycle_entry_mem toZero {1} h1
    rwa [transientDepth_toZero_one] at h
  interior i hi1 hi2 := by omega

-- Non-vacuous `ForestEdgeTable` instance for `toZero` with `H = Finset.univ` and `L = 1`.
noncomputable def sampleForestEdgeTable : ForestEdgeTable toZero Finset.univ 1 :=
  Classical.choice (exists_forest_edge_table toZero Finset.univ 1 one_pos
    (fun x => Or.inr ⟨0, by decide, Finset.mem_univ _⟩))

example : sampleForestEdgeTable.count ≤ (forestMarks toZero Finset.univ).card :=
  sampleForestEdgeTable.card_le

-- Interval labels distinguish ancestors before cycle entry on `toZero`.
example : ∃ low high : Fin 2 → Fin (Nat.card (Fin 2)),
    ∀ x y, (low y ≤ low x ∧ low x ≤ high y) ↔
      ∃ t ≤ transientDepth toZero x, toZero^[t] x = y :=
  exists_forest_intervals toZero

/-! ### Axioms -/

/--
info: 'Cslib.FunctionalGraph.forestBranches_roots_le_leaves' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms forestBranches_roots_le_leaves

/--
info: 'Cslib.FunctionalGraph.forestMarks_card' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms forestMarks_card

/--
info: 'Cslib.FunctionalGraph.forestPredecessor_unique' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms forestPredecessor_unique

/--
info: 'Cslib.FunctionalGraph.forestPath_prefix' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms forestPath_prefix

/--
info: 'Cslib.FunctionalGraph.forest_interval_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms forest_interval_spec

/--
info: 'Cslib.FunctionalGraph.exists_forest_intervals' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_forest_intervals

/--
info: 'Cslib.FunctionalGraph.exists_short_forest_edge' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_short_forest_edge

/--
info: 'Cslib.FunctionalGraph.forest_edges_merge' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms forest_edges_merge

/--
info: 'Cslib.FunctionalGraph.forest_edge_last_injective' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms forest_edge_last_injective

/--
info: 'Cslib.FunctionalGraph.forest_hull_partition' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms forest_hull_partition

/--
info: 'Cslib.FunctionalGraph.exists_forest_anchor' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_forest_anchor

/--
info: 'Cslib.FunctionalGraph.forestAnchor_unique' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms forestAnchor_unique

/--
info: 'Cslib.FunctionalGraph.forest_navigation_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms forest_navigation_spec

/--
info: 'Cslib.FunctionalGraph.exists_forest_edge_table' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_forest_edge_table

/--
info: 'Cslib.FunctionalGraph.ForestEdgeTable.anchor_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ForestEdgeTable.anchor_iff

end ComplexityTests.FunctionalGraph
