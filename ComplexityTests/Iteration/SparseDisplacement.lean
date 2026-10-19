/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Iteration.SparseDisplacement
import Mathlib.Tactic.FinCases

/-!
# Sparse-counter circuit clients

Check zero-width words, wraparound cuts, an edited counter, negative powers, and charged
identity coordinates. A noninjective example shows why the factor-two theorem needs injectivity.
-/

namespace ComplexityTests.Iteration.SparseDisplacement

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Iteration
open Cslib.FunctionalGraph

-- At width zero there is one state, and its displacement never changes.
example : displacementCuts (id : BitVec 0 → BitVec 0) = ∅ := by decide

-- Negation has displacement changes at all four edges, including the wraparound edge.
example : displacementCuts (fun x : BitVec 2 => -x) = {0, 1, 2, 3} := by decide

example : thresholdSum (displacementCuts (fun x : BitVec 2 => -x))
    (fun i => displacement (fun x : BitVec 2 => -x) (BitVec.ofNat 2 (i + 1)) -
      displacement (fun x : BitVec 2 => -x) (BitVec.ofNat 2 i))
    (displacement (fun x : BitVec 2 => -x) 0) 3 = 2 := by decide

-- Swapping two counter inputs gives a permutation edited at exactly two successors.
private def editedCounter : Equiv.Perm (BitVec 2) :=
  (Equiv.swap 0 1).trans (Equiv.addRight 1)

private theorem editedCounter_disagreement [Fintype (BitVec 2)] :
    disagreement editedCounter (fun x => x + 1) = {0, 1} := by
  ext x
  simp only [mem_disagreement, Finset.mem_insert, Finset.mem_singleton]
  revert x
  decide

-- The same bound works for every signed exponent, including inverses.
example (T : ℤ) : ∃ out : Circuit signature 2 2,
    out.Computes interpretation (fun x i => ((editedCounter ^ T) (word x)).getLsbD i.val) ∧
    out.size ≤ 900 := by
  have h := sparse_counter_power editedCounter T
  rw [editedCounter_disagreement] at h
  simpa using h

example : ∃ out : Circuit signature 2 2,
    out.Computes interpretation (fun x i => (editedCounter.symm (word x)).getLsbD i.val) ∧
    out.size ≤ 900 := by
  have h := sparse_counter_power editedCounter (-1)
  rw [editedCounter_disagreement] at h
  simpa using h

-- Coordinate transfer is applicable to actual conversion circuits.
example (T : ℤ) : ∃ out : Circuit signature 2 2,
    out.Computes interpretation (fun x i => ((editedCounter ^ T) (word x)).getLsbD i.val) ∧
    out.size ≤ 900 := by
  have hid : (Circuit.id signature 2).Computes interpretation
      (fun x i => ((Equiv.refl (BitVec 2)) (word x)).getLsbD i.val) := by
    intro x
    funext i
    exact (getLsbD_word x i).symm
  have h := sparse_coordinate_power editedCounter (Equiv.addRight 1) (Equiv.refl _)
      (fun _ => rfl) (Circuit.id signature 2) (Circuit.id signature 2) hid hid T
  have hdiff : disagreement editedCounter (Equiv.addRight (1 : BitVec 2)) = {0, 1} :=
    editedCounter_disagreement
  rw [hdiff] at h
  simpa using h

-- Without injectivity one edited input can create four defects.
private def edit (x : Fin 4) : Fin 4 := if x = 0 then 1 else x

example : Function.Commute (fun _ : Fin 4 => 0) id := fun _ => rfl

example : disagreement id edit = {0} := by
  ext x
  fin_cases x <;> simp [mem_disagreement, edit]

example : disagreement ((fun _ : Fin 4 => 0) ∘ edit) (edit ∘ (fun _ => 0)) = Finset.univ := by
  ext x
  simp [mem_disagreement, edit]

/--
info: 'Cslib.FunctionalGraph.commutation_defect_card' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.FunctionalGraph.commutation_defect_card

/--
info: 'Cslib.Circuits.Boolean.Iteration.thresholdSum_displacement' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Iteration.thresholdSum_displacement

/--
info: 'Cslib.Circuits.Boolean.Iteration.sparse_counter_centralizer' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Iteration.sparse_counter_centralizer

/--
info: 'Cslib.Circuits.Boolean.Iteration.sparse_counter_power' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Iteration.sparse_counter_power

/--
info: 'Cslib.Circuits.Boolean.Iteration.sparse_coordinate_power' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Iteration.sparse_coordinate_power


end ComplexityTests.Iteration.SparseDisplacement
