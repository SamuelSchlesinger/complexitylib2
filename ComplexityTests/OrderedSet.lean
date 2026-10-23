/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Foundations.Semantics.Stateful.OrderedSet

/-!
# Representation-independent ordered-set clients

This driver imports only the neutral interface, with no search-tree implementation or cost
module. Finite keys demonstrate that the interface is not restricted to natural-number storage.
A validity specialization shows the intended bounded-key contract without assuming a vEB
implementation or any cost theorem.
-/

@[expose] public section

namespace ComplexityTests.OrderedSet

open Cslib.OrderedSet Cslib.Stateful

-- The absence contract is complete, including exhaustion above the largest key.
example : LeastResult (∅ : Finset (Fin 3)) none := rfl
example : ¬ LeastResult ({1} : Finset (Fin 3)) none := by
  simp [LeastResult]
example : least ({0, 2} : Finset (Fin 3)) = some 0 := by decide
example : (spec (Fin 3)).step {0, 2} (.successor 1) = ({0, 2}, some 2) := by decide
example : (spec (Fin 3)).step {0, 2} (.successor 2) = ({0, 2}, none) := by decide

-- The same adaptive client can be interpreted without choosing a data structure.
example : (spec (Fin 3)).runClient ∅ firstTwo = ((none, none), ∅, [.minimum]) := by decide
example : (spec (Fin 3)).runClient {0, 2} firstTwo =
    ((some 0, some 2), {0, 2}, [.minimum, .successor 0]) := by decide
example : ((spec (Fin 3)).runClient ∅ (insertAll [2, 0, 2])).2.1 = {0, 2} := by decide

-- The general theorem keeps pre-existing keys and repeated operations in their original order.
example (s : Finset (Fin 3)) : (spec (Fin 3)).runClient s (insertAll []) = ((), s, []) := by
  simpa using insertAll_run s []
example : (spec (Fin 3)).runClient {1} (insertAll [2, 0, 2]) =
    ((), {0, 1, 2}, [.insert 2, .insert 0, .insert 2]) := by
  rw [insertAll_run]
  decide
example (s : Finset (Fin 3)) (xs ys : List (Fin 3)) :
    ((spec (Fin 3)).runClient s (insertAll (xs ++ ys))).2.2 =
      xs.map Op.insert ++ ys.map Op.insert := by
  simp only [insertAll_run, List.map_append]

/-- A later bounded-key realization can restrict insertion while leaving all queries admissible. -/
abbrev bounded (bound : Nat) : Spec :=
  { spec Nat with valid := fun _ o => match o with
      | .insert x => x < bound
      | _ => True }

example : ¬ (bounded 4).valid ∅ (.insert 4) := by decide
example : (bounded 4).valid ∅ (.contains 99) := trivial
example : (bounded 4).valid ∅ (.successor 99) := trivial
example : (spec Nat).valid ∅ (.insert 99) := trivial

/--
info: 'Cslib.OrderedSet.least_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.OrderedSet.least_spec
/--
info: 'Cslib.OrderedSet.LeastResult.eq_least' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.OrderedSet.LeastResult.eq_least
/--
info: 'Cslib.OrderedSet.insertAll_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.OrderedSet.insertAll_run

end ComplexityTests.OrderedSet
