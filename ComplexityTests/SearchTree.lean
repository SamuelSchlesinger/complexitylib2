/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.SearchTree.Stateful

/-!
# Worked search-tree examples

Insert the same seven keys in two orders. The median-first order happens to produce height three;
sorted insertion produces a right spine of height seven. This implementation does not rebalance.
The exact node-visit counts expose that difference without claiming machine instruction costs.

The final examples execute `firstTwo`: its successor argument comes from the minimum it observed,
so the query history differs between an empty and a nonempty set. All computation is checked by
the kernel, with no `native_decide`.
-/

@[expose] public section

namespace ComplexityTests.SearchTree

open Cslib.Algorithms.Lean.SearchTree Cslib.Stateful

def build (xs : List Nat) : BinaryTree Nat := (run .nil (insertAll xs)).2.1

private def medianFirst : BinaryTree Nat := build [4, 2, 6, 1, 3, 5, 7]
private def sortedFirst : BinaryTree Nat := build [1, 2, 3, 4, 5, 6, 7]

theorem ordered_build (xs : List Nat) : Ordered (build xs) :=
  (run_correct (insertAll xs) rep_empty).2.1.1

-- These shapes represent exactly the same set, with satisfiable strict ordering invariants.
example : Ordered medianFirst := ordered_build _
example : Ordered sortedFirst := ordered_build _
example : elements medianFirst = elements sortedFirst := by decide
example : (elements medianFirst).card = 7 := by decide
example : medianFirst.height = 3 := rfl
example : sortedFirst.height = 7 := rfl

-- Searching for the maximum or for a missing larger key traverses three versus seven nodes.
example : contains 7 medianFirst = true := rfl
example : contains 8 medianFirst = false := rfl
example : searchVisits 7 medianFirst = 3 := rfl
example : searchVisits 7 sortedFirst = 7 := rfl
example : searchVisits 8 medianFirst = 3 := rfl
example : searchVisits 8 sortedFirst = 7 := rfl
example : (insert 8 sortedFirst).height = 8 := rfl

-- Duplicate insertion preserves shape as well as contents.
example : insert 4 medianFirst = medianFirst := rfl
example : insert 4 medianFirst = medianFirst :=
  insert_eq_self (ordered_build _) (by decide)

-- Successor is strict, can start from an absent key, and reports exhaustion.
example : minimum medianFirst = some 1 := rfl
example : successor 0 medianFirst = some 1 := rfl
example : successor 4 medianFirst = some 5 := rfl
example : successor 7 medianFirst = none := rfl
example : successor 100 medianFirst = none := rfl
example : successor 3 (build [2, 4, 6]) = some 4 := rfl
example : successor 4 (build [2, 4, 6]) = some 6 := rfl
example : successorVisits 7 sortedFirst = 7 := rfl
example : minimumVisits sortedFirst = 1 := rfl

-- Empty queries and singleton boundaries are total.
example : minimum (.nil : BinaryTree Nat) = none := rfl
example : successor 0 (.nil : BinaryTree Nat) = none := rfl
example : searchVisits 0 (.nil : BinaryTree Nat) = 0 := rfl
example : run (.nil : BinaryTree Nat) (.liftBind (.insert 5) .pure) =
    ((), BinaryTree.node 5 .nil .nil, [0]) := rfl
example : successor 5 (build [5]) = none := rfl
example : successor 4 (build [5]) = some 5 := rfl

-- The exact native trace counts minimum and the answer-dependent successor separately.
example : (run medianFirst firstTwo).1 = (some 1, some 2) := rfl
example : (run medianFirst firstTwo).2.2 = [3, 3] := rfl
example : (run sortedFirst firstTwo).1 = (some 1, some 2) := rfl
example : (run sortedFirst firstTwo).2.2 = [1, 2] := rfl
example : (run (.nil : BinaryTree Nat) firstTwo).1 = (none, none) := rfl
example : (run (.nil : BinaryTree Nat) firstTwo).2.2 = [0] := rfl
example : (run (build [5]) firstTwo).1 = (some 5, none) := rfl

-- Native computation and finite-set semantics agree through the shared realization theorem.
example : (run medianFirst firstTwo).1 =
    ((orderedSet Nat).runClient (elements medianFirst) firstTwo).1 :=
  (run_correct firstTwo ⟨ordered_build _, rfl⟩).1

example (xs : List Nat) :
    ∃ t ns, Executes Exec ((insertAll xs).bind fun _ => firstTwo) .nil
        ((orderedSet Nat).runClient ∅ ((insertAll xs).bind fun _ => firstTwo)).1 t ns ∧
      Rep ((orderedSet Nat).runClient ∅ ((insertAll xs).bind fun _ => firstTwo)).2.1 t ∧
      total id ns ≤ (orderedSet Nat).totalCost (fun s _ => s.card) ∅
        ((orderedSet Nat).runClient ∅ ((insertAll xs).bind fun _ => firstTwo)).2.2 :=
  realized_client _ rep_empty

-- A malformed tree demonstrates why query correctness requires Ordered.
private def malformed : BinaryTree Nat := .node 0 (.node 1 .nil .nil) .nil
example : 1 ∈ elements malformed := by decide
example : contains 1 malformed = false := rfl
example : ¬ Ordered malformed := by simp [malformed, Ordered, elements]

-- A finite-set/cardinality bound must not be mistaken for a logarithmic-height assertion.
example : ¬ sortedFirst.height ≤ 3 := by decide

/--
info: 'Cslib.Algorithms.Lean.SearchTree.ordered_insert' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Algorithms.Lean.SearchTree.ordered_insert
/--
info: 'Cslib.Algorithms.Lean.SearchTree.minimum_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Algorithms.Lean.SearchTree.minimum_spec
/--
info: 'Cslib.Algorithms.Lean.SearchTree.successor_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Algorithms.Lean.SearchTree.successor_spec
/--
info: 'Cslib.Algorithms.Lean.SearchTree.exec_visits_le_height' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Algorithms.Lean.SearchTree.exec_visits_le_height
/--
info: 'Cslib.Algorithms.Lean.SearchTree.run_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Algorithms.Lean.SearchTree.run_correct

end ComplexityTests.SearchTree
