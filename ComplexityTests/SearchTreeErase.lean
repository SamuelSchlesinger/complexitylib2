/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.SearchTree.Erase
public import ComplexityTests.SearchTree

/-!
# Worked search-tree deletion examples

Delete keys from the balanced-looking and the right-spine trees of `ComplexityTests.SearchTree`.
Deleting the root of the height-three tree promotes its successor from the right subtree; deleting
from the spine walks the whole search path. Absent keys leave the tree unchanged. All computation
is checked by the kernel, with no `native_decide`.
-/

@[expose] public section

namespace ComplexityTests.SearchTreeErase

open Cslib.Algorithms.Lean.SearchTree ComplexityTests.SearchTree

def medianFirst : BinaryTree Nat := build [4, 2, 6, 1, 3, 5, 7]
def sortedFirst : BinaryTree Nat := build [1, 2, 3, 4, 5, 6, 7]

-- Deleting the root replaces it by its successor, the leftmost key of the right subtree.
example : erase 4 medianFirst =
    .node 5 (.node 2 (.node 1 .nil .nil) (.node 3 .nil .nil)) (.node 6 .nil (.node 7 .nil .nil)) :=
  rfl
example : elements (erase 4 medianFirst) = {1, 2, 3, 5, 6, 7} := by decide
example : elements (erase 4 medianFirst) = (elements medianFirst).erase 4 :=
  elements_erase (ordered_build _) 4
example : Ordered (erase 4 medianFirst) := ordered_erase (ordered_build _) 4
example : eraseVisits 4 medianFirst = 3 := rfl

-- On the right spine, deletion walks the search path plus one successor visit.
example : eraseVisits 4 sortedFirst = 5 := rfl
example : eraseVisits 7 sortedFirst = 7 := rfl
example : (erase 4 sortedFirst).height = 6 := rfl
example : (erase 7 sortedFirst).height = 6 := rfl
example : contains 4 (erase 4 sortedFirst) = false := rfl
example : contains 5 (erase 4 sortedFirst) = true := rfl

-- A leaf or a node without a right subtree is spliced out directly.
example : erase 1 medianFirst =
    .node 4 (.node 2 .nil (.node 3 .nil .nil)) (.node 6 (.node 5 .nil .nil) (.node 7 .nil .nil)) :=
  rfl
example : erase 5 (build [5]) = .nil := rfl
example : erase 5 (build [5, 3]) = .node 3 .nil .nil := rfl

-- Deleting an absent key preserves shape as well as contents, including on the empty tree.
example : erase 8 medianFirst = medianFirst := rfl
example : erase 8 medianFirst = medianFirst := erase_eq_self (by decide)
example : erase 0 (.nil : BinaryTree Nat) = .nil := rfl
example : eraseVisits 8 sortedFirst = 7 := rfl

-- Deletion followed by reinsertion restores the set, though not necessarily the shape.
example : elements (insert 4 (erase 4 medianFirst)) = elements medianFirst := by decide
example : insert 4 (erase 4 medianFirst) ≠ medianFirst := by decide

/--
info: 'Cslib.Algorithms.Lean.SearchTree.elements_erase' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Algorithms.Lean.SearchTree.elements_erase
/--
info: 'Cslib.Algorithms.Lean.SearchTree.ordered_erase' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Algorithms.Lean.SearchTree.ordered_erase
/--
info: 'Cslib.Algorithms.Lean.SearchTree.eraseVisits_le_height' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Algorithms.Lean.SearchTree.eraseVisits_le_height
/--
info: 'Cslib.Algorithms.Lean.SearchTree.height_erase_le' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Algorithms.Lean.SearchTree.height_erase_le

end ComplexityTests.SearchTreeErase
