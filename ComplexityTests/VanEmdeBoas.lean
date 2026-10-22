/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.VanEmdeBoas.Elements

/-!
Boundary and adaptive examples for the recursive vEB algorithms. These evaluate Lean functions;
they do not measure or certify RAM running time.
-/

open Cslib.Algorithms.Lean.VanEmdeBoas

@[expose] public section

namespace ComplexityTests.VanEmdeBoas

private def ofList (d : ℕ) (xs : List ℕ) : Tree d :=
  xs.foldl Tree.insert (Tree.empty d)

private def membership (d : ℕ) (xs : List ℕ) : List Bool :=
  (List.range (universeSize d + 1)).map (ofList d xs).member

private def successors (d : ℕ) (xs : List ℕ) : List (Option ℕ) :=
  (List.range (universeSize d + 1)).map (ofList d xs).successor

/-- The representation invariant has a concrete instance at every supported universe size. -/
theorem empty_valid (d : ℕ) : (Tree.empty d).Valid := Tree.valid_empty d

example : (ofList 2 [15, 12, 8, 4, 0, 15]).Valid := by
  unfold ofList
  simp only [List.foldl_cons, List.foldl_nil]
  iterate 6 apply Tree.valid_insert (hx := by decide)
  exact Tree.valid_empty 2

example : membership 0 [] = [false, false, false] := by decide
example : successors 0 [] = [none, none, none] := by decide
example : membership 0 [0, 0] = [true, false, false] := by decide
example : successors 0 [0, 0] = [none, none, none] := by decide
example : membership 0 [1, 1] = [false, true, false] := by decide
example : successors 0 [1, 1] = [some 1, none, none] := by decide
example : membership 0 [1, 0, 1, 0] = [true, true, false] := by decide
example : successors 0 [1, 0, 1, 0] = [some 1, none, none] := by decide

-- Descending minima move the old minimum into previously empty clusters.
example : membership 2 [15, 12, 8, 4, 0] =
    [true, false, false, false, true, false, false, false, true, false, false, false,
      true, false, false, true, false] := by decide

example : successors 2 [15, 12, 8, 4, 0] =
    [some 4, some 4, some 4, some 4, some 8, some 8, some 8, some 8,
      some 12, some 12, some 12, some 12, some 15, some 15, some 15, none, none] := by decide

-- Minimum, maximum and interior duplicates preserve the set and all strict answers.
example : membership 2 [8, 4, 12, 2, 10, 0, 15, 8, 4, 12, 2, 10, 0, 15] =
    membership 2 [0, 2, 4, 8, 10, 12, 15] := by decide

example : successors 2 [8, 4, 12, 2, 10, 0, 15, 8, 4, 12, 2, 10, 0, 15] =
    successors 2 [0, 2, 4, 8, 10, 12, 15] := by decide

private def adaptive (choosePresent : Bool) : Bool × Option ℕ × Bool :=
  let t := ofList 2 [7, 12]
  let first := if choosePresent then 7 else 3
  let t := if t.member first then t.insert 0 else t.insert first
  let next := t.successor 2
  let t := match next with
    | some x => t.insert (x - 1)
    | none => t.insert 15
  (t.member 0, next, t.member 2)

example : adaptive true = (true, some 7, false) := by decide
example : adaptive false = (false, some 3, true) := by decide

private def histories : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (List.range 4).flatMap fun x => (histories n).map (x :: ·)

private def agrees (xs : List ℕ) : Bool :=
  let t := ofList 1 xs
  (List.range 5).all fun x =>
    t.member x == xs.contains x &&
      t.successor x == ((List.range 4).filter fun y => xs.contains y && x < y).head?

-- All 256 four-insertion histories over the four-key universe, including duplicates.
example : (histories 3).all (fun xs => agrees (0 :: xs)) = true := by decide
example : (histories 3).all (fun xs => agrees (1 :: xs)) = true := by decide
example : (histories 3).all (fun xs => agrees (2 :: xs)) = true := by decide
example : (histories 3).all (fun xs => agrees (3 :: xs)) = true := by decide

/--
info: 'Cslib.Algorithms.Lean.VanEmdeBoas.Tree.valid_empty' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tree.valid_empty
/--
info: 'Cslib.Algorithms.Lean.VanEmdeBoas.Tree.member_iff_contains' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tree.member_iff_contains
/--
info: 'Cslib.Algorithms.Lean.VanEmdeBoas.Tree.valid_insert' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tree.valid_insert
/--
info: 'Cslib.Algorithms.Lean.VanEmdeBoas.Tree.elements_insert' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tree.elements_insert
/--
info: 'Cslib.Algorithms.Lean.VanEmdeBoas.Tree.successor_eq_some_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tree.successor_eq_some_iff
/--
info: 'Cslib.Algorithms.Lean.VanEmdeBoas.Tree.successor_eq_none_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tree.successor_eq_none_iff
/--
info: 'Cslib.Algorithms.Lean.VanEmdeBoas.span_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms span_le

end ComplexityTests.VanEmdeBoas
