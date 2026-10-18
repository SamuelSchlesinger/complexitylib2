/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

import Complexity.Algorithms.Reachability.Savitch

/-!
# Tests: Savitch's midpoint reachability

The binary counter on the words of width two; the midpoint recursion and the stack machine on a
directed path through them, on a graph whose target is unreachable, and on the trivial walk at
depth zero; walks of the path through `Cslib.Reachability.savitch_iff`; instances of the
quantitative certificate and of its polynomial-space form for a family of depths, so that their
hypotheses are satisfiable; and the axioms of the headline theorems.
-/

namespace ComplexityTests.Savitch

open Cslib Cslib.Reachability Turing.MultiTapeTM

/-! ### The binary counter -/

example : words 2 = [[false, false], [true, false], [false, true], [true, true]] := by decide

example : words 0 = [[]] := rfl

example : next [true, true] = none := rfl

example : next [true, false, true] = some [false, true, true] := rfl

/-! ### A directed path -/

/-- The path `00 → 10 → 01 → 11` through the words of width two, in counter order. -/
def path (u v : List Bool) : Bool := decide (next u = some v)

-- At level `i`, the walks of at most `2 ^ i` steps.
example : reach path 2 0 [false, false] [true, false] = true := by decide

example : reach path 2 0 [false, false] [false, true] = false := by decide

example : reach path 2 1 [false, false] [false, true] = true := by decide

example : reach path 2 1 [false, false] [true, true] = false := by decide

example : reach path 2 2 [false, false] [true, true] = true := by decide

-- The path is directed.
example : reach path 2 3 [true, true] [false, false] = false := by decide

-- The machine itself, run for `2 ^ 8 - 1` steps by the kernel.
example : savitch path 2 1 [false, false] [false, true] = true := by decide +kernel

example : savitch path 2 1 [false, false] [true, true] = false := by decide +kernel

-- At depth two the machine runs for `2 ^ 12 - 1` steps; the correctness theorem shortcuts them.
example : savitch path 2 2 [false, false] [true, true] = true := by
  rw [savitch_eq]
  decide

example : Relation.RelatesWithinSteps
    (fun a b => a.length = 2 ∧ b.length = 2 ∧ path a b = true) [false, false] [true, true]
    (2 ^ 2) :=
  (savitch_iff (w := 2) (u := [false, false]) (v := [true, true]) rfl rfl).mp
    (by rw [savitch_eq]; decide)

example : ¬Relation.RelatesWithinSteps
    (fun a b => a.length = 2 ∧ b.length = 2 ∧ path a b = true) [false, false] [true, true]
    (2 ^ 1) := by
  rw [← savitch_iff (w := 2) (u := [false, false]) (v := [true, true]) rfl rfl]
  decide +kernel

/-! ### An unreachable target -/

/-- Edges between the words with the same last bit: `{00, 10}` and `{01, 11}` are disconnected. -/
def halves (u v : List Bool) : Bool := decide (u.getLast? = v.getLast?)

example : reach halves 2 1 [false, false] [true, false] = true := by decide

example : reach halves 2 3 [false, false] [true, true] = false := by decide

example : savitch halves 2 1 [false, false] [true, true] = false := by decide +kernel

example : ¬Relation.RelatesWithinSteps
    (fun a b => a.length = 2 ∧ b.length = 2 ∧ halves a b = true) [false, false] [true, true]
    (2 ^ 3) := by
  rw [← reach_iff (w := 2) (u := [false, false]) (v := [true, true]) rfl rfl]
  decide

/-! ### The trivial walk -/

example : savitch (fun _ _ => false) 2 0 [true, false] [true, false] = true := by decide

example : savitch (fun _ _ => false) 2 0 [true, false] [false, true] = false := by decide

example : savitch (fun _ _ => false) 0 3 [] [] = true := by decide +kernel

/-! ### The certificates, for a family of depths -/

/-- The unit type, encoded by the empty word. -/
def encUnit : Unit ↪ List Bool := ⟨fun _ => [], fun _ _ _ => rfl⟩

/-- The equality of words, as an edge test with a trivial parameter, in the calculus. -/
theorem exists_inO_eq : ∃ T S, ComputableTidilyInO
    (fun q : Unit × List Bool × List Bool => decide (q.2.1 = q.2.2))
    (encPair encUnit (encPair encBits encBits)) encBool T S :=
  ⟨_, _, ComputableTidilyInO.eqWords.comp (ComputableTidilyInO.snd encUnit _)⟩

-- Savitch's algorithm at depth `n`, with the width, the endpoints and the edge test fixed.
example : ∃ T S, ComputableTidilyInO
    (fun n : ℕ => savitch (fun u v => decide (u = v)) 1 n [false] [true]) encUnary encBool T S := by
  obtain ⟨Te, Se, hedge⟩ := exists_inO_eq
  have hin : ComputableTidilyInO (fun n : ℕ => ((), 1, n, [false], [true])) encUnary
      (encArgs encUnit) _ _ :=
    (ComputableTidilyInO.const ()).prod ((ComputableTidilyInO.const 1).prod
      ((ComputableTidilyInO.of_linear (.of_eq fun _ => rfl)).prod
        ((ComputableTidilyInO.const [false]).prod (ComputableTidilyInO.const [true]))))
  exact ⟨_, _, computableTidilyInO_savitch (edge := fun _ u v => decide (u = v)) hedge hin
    (fun _ => rfl) fun _ => rfl⟩

-- The same family, in polynomial space.
example : ∃ t s, PolyBounded (fun n : ℕ => (encUnary n).length) s ∧
    ComputableTidilyInTimeAndSpace
      (fun n : ℕ => savitch (fun u v => decide (u = v)) 1 n [false] [true]) encUnary encBool
      t s := by
  have hedge : ComputableTidilyInPolyTime
      (fun q : Unit × List Bool × List Bool => decide (q.2.1 = q.2.2))
      (encPair encUnit (encPair encBits encBits)) encBool :=
    (ComputableTidilyInDegree.eqWords.comp
      (ComputableTidilyInDegree.snd encUnit _)).computableTidilyInPolyTime
  have hin : ComputableTidilyInPolyTime (fun n : ℕ => ((), 1, n, [false], [true])) encUnary
      (encArgs encUnit) := by
    fun_prop
  exact exists_polyBounded_space_savitch (edge := fun _ u v => decide (u = v)) hedge hin
    (fun _ => rfl) fun _ => rfl

/-! ### Axioms -/

/--
info: 'Cslib.Reachability.reach_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Reachability.reach_iff

/--
info: 'Cslib.Reachability.savitch_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Reachability.savitch_eq

/--
info: 'Cslib.Reachability.savitch_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Reachability.savitch_iff

/--
info: 'Cslib.Reachability.computableTidilyInO_roundStep' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Reachability.computableTidilyInO_roundStep

/--
info: 'Cslib.Reachability.computableTidilyInO_savitch' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Reachability.computableTidilyInO_savitch

/--
info: 'Cslib.Reachability.exists_polyBounded_space_savitch' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Reachability.exists_polyBounded_space_savitch

end ComplexityTests.Savitch
