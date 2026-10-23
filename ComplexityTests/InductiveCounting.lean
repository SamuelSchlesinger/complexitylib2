/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

import Complexity.Algorithms.Reachability.InductiveCounting.Bounds

/-!
# Tests of the binary-choice inductive-counting controller

These tests execute the actual guarded transition on singleton, edgeless and cyclic graphs.
They include reflexive reachability, dishonest omissions, count mismatches, invalid identifiers,
and a guessed nonedge.
-/

namespace ComplexityTests.InductiveCounting

open Cslib.InductiveCounting

-- Kernel-checked evaluation unfolds up to 120 controller instructions, each with ten-register
-- updates and progress checks. The larger elaborator stack is confined to these finite tests.
set_option maxRecDepth 4096

private def noEdge : ℕ → ℕ → Bool := fun _ _ => false
private def noBad : ℕ → Bool := fun _ => false
private def badAt (target : ℕ) : ℕ → Bool := fun u => u == target

/-- Replay a state-dependent test strategy. This helper is not part of the controller. -/
private def drive (N width source : ℕ) (edge : ℕ → ℕ → Bool) (bad : ℕ → Bool)
    (strategy : State → Bool) : ℕ → State → State
  | 0, s => s
  | n + 1, s => drive N width source edge bad strategy n
      (step N width source edge bad s (strategy s))

private def onlySource (source : ℕ) (s : State) : Bool :=
  s.phase == .candidate && s.candidate == source ||
    s.phase == .guess && source == 1

private def cycleEdge (u v : ℕ) : Bool := (u == 0 && v == 1) || (u == 1 && v == 0)

private def cycleChoice (s : State) : Bool :=
  (s.phase == .candidate && (s.round != 0 || s.candidate == 0)) ||
    (s.phase == .guess && s.candidate == 1)

-- A singleton, including width zero and a padded walk of length zero.
example : (drive 1 0 0 noEdge noBad (onlySource 0) 8 (initial 1 0)).phase = .accept := by
  decide

-- The source itself is reachable even when there are no edges.
example : (drive 1 0 0 noEdge (badAt 0) (onlySource 0) 8 (initial 1 0)).phase = .reject := by
  decide

-- An isolated other vertex is unreachable; the final scan uses a length-one padded walk.
example : (drive 2 1 0 noEdge (badAt 1) (onlySource 0) 80 (initial 2 0)).phase = .accept := by
  decide

example : (drive 2 1 1 noEdge (badAt 0) (onlySource 1) 80 (initial 2 1)).phase = .accept := by
  decide

example : (drive 2 1 0 noEdge (badAt 0) (onlySource 0) 80 (initial 2 0)).phase = .reject := by
  decide

-- A non-power-of-two vertex interval exercises two binary choices for each next vertex.
example : (drive 3 2 0 noEdge (badAt 2) (onlySource 0) 120 (initial 3 0)).phase = .accept := by
  decide

-- A directed cycle reaches both vertices after one round.
example : (drive 2 1 0 cycleEdge noBad cycleChoice 100 (initial 2 0)).phase = .accept := by
  decide

example : (drive 2 1 0 cycleEdge (badAt 1) cycleChoice 100 (initial 2 0)).phase = .reject := by
  decide

-- Omitting a reachable bad vertex cannot pass the final scan's count check.
example : (drive 2 1 0 cycleEdge (badAt 1) (onlySource 0) 100 (initial 2 0)).phase = .reject := by
  decide

-- Omitting the source immediately fails the first scan's count check.
example : (drive 2 1 0 noEdge noBad (fun _ => false) 20 (initial 2 0)).phase = .reject := by
  decide

example : step 2 1 0 noEdge noBad
    { phase := .done, count := 1, selected := 0, finalScan := true } false = reject := by
  decide

-- Counts can equal N; they are not width-bit vertex identifiers.
example : Bounded 2 1 { phase := .done, count := 2, selected := 2 } := by decide

-- The unused binary code for vertex 3 is rejected in a three-vertex graph.
example : step 3 2 0 noEdge noBad
    { phase := .guess, guess := 3, bits := 0 } false = reject := by decide

example : step 3 2 0 noEdge noBad
    (step 3 2 0 noEdge noBad { phase := .guess, guess := 0, bits := 2 } true) false =
      { phase := .guess, guess := 2, bits := 0 } := by decide

example : step 2 1 0 noEdge noBad
    { phase := .edge, current := 0, guess := 1, remaining := 1 } false = reject := by decide

example : initial 0 0 = reject := by decide
example : initial 2 2 = reject := by decide

-- The primitive correctness theorem is uniform in the graph, not just these computations.
example (edge : ℕ → ℕ → Bool) (bad : ℕ → Bool) :
    Accepts 1 0 0 edge bad ↔ Safe 1 0 edge bad := accepts_iff (by decide) (by decide)

/--
info: 'Cslib.InductiveCounting.accepts_sound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.InductiveCounting.accepts_sound

/--
info: 'Cslib.InductiveCounting.accepts_complete' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.InductiveCounting.accepts_complete

/--
info: 'Cslib.InductiveCounting.accepts_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.InductiveCounting.accepts_iff

/--
info: 'Cslib.InductiveCounting.accepts_iff_not_reachable' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.InductiveCounting.accepts_iff_not_reachable

/--
info: 'Cslib.InductiveCounting.accepts_complete_bounded' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.InductiveCounting.accepts_complete_bounded

/--
info: 'Cslib.InductiveCounting.halted_replay_budget' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.InductiveCounting.halted_replay_budget

end ComplexityTests.InductiveCounting
