/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Tactic.PolyTime

/-!
# Plain automation from a source-only import

This module imports the tactic directly, without compiled program certificates whose proof
bodies might make its internal construction lemmas available incidentally. The named shrinking
step has the same nonincreasing fold contract used by the GGM evaluator.
-/

public section

open Turing.MultiTapeTM

namespace ComplexityTests.PolyTimePlainSource

/-- A total step which truncates a routine output to the current state length. -/
@[expose] def shrinkingStep (routine : List Bool → List Bool) (state : List Bool) (_ : Bool) :
    List Bool :=
  (routine state).take state.length

private theorem shrinkingStep_polyTime {routine : List Bool → List Bool}
    (hroutine : ComputableInPolyTime routine encBits encBits) :
    ComputableInPolyTime (fun p : List Bool × Bool => shrinkingStep routine p.1 p.2)
      (encPair encBits encBool) encBits := by
  fun_prop [shrinkingStep]

private theorem shrinkingStep_length (routine : List Bool → List Bool)
    (state : List Bool) (bit : Bool) :
    (shrinkingStep routine state bit).length ≤ state.length := by
  simp only [shrinkingStep, List.length_take]
  exact Nat.min_le_left _ _

/-- Source-only named folding uses the runtime helper declarations from the tactic import. -/
theorem shrinkingFold_polyTime {routine : List Bool → List Bool}
    (hroutine : ComputableInPolyTime routine encBits encBits) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool => p.2.foldl (shrinkingStep routine) p.1)
      (encPair encBits encBits) encBits := by
  have hstep := shrinkingStep_polyTime hroutine
  have hgrowth := shrinkingStep_length routine
  polytime

/-- The framed-query variant exercises the separate framed-list fold adapter. -/
theorem shrinkingFramedFold_polyTime {routine : List Bool → List Bool}
    (hroutine : ComputableInPolyTime routine encBits encBits) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool => p.2.foldl (shrinkingStep routine) p.1)
      (encPair encBits (encList encBool)) encBits := by
  have hstep := shrinkingStep_polyTime hroutine
  have hgrowth := shrinkingStep_length routine
  polytime

example : ComputableInPolyTime (fun p : List Bool × List Bool => p.1 ++ p.2)
    (encPair encBits encBits) encBits := by
  polytime

example : ComputableInPolyTime (fun p : List Bool × List Bool => p.1 ++ p.2)
    (encPair (encList encBool) (encList encBool)) (encList encBool) := by
  polytime

example : ComputableInPolyTime (fun p : Bool × List Bool => p.1 :: p.2)
    (encPair encBool (encList encBool)) (encList encBool) := by
  polytime

example : ComputableInPolyTime (fun p : Bool × List Bool => p.1 :: p.2)
    (encPair encBool encBits) encBits := by
  polytime

example {routine : List Bool → List Bool}
    (hroutine : ComputableInPolyTime routine encBits encBits) (growth : ℕ) :
    ComputableInPolyTime
      (fun p : ℕ × List Bool => (fun state => shrinkingStep routine state true)^[p.1] p.2)
      (encPair encUnary encBits) encBits := by
  have hstep : ComputableInPolyTime (fun state => shrinkingStep routine state true)
      encBits encBits := by fun_prop [shrinkingStep]
  have hgrowth : ∀ state, (shrinkingStep routine state true).length ≤ state.length + growth := by
    intro state
    exact (shrinkingStep_length routine state true).trans (Nat.le_add_right _ _)
  polytime

end ComplexityTests.PolyTimePlainSource
