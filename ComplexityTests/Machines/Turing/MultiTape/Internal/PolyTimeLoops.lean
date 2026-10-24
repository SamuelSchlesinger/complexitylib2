/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops

/-! # Direct plain loops without a tidy polynomial-time calculus -/

open Turing.MultiTapeTM

run_elab do
  let env ← Lean.getEnv
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree,
      `Turing.MultiTapeTM.ComputableTidilyInO] do
    if env.contains name then throwError "unexpected high-level tidy predicate: {name}"

-- The list varies with the input; this is not a fixed finite lookup family.
example : ComputableInPolyTime (fun word : List Bool => word.foldl Bool.xor false)
    encBits encBool := by
  apply ComputableInPolyTime.foldl' (encA := encBool) (B := fun _ => 1)
    ComputableInPolyTime.id' (ComputableInPolyTime.const false)
    (ComputableInPolyTime.of_finite (fun p : Bool × Bool => Bool.xor p.1 p.2))
  · exact PolyBounded.const 1
  · simp

-- The invariant is needed: a uniform efficient step can still double the output every round.
example : ¬ (∀ word : List Bool, ∀ i ≤ word.length,
    (((word.take i).foldl (fun state _ => state ++ state) [true]).length ≤ 1)) := by
  intro h
  have := h [false] 1 (by decide)
  simp at this

/-- info: 'Turing.MultiTapeTM.ComputableInPolyTime.foldl'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableInPolyTime.foldl'
