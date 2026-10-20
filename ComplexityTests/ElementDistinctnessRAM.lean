/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.WordRAM.ElementDistinctnessRAM

/-!
# Logarithmic-cost element-distinctness clients

The compiled target program is exercised on the empty list, the smallest nonempty instance,
a distinct list and a duplicate list. The declared theorem concerns the supplied padded input;
these clients do not assert that preparation has been charged.
-/

namespace ComplexityTests.ElementDistinctnessRAM

open Cslib Cslib.WordRAM Cslib.Algorithms.WordRAM.ElementDistinctness

private def result (input : List ℕ) : ℕ × Bool :=
  let s := RAM.run paddedRamProgram 250 (RAM.State.init (ToRAM.paddedInput 12 input))
  (s.regs.output, decide (s.isHalted paddedRamProgram))

/-- info: [(1, true), (1, true), (1, true), (0, true)] -/
#guard_msgs in
#eval [result [], result [0], result [0, 1], result [1, 1]]

/-- The empty-list time bound is non-vacuous and includes the target's explicit halt path. -/
example : RAM.HaltsWithResultInTime RAM.logCost paddedRamProgram (ToRAM.paddedInput 12 [])
    1 2448 := by
  simpa using haltsWithResultInTime_nodup_padded ⟨[], by simp⟩

/-- A duplicate instance uses the same fixed target program and logarithmic-cost theorem. -/
example : RAM.HaltsWithResultInTime RAM.logCost paddedRamProgram (ToRAM.paddedInput 12 [1, 1])
    0 (2448 * 3 * 2) := by
  simpa [show Nat.log 2 3 = 1 by decide] using
    haltsWithResultInTime_nodup_padded ⟨[1, 1], by simp⟩

/--
info: 'Cslib.Algorithms.WordRAM.ElementDistinctness.haltsWithResultInTime_nodup_padded'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Algorithms.WordRAM.ElementDistinctness.haltsWithResultInTime_nodup_padded

end ComplexityTests.ElementDistinctnessRAM
