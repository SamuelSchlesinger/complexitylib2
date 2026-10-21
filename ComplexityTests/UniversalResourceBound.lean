/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Universal.ResourceBound

/-! The universal resource estimates are available without importing complexity classes. -/

open Turing.MultiTapeTM.Universal

example {D N J B L : ℕ} (hD : D ≤ B) (hN : N ≤ B) (hL : L ≤ B) (hJ : 1 ≤ J) :
    (J + 1) * (stepBound D N J + runBound D N J + (L + 1) ^ 2) ≤
        100000 * (B + 1) ^ 5 * J ^ 3 ∧
      runBound D N J ≤ 200 * (B + 1) ^ 2 * J :=
  universal_bounds_le hD hN hL hJ

-- The minimum permitted clock and zero size bounds satisfy all hypotheses.
example : 2 * (stepBound 0 0 1 + runBound 0 0 1 + 1) ≤ 100000 ∧
    runBound 0 0 1 ≤ 200 := by
  simpa using universal_bounds_le (D := 0) (N := 0) (J := 1) (B := 0) (L := 0)
    (by decide) (by decide) (by decide) (by decide)

example {D N : ℕ} : runBound D N 0 ≤ runBound D N 1 := runBound_mono (by decide)

/--
info: 'Turing.MultiTapeTM.Universal.universal_bounds_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.Universal.universal_bounds_le
