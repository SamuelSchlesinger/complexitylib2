/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Foundations.Data.Nat.Bitwise.Projection

/-! A foundation-only client for differences, projections, and prefix boundaries. -/

open Cslib.BitString

namespace BitStringProjectionTests

/-- Empty widths and equal words use the documented default differing position. -/
example : differingBits 0 1 2 = ∅ ∧ highestDiff 0 1 2 = 0 ∧
    highestDiff 4 9 9 = 0 := by decide

/-- Both the least and the most significant position can distinguish bounded words. -/
example : highestDiff 4 8 9 = 0 ∧ highestDiff 4 1 8 = 3 := by decide

/-- Projection supports empty, repeated, and unsorted position lists. -/
example : projectBits [] 9 = 0 ∧ projectBits [0, 0] 1 = 3 ∧
    projectBits [3, 0] 1 = 2 ∧ projectBits [3, 0] 8 = 1 := by decide

/-- Increasing selected positions preserve this pair by retaining its highest difference. -/
example : sketch {0, 1, 3} 16 < sketch {0, 1, 3} 27 :=
  sketch_lt_of_highestDiff_mem (w := 5) (by decide) (by decide) (by decide) (by decide)

/-- The generic difference theorem can be used without importing any algorithm. -/
example {w x y : ℕ} (hx : x < 2 ^ w) (hy : y < 2 ^ w) (hne : x ≠ y) :
    highestDiff w x y < w ∧
      x.testBit (highestDiff w x y) ≠ y.testBit (highestDiff w x y) ∧
      ∀ i, highestDiff w x y < i → x.testBit i = y.testBit i :=
  highestDiff_spec hx hy hne

/-- Numeric projection sums are available through the same foundation import. -/
example {r : ℕ} (positions : Fin r → ℕ) (x : ℕ) :
    projectBits (List.ofFn positions) x =
      ∑ i, (x.testBit (positions i)).toNat * 2 ^ i.val :=
  projectBits_ofFn_eq_sum positions x

/-- The two masks meet across the selected bit and preserve the high prefix. -/
example : lowerBoundary 13 2 = 11 ∧ upperBoundary 13 2 = 12 := by decide

example (q p : ℕ) : lowerBoundary q p >>> (p + 1) = q >>> (p + 1) ∧
    upperBoundary q p >>> (p + 1) = q >>> (p + 1) := boundary_prefix q p

/-- info: 'Cslib.BitString.highestDiff_spec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.highestDiff_spec

end BitStringProjectionTests
