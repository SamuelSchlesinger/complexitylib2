/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (to Mathlib's `Mathlib/Data/Nat/Defs.lean` or cslib)

public import Complexity.Init

/-!
# Dividing repeatedly by a power

Facts about `n / b ^ j` for the stages of an argument that divides a quantity by `b` at each step.

## Main results

* `Nat.le_div_pow_of_mul_pow_le`: lower bound on `n / b ^ j` when `a * b ^ d ≤ n` and `j ≤ d`.
* `Nat.mul_div_pow_succ_le`: `b * (n / b ^ (j + 1)) ≤ n / b ^ j`.
-/

@[expose] public section

namespace Nat

/-- If `a b ^ d ≤ n`, then `a ≤ n / b ^ j` for every `j ≤ d`. -/
theorem le_div_pow_of_mul_pow_le {a b d j n : ℕ} (hb : 0 < b) (hj : j ≤ d) (h : a * b ^ d ≤ n) :
    a ≤ n / b ^ j := by
  rw [Nat.le_div_iff_mul_le (Nat.pow_pos hb)]
  exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb hj)) h

/-- Dividing by one more power of `b`: `b (n / b ^ (j + 1)) ≤ n / b ^ j`. -/
theorem mul_div_pow_succ_le (n b j : ℕ) : b * (n / b ^ (j + 1)) ≤ n / b ^ j := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  exact Nat.mul_div_le _ _

end Nat
