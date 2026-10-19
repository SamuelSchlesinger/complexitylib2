/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Nat/Log.lean`)

public import Complexity.Init
public import Mathlib.Data.Nat.Log

/-!
# Powers with logarithmic exponents

The power `b ^ ⌈log_b n⌉` overshoots `n` by less than a factor `b` (`Nat.pow_clog_le_mul`), so
`m ^ ⌈log_b n⌉`, which is at most `(b ^ ⌈log_b m⌉) ^ ⌈log_b n⌉ = (b ^ ⌈log_b n⌉) ^ ⌈log_b m⌉`, is
at most `b ^ ⌈log_b m⌉ * n ^ ⌈log_b m⌉` (`Nat.pow_clog_le_pow_clog_mul_pow_clog`): a factor `m`
applied `⌈log_b n⌉` times is polynomial in `n`. This is how the size of an iterated construction
stays polynomial after logarithmically many rounds. Similarly `2 ^ (⌊log₂ n⌋ + 1)` is at most
`2 (n + 1)` (`Nat.two_pow_log2_succ_le`).

## Main results

* `Nat.pow_clog_le_mul`: `b ^ ⌈log_b n⌉ ≤ b * n` for `n ≠ 0`.
* `Nat.pow_clog_le_pow_clog_mul_pow_clog`: `m ^ ⌈log_b n⌉ ≤ b ^ ⌈log_b m⌉ * n ^ ⌈log_b m⌉` for
  `n ≠ 0`.
* `Nat.two_pow_log2_succ_le`: `2 ^ (⌊log₂ n⌋ + 1) ≤ 2 (n + 1)`.
-/

@[expose] public section

namespace Nat

variable {b n : ℕ}

/-- The power `b ^ ⌈log_b n⌉` overshoots `n ≠ 0` by less than a factor `b`. -/
theorem pow_clog_le_mul (hb : 1 < b) (hn : n ≠ 0) : b ^ clog b n ≤ b * n := by
  rcases (one_le_iff_ne_zero.2 hn).eq_or_lt with rfl | hn
  · simpa using hb.le
  · have := pow_pred_clog_lt_self hb hn
    rw [← succ_pred_eq_of_pos (clog_pos hb hn), pow_succ']
    exact Nat.mul_le_mul_left _ this.le

/-- A factor `m` applied `⌈log_b n⌉` times is polynomial in `n ≠ 0`:
`m ^ ⌈log_b n⌉ ≤ b ^ ⌈log_b m⌉ * n ^ ⌈log_b m⌉`. -/
theorem pow_clog_le_pow_clog_mul_pow_clog (hb : 1 < b) (m : ℕ) (hn : n ≠ 0) :
    m ^ clog b n ≤ b ^ clog b m * n ^ clog b m :=
  calc m ^ clog b n ≤ (b ^ clog b m) ^ clog b n := Nat.pow_le_pow_left (le_pow_clog hb m) _
    _ = (b ^ clog b n) ^ clog b m := by rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
    _ ≤ (b * n) ^ clog b m := Nat.pow_le_pow_left (pow_clog_le_mul hb hn) _
    _ = b ^ clog b m * n ^ clog b m := Nat.mul_pow _ _ _

/-- `2 ^ (log₂ n + 1)` is at most `2 (n + 1)`. -/
theorem two_pow_log2_succ_le (n : ℕ) : 2 ^ (Nat.log2 n + 1) ≤ 2 * (n + 1) := by
  rw [Nat.pow_succ, Nat.mul_comm]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Nat.mul_le_mul_left 2 ((Nat.log2_self_le hn.ne').trans (Nat.le_succ n))

end Nat
