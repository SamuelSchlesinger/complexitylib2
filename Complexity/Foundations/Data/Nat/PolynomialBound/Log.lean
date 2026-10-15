/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Foundations/Data/Nat/PolynomialBound.lean`)

public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Mathlib.Data.Nat.Log

/-!
# Polynomial bounds and logarithms

Polynomially bounded functions have logarithmic logarithms: if `s` is polynomially bounded, then
`⌈log₂ (s n)⌉` is at most `e (⌊log₂ n⌋ + 1)` for a constant `e`
(`PolynomiallyBounded.exists_clog_le_mul_log`). Conversely, `2` to the power `c (⌊log₂ n⌋ + 1)`
is polynomially bounded (`polynomiallyBounded_two_pow_mul_log`). These are the conversions between
depth `O(log n)` and size `n ^ O(1)` in circuit complexity.

Here `⌊log₂ n⌋ + 1`, written `Nat.log 2 n + 1`, is the number of binary digits of `n` with `0`
written as one digit, that is `max n.size 1`, which unlike `Nat.size n` is positive at `n = 0`.

## Main results

* `Cslib.PolynomiallyBounded.exists_clog_le_mul_log`: the logarithm of a polynomially bounded
  function is `O(log n)`.
* `Cslib.polynomiallyBounded_two_pow_mul_log`: `2 ^ O(log n)` is polynomially bounded.
-/

@[expose] public section

namespace Cslib

/-- `2 ^ (c (⌊log₂ n⌋ + 1))` is polynomially bounded: it is at most `2 ^ c (n + 1) ^ c`. -/
theorem polynomiallyBounded_two_pow_mul_log (c : ℕ) :
    PolynomiallyBounded fun n => 2 ^ (c * (Nat.log 2 n + 1)) := by
  refine polynomiallyBounded_iff_le.2 ⟨2 ^ c, c, fun n => ?_⟩
  have h : 2 ^ Nat.log 2 n ≤ n + 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact (Nat.pow_log_le_self 2 hn.ne').trans (Nat.le_succ n)
  calc 2 ^ (c * (Nat.log 2 n + 1)) = 2 ^ c * (2 ^ Nat.log 2 n) ^ c := by
        rw [mul_add, mul_one, pow_add, mul_comm c, pow_mul, mul_comm]
    _ ≤ 2 ^ c * (n + 1) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h c)

/-- The binary logarithm of a polynomially bounded function is at most `e (⌊log₂ n⌋ + 1)` for a
constant `e`. -/
theorem PolynomiallyBounded.exists_clog_le_mul_log {s : ℕ → ℕ} (hs : PolynomiallyBounded s) :
    ∃ e, ∀ n, Nat.clog 2 (s n) ≤ e * (Nat.log 2 n + 1) := by
  obtain ⟨a, d, h⟩ := polynomiallyBounded_iff_le.1 hs
  refine ⟨a + d, fun n => (Nat.clog_le_iff_le_pow one_lt_two).2 ?_⟩
  calc s n ≤ a * (n + 1) ^ d := h n
    _ ≤ 2 ^ a * (2 ^ (Nat.log 2 n + 1)) ^ d :=
        Nat.mul_le_mul Nat.lt_two_pow_self.le
          (Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self one_lt_two n) d)
    _ = 2 ^ (a + d * (Nat.log 2 n + 1)) := by
        rw [← pow_mul, ← pow_add, mul_comm (Nat.log 2 n + 1)]
    _ ≤ 2 ^ ((a + d) * (Nat.log 2 n + 1)) := by
        refine Nat.pow_le_pow_right two_pos ?_
        rw [add_mul]
        exact Nat.add_le_add_right (Nat.le_mul_of_pos_right a (Nat.succ_pos _)) _

end Cslib
