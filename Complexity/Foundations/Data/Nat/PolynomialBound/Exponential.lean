/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Foundations/Data/Nat/PolynomialBound.lean`)

public import Cslib.Foundations.Data.Nat.PolynomialBound
import Cslib.Foundations.Data.Nat.Asymptotics

/-!
# Polynomial bounds are eventually below exponentials

A polynomially bounded function is eventually smaller than `2 ^ n`
(`PolynomiallyBounded.eventually_lt_two_pow`): exponential lower bounds rule out polynomial upper
bounds.

## Main results

* `Cslib.PolynomiallyBounded.eventually_lt_two_pow`.
-/

@[expose] public section

namespace Cslib.PolynomiallyBounded

open Filter

/-- **A polynomially bounded function is eventually below `2 ^ n`.** -/
theorem eventually_lt_two_pow {f : ℕ → ℕ} (hf : PolynomiallyBounded f) :
    ∀ᶠ n in atTop, f n < 2 ^ n := by
  obtain ⟨d, hd⟩ := hf
  filter_upwards [hd, Nat.eventually_mul_pow_le_pow 2 d one_lt_two, eventually_ge_atTop 1]
    with n hn hpow hn1
  have := Nat.pow_pos (n := d) hn1
  omega

end Cslib.PolynomiallyBounded
