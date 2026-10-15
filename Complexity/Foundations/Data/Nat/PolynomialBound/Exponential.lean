/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Foundations/Data/Nat/PolynomialBound.lean`)

public import Cslib.Foundations.Data.Nat.PolynomialBound
import Mathlib.Analysis.SpecificLimits.Normed

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
  have h := (tendsto_pow_const_div_const_pow_of_one_lt d (one_lt_two : (1 : ℝ) < 2)).eventually
    (gt_mem_nhds zero_lt_one)
  filter_upwards [hd, h] with n hn hlt
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have hlt' : ((n : ℝ) ^ d) < 2 ^ n := by rwa [div_lt_one hpos] at hlt
  exact lt_of_le_of_lt hn (by exact_mod_cast hlt')

end Cslib.PolynomiallyBounded
