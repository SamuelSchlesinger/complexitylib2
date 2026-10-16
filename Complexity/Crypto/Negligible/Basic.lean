/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Negligible

/-!
# Negligible bounds and real-valued estimates

The security-game API uses nonnegative advantages. Real-valued estimates, including the pinned
finite PRG API, express the same decay after coercion. A positive constant advantage cannot be
negligible.

## Main results

* `Cslib.Crypto.negligible_iff_coe`: pass between nonnegative and real-valued decay bounds.
* `Cslib.Crypto.not_negligible_const`: constant nonzero success contradicts security.

## References

The constant-bound argument is adapted from `Crypto/Negligible.lean` on the cslib `crypto` branch
at `5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the current upstream nonnegative API.
-/

@[expose] public section

namespace Cslib.Crypto

open scoped NNReal

/-- Nonnegative advantages decay negligibly exactly when their real coercions do. -/
theorem negligible_iff_coe {ε : ℕ → ℝ≥0} : Negligible ε ↔
    Asymptotics.SuperpolynomialDecay Filter.atTop (fun n : ℕ => (n : ℝ))
      (fun n => (ε n : ℝ)) := by
  simp only [Negligible, Asymptotics.SuperpolynomialDecay, ← NNReal.tendsto_coe,
    NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_zero]

/-- A constant nonzero advantage is not negligible. -/
theorem not_negligible_const {c : ℝ≥0} (hc : c ≠ 0) : ¬ Negligible (fun _ => c) := by
  intro h
  have ht : Filter.Tendsto (fun _ : ℕ => c) Filter.atTop (nhds 0) := by simpa using h 0
  exact hc (tendsto_nhds_unique tendsto_const_nhds ht)

end Cslib.Crypto
