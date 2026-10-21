/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Machine
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial resource bounds for the universal simulator

The resource functions of Christian Reitwiessner's universal simulator admit explicit polynomial
bounds in the encoded description length, encoded input length, clock length, and number of
simulated steps. These estimates are shared by unary-clock polynomial-time simulation and the
time-hierarchy construction.

## Main results

* `Turing.MultiTapeTM.Universal.runBound_mono`: the space bound grows with the number of steps.
* `Turing.MultiTapeTM.Universal.universal_bounds_le`: for `D, N, L ≤ B` and `1 ≤ J`, the time
  expression is at most `100000 * (B + 1) ^ 5 * J ^ 3` and the space bound is at most
  `200 * (B + 1) ^ 2 * J`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.Universal

/-- The universal simulator's space bound grows with the number of simulated steps. -/
theorem runBound_mono {D N t t' : ℕ} (h : t ≤ t') : runBound D N t ≤ runBound D N t' := by
  unfold runBound ctxBound cfgBound tapeBound
  gcongr

/-- **The resources of the universal run.** If the encoded description, the encoded input and the
number of digits `L` of the clock have length at most `B`, the time of the universal function on
`J ≥ 1` steps is `O(B ^ 5 * J ^ 3)` and its space `O(B ^ 2 * J)`. -/
theorem universal_bounds_le {D N J B L : ℕ} (hD : D ≤ B) (hN : N ≤ B) (hL : L ≤ B) (hJ : 1 ≤ J) :
    (J + 1) * (stepBound D N J + runBound D N J + (L + 1) ^ 2) ≤ 100000 * (B + 1) ^ 5 * J ^ 3 ∧
      runBound D N J ≤ 200 * (B + 1) ^ 2 * J := by
  set M := B + 1 with hM
  have hM1 : 1 ≤ M := by omega
  have hDM : D + 1 ≤ M := by omega
  have hNM : N + 1 ≤ M := by omega
  have hMJ : M ≤ M * J := Nat.le_mul_of_pos_right _ hJ
  have hM2 : M ≤ M ^ 2 := Nat.le_self_pow two_ne_zero _
  have hM2J : M ^ 2 ≤ M ^ 2 * J := Nat.le_mul_of_pos_right _ hJ
  have htape : tapeBound D J ≤ 36 * M * J := by
    unfold tapeBound
    nlinarith
  have hcfg : cfgBound D N J ≤ 80 * M ^ 2 * J := by
    unfold cfgBound
    have : D * (2 * tapeBound D J + 1) ≤ M * (72 * M * J + 1) :=
      Nat.mul_le_mul (by omega) (by linarith)
    nlinarith
  have hctx : ctxBound D N J ≤ 89 * M ^ 2 * J := by
    unfold ctxBound
    nlinarith
  have hrun : runBound D N J ≤ 200 * M ^ 2 * J := by
    unfold runBound
    have : J * (2 * D + 1) ≤ J * (2 * M) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  refine ⟨?_, hrun⟩
  have hstep : stepBound D N J ≤ 40500 * M ^ 5 * J ^ 2 := by
    unfold stepBound
    have h₁ : 2 * D + N + 2 ≤ 5 * M := by omega
    have h₂ : (ctxBound D N J + 1) ^ 2 ≤ (90 * M ^ 2 * J) ^ 2 :=
      Nat.pow_le_pow_left (by nlinarith) 2
    calc (2 * D + N + 2) * (ctxBound D N J + 1) ^ 2 ≤ (5 * M) * (90 * M ^ 2 * J) ^ 2 :=
          Nat.mul_le_mul h₁ h₂
      _ = 40500 * M ^ 5 * J ^ 2 := by ring
  have hM5 : M ^ 2 * J ≤ M ^ 5 * J ^ 2 :=
    Nat.mul_le_mul (Nat.pow_le_pow_right hM1 (by omega)) (Nat.le_self_pow two_ne_zero _)
  have hL2 : (L + 1) ^ 2 ≤ M ^ 5 * J ^ 2 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (hM2J.trans hM5)
  have hsum : stepBound D N J + runBound D N J + (L + 1) ^ 2 ≤ 40701 * M ^ 5 * J ^ 2 := by
    nlinarith
  calc (J + 1) * (stepBound D N J + runBound D N J + (L + 1) ^ 2)
      ≤ (2 * J) * (40701 * M ^ 5 * J ^ 2) := Nat.mul_le_mul (by omega) hsum
    _ ≤ 100000 * M ^ 5 * J ^ 3 := by nlinarith [Nat.zero_le (M ^ 5 * J ^ 3)]

end Turing.MultiTapeTM.Universal
