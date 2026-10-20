/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.MassProduction.Fine
import Complexity.Computability.Circuit.Boolean.MassProduction.FineParameters

/-!
# Fine mass-production clients

These clients evaluate the parameter choices at concrete lengths, exercise the boundary of the
floor budget and the copy depth, check the slack and suffix-fraction inequalities at concrete
values, and record the axioms of the headline statements.
-/

namespace ComplexityTests.MassProduction.Fine

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.MassProduction
open Cslib.Circuits.Boolean.MassProduction.Fine Filter

/-! ### Parameters at rate `1 / 2` with slack `X = 32` -/

-- Prefix fraction `(den + num X) / ((X + 1) den) = 34 / 66`.
example : prefixWidth 1 2 32 1000 = 515 := by decide
example : suffixWidth 1 2 32 1000 = 485 := by decide
-- The suffix keeps a `32 / 33` fraction of the half of the input not taken by the copies.
example : 32 * (2 - 1) * 1000 ≤ (32 + 1) * 2 * suffixWidth 1 2 32 1000 := by decide
-- Dimension `4 (den + num X) + 3 = 139`, and `139 ≤ 2 ^ 8`.
example : dimension 1 2 32 = 139 ∧ blockWidth 1 2 32 = 8 := by decide
-- At `n = 1000` there are no complete blocks yet: the parameters are eventual.
example : blocks 1 2 32 1000 = 0 ∧ fieldWidth 1 2 32 1000 = 0 := by decide
-- The batch exponent rounds `γ n` down and adds one.
example : depth 1 2 1000 = 501 ∧ depth 1 2 1001 = 501 ∧ depth 0 7 1000 = 1 := by decide

-- Zero copies: the core budget always allows at least two copies, the floor budget one.
example (n : ℕ) : 2 ≤ 2 ^ (0 * n / 1 + 1) ∧ rationalCopyBudget 0 1 n = 1 := by
  simp [rationalCopyBudget]

-- The floor budget sits inside the core budget at every length.
example (n : ℕ) : rationalCopyBudget 2 3 n ≤ 2 ^ (2 * n / 3 + 1) :=
  rationalCopyBudget_le_two_pow n

/-! ### The slack -/

example : 2 * 1 * ((16 * (1 + 1) + 1) ^ 2 * (16 * (1 + 1) + 2)) ≤
    (2 * 1 + 1) * (16 * (1 + 1)) ^ 3 := two_mul_slack_le 1

-- The finite leading-coefficient arithmetic at concrete values: rate `0`, precision one, a
-- suffix of all `n = 4` inputs, one resource of single-copy cost `L = 1`, no overhead.
example : 1 * (1 - 0) * 4 * (1 * 1 + 0) ≤ (1 + 1) * 1 * 2 ^ 4 :=
  mul_add_le_of_slack (P := 1) (p := 0) (w := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-! ### Corollaries -/

-- The corollaries require only the core bound at every rational exponent.
example (h : ∀ num den : ℕ, num < den → FineMassProducesThrough num den) :
    ExponentialMassProduction ∧ RealFineMassProduction ∧ FineMassProducesAt 1 2 :=
  ⟨exponentialMassProduction_of_fine h, realFineMassProduction_of_fine h,
    (h 1 2 (by decide)).fineMassProducesAt⟩

-- The real-rate parameters exist for every `0 ≤ γ < 1` and `ε > 0`.
example : ∃ num den P : ℕ, num < den ∧ 0 < P ∧ (1 / 2 : ℝ) < (num : ℝ) / den ∧
    ((P : ℝ) + 1) * den ≤ (1 / (1 - 1 / 2) + 1 / 10) * P * ((den - num : ℕ) : ℝ) :=
  exists_rat_coefficient (by norm_num) (by norm_num) (by norm_num)

/-! ### The unconditional theorems -/

-- Rate `1 / 2`, precision `4`: eventually up to `2 ^ (⌊n / 2⌋ + 1)` copies of any function cost
-- at most `(1 + 1/4) · 2 · 2 ^ n / n`.
example : ∀ᶠ n in atTop, ∀ (f : (Fin n → Bool) → Bool) (k : ℕ), k ≤ 2 ^ (1 * n / 2 + 1) →
    ((4 * (2 - 1) * n : ℕ) : ℕ∞) * massComplexity f k ≤ ((4 + 1) * 2 * 2 ^ n : ℕ) :=
  fineMassProducesThrough (num := 1) (den := 2) (by decide) 4

-- Rate zero: a constant number of copies costs `(1 + 1/P) 2 ^ n / n`, Lupanov's coefficient.
example (P : ℕ) : ∀ᶠ n in atTop, ∀ (f : (Fin n → Bool) → Bool) (k : ℕ), k ≤ 2 ^ (0 * n / 1 + 1) →
    ((P * (1 - 0) * n : ℕ) : ℕ∞) * massComplexity f k ≤ ((P + 1) * 1 * 2 ^ n : ℕ) :=
  fineMassProducesThrough (num := 0) (den := 1) (by decide) P

-- Exponential range at rate `9 / 10`, at every positive length with one constant.
example : MassProducesAtAllLengths 9 10 := exponentialMassProduction 9 10 (by decide) (by decide)

-- Real rates: `γ = 0.99`, `ε = 1`.
example : ∃ cutoff : ℕ, ∀ n, cutoff ≤ n → ∀ (f : (Fin n → Bool) → Bool) (k : ℕ), 0 < k →
    (k : ℝ) ≤ (2 : ℝ) ^ ((99 / 100 : ℝ) * n) → ∃ bound : ℕ, massComplexity f k ≤ bound ∧
      (bound : ℝ) ≤ (1 / (1 - 99 / 100) + 1) * ((2 : ℝ) ^ n / n) :=
  realFineMassProduction _ (by norm_num) (by norm_num) 1 (by norm_num)

/-! ### Axioms -/

/--
info: 'Cslib.Circuits.Boolean.MassProduction.fineMassProducesThrough' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fineMassProducesThrough

/--
info: 'Cslib.Circuits.Boolean.MassProduction.exponentialMassProduction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exponentialMassProduction

/--
info: 'Cslib.Circuits.Boolean.MassProduction.realFineMassProduction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms realFineMassProduction

/--
info: 'Cslib.Circuits.Boolean.MassProduction.schedulerSizeBound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms schedulerSizeBound

/--
info: 'Cslib.Circuits.Boolean.MassProduction.fineMassProducesThrough_of_bounds' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fineMassProducesThrough_of_bounds

/--
info: 'Cslib.Circuits.Boolean.MassProduction.exists_complexity_le_of_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_complexity_le_of_bounds

/--
info: 'Cslib.Circuits.Boolean.MassProduction.pipelineSizeBound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pipelineSizeBound

/--
info: 'Cslib.Circuits.Boolean.MassProduction.realFineMassProduction_of_fine' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms realFineMassProduction_of_fine

/--
info: 'Cslib.Circuits.Boolean.MassProduction.exponentialMassProduction_of_fine' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exponentialMassProduction_of_fine

/--
info: 'Cslib.Circuits.Boolean.MassProduction.Fine.eventually_overhead_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fine.eventually_overhead_le

/-! ### Deprecated names -/

set_option linter.deprecated false in
/-- Field notation on a hypothesis of the deprecated type still resolves. -/
example (h : SharpMassProducesThrough 1 2) : SharpMassProducesAt 1 2 := h.sharpMassProducesAt

set_option linter.deprecated false in
/-- Field notation skips the explicit rate hypothesis. -/
example (h : SharpMassProducesThrough 1 2) : MassProducesAt 1 2 := h.massProducesAt (by decide)

set_option linter.deprecated false in
/-- So does the old idiom through the deprecated theorem name. -/
example : SharpMassProducesAt 1 2 :=
  (sharpMassProducesThrough (num := 1) (den := 2) (by decide)).sharpMassProducesAt

end ComplexityTests.MassProduction.Fine
