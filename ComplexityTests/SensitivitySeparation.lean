/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.QueryComplexity.SensitivitySeparation
import Complexity.Computability.QueryComplexity.SensitivitySeparation.Internal.Bridge

/-! Clients and axiom guards for the superquadratic sensitivity separation. -/

namespace ComplexityTests.SensitivitySeparation

open Cslib Cslib.BitString Cslib.QueryComplexity

-- The headline separation, at a concrete constant.
example : ∃ (n : ℕ) (f : BooleanFunction n), 0 < n ∧ (∃ x y, f x ≠ f y) ∧
    1000 * (sensitivity f : ℝ) ^ 2 < (blockSensitivity f : ℝ) :=
  exists_mul_sensitivity_sq_lt_blockSensitivity 1000 (by norm_num)

-- No polynomial bound of degree two holds for decision-tree complexity either.
example (C : ℝ) (hC : 0 < C) : ¬ ∀ (n : ℕ) (f : BooleanFunction n),
    (DecisionTree.complexity f : ℝ) ≤ C * (sensitivity f : ℝ) ^ 2 := fun h => by
  obtain ⟨n, f, -, -, hf⟩ := DecisionTree.exists_mul_sensitivity_sq_lt_complexity C hC
  exact (h n f).not_gt hf

-- The internal measures agree with CSLib's on `Fin n`.
example {n : ℕ} (f : BooleanFunction n) :
    SensitivitySeparation.Internal.blockSensitivity f = blockSensitivity f :=
  SensitivitySeparation.Internal.blockSensitivity_eq_blockSensitivity f

/--
info: 'Cslib.QueryComplexity.exists_two_pow_div_le_blockSensitivityAt_div_sensitivity_sq' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_two_pow_div_le_blockSensitivityAt_div_sensitivity_sq

/--
info: 'Cslib.QueryComplexity.exists_mul_sensitivity_sq_lt_blockSensitivityAt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_mul_sensitivity_sq_lt_blockSensitivityAt

/--
info: 'Cslib.QueryComplexity.exists_mul_sensitivity_sq_lt_blockSensitivity' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_mul_sensitivity_sq_lt_blockSensitivity

/--
info: 'Cslib.QueryComplexity.exists_sensitivity_rpow_le_blockSensitivityAt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_sensitivity_rpow_le_blockSensitivityAt

/--
info: 'Cslib.QueryComplexity.exists_mul_sensitivity_sq_lt_certificateComplexity' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_mul_sensitivity_sq_lt_certificateComplexity

/--
info: 'Cslib.DecisionTree.exists_mul_sensitivity_sq_lt_complexity' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DecisionTree.exists_mul_sensitivity_sq_lt_complexity

/--
info: 'Cslib.DecisionTree.exists_sensitivity_rpow_le_complexity' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DecisionTree.exists_sensitivity_rpow_le_complexity

end ComplexityTests.SensitivitySeparation
