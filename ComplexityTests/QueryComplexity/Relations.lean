/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.DecisionTree.Symmetric
import Complexity.Computability.QueryComplexity.Monotone
import Complexity.Computability.QueryComplexity.SensitivityBounds
import Complexity.Computability.QueryComplexity.Threshold

/-! Query complexity of threshold, majority and monotone functions, one-sided bounds and the
evasiveness of symmetric functions: concrete values checked against the general formulas,
witnesses that the monotonicity and symmetry hypotheses are satisfiable, and axiom guards for the
headline theorems. -/

namespace ComplexityTests.QueryComplexity.Relations

open Cslib Cslib.BitString Cslib.QueryComplexity Finset

/-! ### Threshold functions -/

/-- The formula `max(j, n + 1 - j)` agrees with exhaustive computation on four bits. -/
example : sensitivity (threshold 4 2) = 3 ∧ certificateComplexity (threshold 4 2) = 3 := by
  refine ⟨by decide, ?_⟩
  rw [certificateComplexity_threshold (by norm_num) (by norm_num)]
  rfl

example : sensitivity (threshold 4 2) = max 2 (4 + 1 - 2) :=
  sensitivity_threshold (by norm_num) (by norm_num)

example : sensitivity (majority 5) = 3 ∧ blockSensitivity (threshold 5 2) = 4 :=
  ⟨sensitivity_majority (by norm_num), blockSensitivity_threshold (by norm_num) (by norm_num)⟩

/-- One true bit certifies the disjunction, but its value `0` needs every bit. -/
example : certificateComplexityFor (threshold 3 1) true = 1 ∧
    certificateComplexityFor (threshold 3 1) false = 3 ∧
    certificateComplexity (threshold 3 1) = 3 :=
  ⟨certificateComplexityFor_threshold_one_right_true (by norm_num),
    certificateComplexityFor_threshold_one_right_false, certificateComplexity_threshold_one_right⟩

example : certificateComplexityFor (threshold 3 1) true = 1 := by decide

/-! ### Evasiveness -/

example : DecisionTree.complexity (majority 4) = 4 ∧ DecisionTree.complexity (threshold 7 5) = 7 :=
  ⟨DecisionTree.complexity_majority (by norm_num),
    DecisionTree.complexity_threshold (by norm_num) (by norm_num)⟩

/-- Majority of four bits has sensitivity `3` yet is evasive. -/
example : sensitivity (majority 4) = 3 ∧ DecisionTree.complexity (majority 4) = 4 :=
  ⟨sensitivity_majority (by norm_num), DecisionTree.complexity_majority (by norm_num)⟩

/-- The symmetry hypothesis is satisfiable by a non-monotone function, parity. -/
example {n : ℕ} (hn : 1 ≤ n) : DecisionTree.complexity (parity n) = n :=
  DecisionTree.complexity_eq_card_of_isSymmetric isSymmetric_parity fun h => by
    have h0 : parity n (fun _ => false) = false := by
      rw [parity_eq_decide_weight]
      simp [weight]
    have h1 : parity n (Function.update (fun _ => false) ⟨0, hn⟩ true) = true := by
      rw [parity_eq_decide_weight, weight_update_true rfl, decide_eq_true_iff]
      simp [weight]
    exact Bool.false_ne_true (h0.symm.trans ((h _ _).trans h1))

/-! ### Monotone functions and one-sided measures -/

/-- The monotonicity hypothesis is satisfiable: majority is monotone, so `C = bs = s`. -/
example {n : ℕ} : certificateComplexity (majority n) = sensitivity (majority n) ∧
    blockSensitivity (majority n) = sensitivity (majority n) :=
  ⟨certificateComplexity_eq_sensitivity_of_monotone (monotone_threshold _),
    blockSensitivity_eq_sensitivity_of_monotone (monotone_threshold _)⟩

/-- The one-sided sensitivity is computable. -/
example : sensitivityFor (threshold 3 1) false = 3 ∧ sensitivityFor (threshold 3 1) true = 1 := by
  refine ⟨?_, ?_⟩ <;> decide

example {n : ℕ} (f : BooleanFunction n) :
    certificateComplexityFor f true ≤ sensitivityFor f false * blockSensitivityFor f true ∧
      DecisionTree.complexity f ≤ blockSensitivityFor f true * certificateComplexityFor f false ∧
      DecisionTree.complexity f ≤
        blockSensitivityFor f false * sensitivityFor f false * blockSensitivityFor f true :=
  ⟨certificateComplexityFor_le_sensitivityFor_mul_blockSensitivityFor f true,
    DecisionTree.complexity_le_blockSensitivityFor_not_mul_certificateComplexityFor f false,
    DecisionTree.complexity_le_blockSensitivityFor_mul_sensitivityFor_mul_blockSensitivityFor
      f true⟩

example {n : ℕ} (f : BooleanFunction n) :
    certificateComplexity f ≤ 2 * sensitivity f ^ 5 ∧
      DecisionTree.complexity f ≤ 4 * sensitivity f ^ 9 :=
  ⟨certificateComplexity_le_two_mul_sensitivity_pow_five f,
    DecisionTree.complexity_le_four_mul_sensitivity_pow_nine f⟩

/-! ### Axiom checks for headline theorems -/

/--
info: 'Cslib.BitString.sensitivity_threshold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.sensitivity_threshold

/--
info: 'Cslib.QueryComplexity.certificateComplexity_threshold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.QueryComplexity.certificateComplexity_threshold

/--
info: 'Cslib.DecisionTree.complexity_eq_card_of_isSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.DecisionTree.complexity_eq_card_of_isSymmetric

/--
info: 'Cslib.QueryComplexity.certificateComplexityFor_le_sensitivityFor_mul_blockSensitivityFor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms certificateComplexityFor_le_sensitivityFor_mul_blockSensitivityFor

/--
info: 'Cslib.QueryComplexity.certificateComplexity_eq_sensitivity_of_monotone' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.QueryComplexity.certificateComplexity_eq_sensitivity_of_monotone

/--
info: 'Cslib.DecisionTree.complexity_le_four_mul_sensitivity_pow_nine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.DecisionTree.complexity_le_four_mul_sensitivity_pow_nine

end ComplexityTests.QueryComplexity.Relations
