/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.DecisionTree.Parity
import Complexity.Computability.QueryComplexity.Huang
import Complexity.Computability.QueryComplexity.Relations

/-! Degree, Nisan's relations and Huang's sensitivity theorem on concrete functions: parity,
disjunction and conjunction of `n` bits, majority of three bits and the address function with one
address bit. Non-vacuity witnesses for the induced subgraph theorem, and axiom guards for the
headline theorems. -/

namespace ComplexityTests.QueryComplexity.Measures

open Cslib Cslib.BitString Cslib.QueryComplexity Finset

/-! ### Disjunction and conjunction of `n` bits -/

/-- The disjunction is sensitive to every bit at the all-false input. -/
private theorem sensitivityAt_or {n : ℕ} :
    sensitivityAt (threshold n 1) (fun _ => false) = n := by
  have h : sensitiveCoords (threshold n 1) (fun _ => false) = univ :=
    eq_univ_of_forall fun i => mem_sensitiveCoords.2 (by
      rw [IsSensitiveCoord, threshold_one_right, threshold_one_right]
      simp only [Bool.not_false, ne_eq, decide_eq_decide]
      exact fun h => absurd (h.1 ⟨i, by simp⟩) (by simp))
  rw [sensitivityAt, h, card_univ, Fintype.card_fin]

/-- The conjunction is sensitive to every bit at the all-true input. -/
private theorem sensitivityAt_and {n : ℕ} :
    sensitivityAt (threshold n n) (fun _ => true) = n := by
  have h : sensitiveCoords (threshold n n) (fun _ => true) = univ :=
    eq_univ_of_forall fun i => mem_sensitiveCoords.2 (by
      rw [IsSensitiveCoord, threshold_self, threshold_self]
      simp only [Bool.not_true, ne_eq, decide_eq_decide]
      exact fun h => absurd (h.2 (fun _ => trivial) i) (by simp))
  rw [sensitivityAt, h, card_univ, Fintype.card_fin]

example {n : ℕ} : degree (threshold n 1) = n ∧ sensitivity (threshold n 1) = n ∧
    DecisionTree.complexity (threshold n 1) = n :=
  ⟨degree_threshold_one,
    le_antisymm (sensitivity_le_card _) (sensitivityAt_or.symm.trans_le
      (sensitivityAt_le_sensitivity _ _)),
    DecisionTree.complexity_eq_card_of_sensitivityAt_eq_card sensitivityAt_or⟩

example {n : ℕ} : degree (threshold n n) = n ∧ sensitivity (threshold n n) = n ∧
    DecisionTree.complexity (threshold n n) = n :=
  ⟨degree_threshold_self,
    le_antisymm (sensitivity_le_card _) (sensitivityAt_and.symm.trans_le
      (sensitivityAt_le_sensitivity _ _)),
    DecisionTree.complexity_eq_card_of_sensitivityAt_eq_card sensitivityAt_and⟩

/-! ### Parity -/

example {n : ℕ} : degree (parity n) = n ∧ sensitivity (parity n) = n :=
  ⟨degree_parity, sensitivity_parity⟩

/-- Parity of three bits is not a combination of monomials of two coordinates. -/
example : (fun x : BitString 3 => bitVal ℝ (parity 3 x)) ∉ lowDegree ℝ (Fin 3) 2 := fun h => by
  have := QueryComplexity.degree_le_iff_mem_lowDegree.2 h
  rw [degree_parity] at this
  omega

/-- Read as signs, parity of two bits has its weight on the set of both coordinates. -/
example : fourierCoeff (fun x : BitString 2 => signVal (parity 2 x)) univ ≠ 0 := by
  rw [parity, fourierCoeff_signVal_parityOn]
  simp

/-! ### Majority of three bits and the address function -/

/-- The address function with one address bit: bit `0` selects bit `1` or bit `2`. -/
private def address : BooleanFunction 3 := fun x => if x 0 then x 2 else x 1

example : sensitivity (majority 3) = 2 ∧ blockSensitivity (majority 3) = 2 ∧
    certificateComplexity (majority 3) = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

example : sensitivity address = 2 ∧ blockSensitivity address = 2 ∧
    certificateComplexity address = 2 ∧ blockSensitivityFor address false = 2 ∧
    certificateComplexityFor address true = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Huang's theorem bounds the degree of majority of three bits by `s² = 4`. -/
example : degree (majority 3) ≤ 4 := by
  have h := degree_le_sensitivity_sq (majority 3)
  rwa [show sensitivity (majority 3) = 2 by decide] at h

/-- Nisan's bounds for the address function: `C ≤ s bs = 4` and `D ≤ bs₀ C₁ = 4`. -/
example : certificateComplexity address ≤ 4 ∧ DecisionTree.complexity address ≤ 4 := by
  have h₁ := certificateComplexity_le_sensitivity_mul_blockSensitivity address
  have h₂ := DecisionTree.complexity_le_blockSensitivityFor_mul_certificateComplexityFor address
  rw [show sensitivity address = 2 by decide, show blockSensitivity address = 2 by decide] at h₁
  rw [show blockSensitivityFor address false = 2 by decide,
    show certificateComplexityFor address true = 2 by decide] at h₂
  exact ⟨h₁, h₂⟩

/-! ### The general bounds -/

example {n : ℕ} (f : BooleanFunction n) :
    degree f ≤ DecisionTree.complexity f ∧ degree f ≤ sensitivity f ^ 2 ∧
      √(degree f : ℝ) ≤ sensitivity f :=
  ⟨DecisionTree.degree_le_complexity f, degree_le_sensitivity_sq f,
    sqrt_degree_le_sensitivity f⟩

example {n : ℕ} (f : BooleanFunction n) :
    certificateComplexity f ≤ sensitivity f * blockSensitivity f ∧
      DecisionTree.complexity f ≤ certificateComplexity f * blockSensitivity f ∧
      DecisionTree.complexity f ≤ blockSensitivity f ^ 3 :=
  ⟨certificateComplexity_le_sensitivity_mul_blockSensitivity f,
    DecisionTree.complexity_le_certificateComplexity_mul_blockSensitivity f,
    DecisionTree.complexity_le_blockSensitivity_pow_three f⟩

/-- A decision tree of depth one computes a function of degree at most one. -/
example : totalDegree (fun x : BitString 2 =>
    bitVal ℝ ((DecisionTree.node (0 : Fin 2) (.leaf false) (.leaf true)).eval x)) ≤ 1 :=
  DecisionTree.totalDegree_comp_eval_le _ _

/-! ### The induced subgraph theorem -/

/-- The hypothesis is satisfiable: the whole cube has more than half of its points. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] :
    2 ^ Fintype.card ι < 2 * #(univ : Finset (ι → Bool)) := by
  rw [card_univ, Fintype.card_fun, Fintype.card_bool]
  have := Nat.two_pow_pos (Fintype.card ι)
  omega

/-- Three of the four points of the square: one of them has both neighbors in the set. -/
example : ∃ x ∈ ({![false, false], ![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
    2 ≤ #{i | Function.update x i (!x i) ∈
      ({![false, false], ![true, false], ![false, true]} : Finset (Fin 2 → Bool))} := by
  obtain ⟨x, hx, h⟩ := exists_mem_sqrt_card_le_card_update_mem
    (V := {![false, false], ![true, false], ![false, true]}) (by decide) (univ : Finset (Fin 2))
  refine ⟨x, hx, ?_⟩
  rw [card_univ, Fintype.card_fin] at h
  have h1 : (1 : ℝ) < √(2 : ℕ) := by
    rw [Real.lt_sqrt zero_le_one]
    norm_num
  exact_mod_cast h1.trans_le h

example {ι : Type*} [LinearOrder ι] (S : Finset ι) (v : (ι → Bool) → ℝ) :
    signedAdjacency S (signedAdjacency S v) = (#S : ℝ) • v :=
  signedAdjacency_signedAdjacency S v

/-! ### Axiom checks for headline theorems -/

/--
info: 'Cslib.BitString.mem_lowDegree_iff_fourierCoeff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.mem_lowDegree_iff_fourierCoeff

/--
info: 'Cslib.DecisionTree.degree_le_complexity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.DecisionTree.degree_le_complexity

/--
info: 'Cslib.QueryComplexity.certificateComplexity_le_sensitivity_mul_blockSensitivity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.QueryComplexity.certificateComplexity_le_sensitivity_mul_blockSensitivity

/--
info: 'Cslib.DecisionTree.complexity_le_blockSensitivityFor_mul_certificateComplexityFor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.DecisionTree.complexity_le_blockSensitivityFor_mul_certificateComplexityFor

/--
info: 'Cslib.DecisionTree.complexity_le_blockSensitivity_pow_three' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.DecisionTree.complexity_le_blockSensitivity_pow_three

/--
info: 'Cslib.BitString.exists_mem_sqrt_card_le_card_update_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.exists_mem_sqrt_card_le_card_update_mem

/--
info: 'Cslib.QueryComplexity.degree_le_sensitivity_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.QueryComplexity.degree_le_sensitivity_sq

/--
info: 'Cslib.QueryComplexity.sqrt_degree_le_sensitivity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.QueryComplexity.sqrt_degree_le_sensitivity

end ComplexityTests.QueryComplexity.Measures
