/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.HardnessAmplification.WorstCase
import Mathlib.FieldTheory.Finite.GaloisField

/-! Worst-case to average-case reconstruction: the parameter hypotheses of the reconstruction
theorem are jointly satisfiable, over a field of `2 ^ 35` elements, for a function on one bit and
the encoding itself as the predictor; such fields, encodings and embeddings exist; and named axiom
guards for the headline theorems of the development. -/

namespace ComplexityTests.WorstCaseHardness

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Code Finset

/-- Fields of `2 ^ 35` elements exist. -/
example : ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ 35 := by
  refine ⟨GaloisField 2 35, inferInstance, Fintype.ofFinite _, ?_⟩
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 2 35 (by norm_num)

/-- A field of `2 ^ 35` elements has an encoding by `35` bits and contains a copy of
`BitString 1`. -/
example {F : Type*} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ 35) :
    Nonempty (F ≃ BitString 35) ∧ Nonempty (BitString 1 ↪ F) := by
  refine ⟨⟨Fintype.equivOfCardEq (by simp [hF, BitString])⟩,
    Function.Embedding.nonempty_of_card_le (by simp [hF, BitString])⟩

/-- **The reconstruction theorem is not vacuous.** Over a field of `2 ^ 35` elements, with
`K = 11` masks, Sudan parameter `D = 2 ^ 18 + 1` and majority trees of depth `0`, the parameter
hypotheses hold for a function on one bit, with the encoding itself as a predictor agreeing on all
inputs (`ε = 1 / 4`). -/
example {F : Type*} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ 35)
    (enc : F ≃ BitString 35) (h : BitString 1 ↪ F) (f : BooleanFunction (1 * 1)) :
    complexity interpretation (single f) ≤
      reconstructionCost 35 1 1 (2 ^ 18 + 1) 11 0
        (complexity interpretation (single (hardnessEncode enc h f))) (Fintype.card F)
        #(Sudan.monomials (1 * (2 ^ 1 - 1)) (2 ^ 18 + 1)) := by
  refine complexity_le_of_agree_hardnessEncode enc h f le_rfl (ε := 1 / 4) (by norm_num) ?_
    (by norm_num) ?_ (by norm_num) ?_ ?_ ?_ (by norm_num)
  · have : (#{y | hardnessEncode enc h f y = hardnessEncode enc h f y} : ℝ) =
        2 ^ (1 * 35 + 35) := by
      simp [BitString]
      norm_num
    rw [this]
    norm_num
  · norm_num
  · rw [hF]
    have := Sudan.add_one_mul_add_two_le_two_mul_mul_card_monomials (w := 1) le_rfl (2 ^ 18 + 1)
    norm_num at this ⊢
    omega
  · rw [hF]
    norm_num
  · rw [hF]
    norm_num

/-! ### Axioms -/

/--
info: 'Cslib.Circuits.Boolean.complexity_le_of_agree_hardnessEncode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.complexity_le_of_agree_hardnessEncode

/--
info: 'Cslib.Circuits.Boolean.complexity_le_pow_of_agree_hardnessEncode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.complexity_le_pow_of_agree_hardnessEncode

/--
info: 'Cslib.Circuits.Boolean.reconstructionCost_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.reconstructionCost_le

/--
info: 'Cslib.Circuits.Boolean.exists_glPredictor_agree' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.exists_glPredictor_agree

/--
info: 'Cslib.Code.exists_card_lineListDecode_ne_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.exists_card_lineListDecode_ne_le

/--
info: 'Cslib.Code.card_hintDecode_ne_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.card_hintDecode_ne_le

/--
info: 'Cslib.Code.exists_forall_majTree_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.exists_forall_majTree_eq

/--
info: 'Cslib.LinearAlgebra.kernelVec_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.LinearAlgebra.kernelVec_ne_zero

/--
info: 'Cslib.Circuits.Synthesis.bitBlast' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Synthesis.bitBlast

/--
info: 'Cslib.Crypto.GoldreichLevin.exists_card_candidate_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GoldreichLevin.exists_card_candidate_eq

end ComplexityTests.WorstCaseHardness
