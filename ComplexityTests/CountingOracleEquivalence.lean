/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Oracle.CountingEquivalence

/-!
# Counting-oracle equivalence clients

The clients exercise a nonconstant PP problem, zero-coin and tied majority arithmetic, and
distinct admissible counting oracles that disagree on a non-code word.
-/

namespace ComplexityTests.CountingOracleEquivalence

open Cslib Cslib.Complexity Turing.MultiTapeTM

-- With zero random bits the shifted count is 0 or 2, and bit 1 gives the decision.
example : (2 * 0 + (2 ^ 0 - 1)).testBit 1 = false ∧
    (2 * 1 + (2 ^ 0 - 1)).testBit 1 = true := by decide

-- With two paths a tie is rejected, while accepting both paths gives bit 2.
example : (2 * 1 + (2 ^ 1 - 1)).testBit 2 = false ∧
    (2 * 2 + (2 ^ 1 - 1)).testBit 2 = true := by decide

private theorem true_mem_PP : {b : Bool | b = true} ∈ PP encBool :=
  BPP_subset_PP (P_subset_BPP ⟨id, ComputableInPolyTime.id', fun _ => Iff.rfl⟩)

-- The input hypothesis has a satisfiable, nonconstant instance.
example : ∃ f ∈ SharpP encBool, ∃ q : Polynomial ℕ,
    ∀ b : Bool, b = true ↔ (f b).testBit (q.eval (encBool b).length) = true :=
  exists_SharpP_testBit_of_mem_PP true_mem_PP

example : {b : Bool | b = true} ∈ PWithSharpPOracle encBool :=
  PWithPPOracle_subset_PWithSharpPOracle (PP_subset_PWithPPOracle true_mem_PP)

example : PWithPPOracle encBool = PWithSharpPOracle encBool :=
  PWithPPOracle_eq_PWithSharpPOracle encBool

private def count (b : Bool) : ℕ := if b then 2 else 0

-- The empty word is not a pair code, so changing its answer preserves AnswersBits.
example : AnswersBits encBool count (insert [] (bitGraph encBool count)) := by
  intro b i
  have hne : encPair encBool encNat (b, i) ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [length_encPair, List.length_nil] at this
    lia
  simp only [Set.mem_insert_iff, hne, false_or]
  exact answersBits_bitGraph encBool count b i

example : ([] : List Bool) ∉ bitGraph encBool count := by
  rintro ⟨⟨b, i⟩, _, h⟩
  have := congrArg List.length h
  simp only [length_encPair, List.length_nil] at this
  lia

/--
info: 'Cslib.Complexity.exists_SharpP_testBit_of_mem_PP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.exists_SharpP_testBit_of_mem_PP
/--
info: 'Cslib.Complexity.PWithPPOracle_subset_PWithSharpPOracle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.PWithPPOracle_subset_PWithSharpPOracle
/--
info: 'Cslib.Complexity.PWithPPOracle_eq_PWithSharpPOracle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.PWithPPOracle_eq_PWithSharpPOracle

end ComplexityTests.CountingOracleEquivalence
