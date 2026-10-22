/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Frontier.SourceReduction
import Complexity.Computability.Complexity.SourceReduction

/-!
# Tests for the Chattopadhyay–Liao XOR source reduction and fourth-moment majority certificate

Non-vacuity and `#print axioms` checks for:
* `Complexity.Computability.Circuit.Frontier.SourceReduction.Conditioning`,
* `Complexity.Computability.Circuit.Frontier.SourceReduction.FourthMoment`,
* `Complexity.Computability.Circuit.Frontier.SourceReduction.Moments`,
* `Complexity.Computability.Circuit.Frontier.SourceReduction.Majority`,
* `Complexity.Computability.Circuit.Frontier.SourceReduction.Sampler`,
* `Complexity.Computability.Circuit.Frontier.SourceReduction`, and
* `Complexity.Computability.Complexity.SourceReduction`.
-/

namespace ComplexityTests.SourceReduction

open Cslib Cslib.BitString Cslib.Circuits.Frontier Cslib.Complexity

/-! ### Non-vacuity of `Sampler`, `NeighborCoverage`, and `SomewhereSampler` -/

example : Sampler (fun (_ : BitString 2) (y : BitString 2) => y) 1 (1 / 4) 0 :=
  sampler_seedProjection (by norm_num)

example : NeighborCoverage (fun (_ : BitString 2) (z : BitString 2) => z) 1 1 :=
  neighborCoverage_seedProjection (by decide)

example :
    SomewhereSampler (fun (_ : BitString 2) (_ : BitString 2) (z : BitString 2) => z)
      1 (1 / 4) 0 :=
  somewhereSampler_seedProjection (by norm_num) (by norm_num)

/-! ### Non-vacuity of `ParityBiasBound` and the fourth-moment sign-sum tail bounds -/

/-- A single fair sign coordinate on `Fin 2` has exact zero bias (`ParityBiasBound` with
`δ = 0`). -/
theorem parityBiasBound_fair_single :
    ParityBiasBound (Finset.univ : Finset (Fin 2)) (fun _ => 1 / 2)
      (fun (a : Fin 2) (_ : Fin 1) => if a = 0 then (1 : ℝ) else -1) 0 := by
  intro T hT _
  have hT_eq : T = {0} := by
    ext i
    simp only [Finset.mem_singleton, Fin.eq_zero i, iff_true]
    obtain ⟨j, hj⟩ := hT
    rwa [← Fin.eq_zero j]
  subst hT_eq
  simp [weightedMean, Fin.sum_univ_two]

example :
    (1 / 36 : ℝ) ≤ ∑ a : Fin 2,
      if Real.sqrt (1 : ℕ) / 8 <
          signSum (fun (a : Fin 2) (_ : Fin 1) => if a = 0 then (1 : ℝ) else -1) a
        then (1 / 2 : ℝ) else 0 :=
  signSum_positive_tail_of_parityBias
    (fun _ _ => by norm_num)
    (by simp)
    (by decide)
    (fun a _ _ => by by_cases h : a = 0 <;> simp [h])
    le_rfl
    (by norm_num)
    parityBiasBound_fair_single

/-! ### Non-vacuity of `strictMajority` and `parity` in `Complexity.P encBits` -/

example :
    (Language.ofSlices strictMajority : Set (List Bool)) ∈ P Turing.MultiTapeTM.encBits ∧
      (Language.ofSlices parity : Set (List Bool)) ∈ P Turing.MultiTapeTM.encBits :=
  ⟨ofSlices_strictMajority_mem_P, ofSlices_parity_mem_P⟩

/-! ### Non-vacuity of parameter guards at `b = 5` -/

example :
    0 < sourceReductionOuterCount 5 ∧
      ((sourceReductionOuterCount 5 - sourceReductionOuterCount 5 : ℕ) : ℝ) ≤
        Real.sqrt (sourceReductionOuterCount 5 : ℝ) / 8 :=
  sourceReduction_majority_guards (by decide) le_rfl (by
    have := sourceReductionSamplerError_pos 5
    have := sourceReductionOuterCount_pos 5
    simp only [Nat.sub_self, Nat.cast_zero]
    positivity)

/-! ### Axiom guards -/

/-- info: 'Cslib.Circuits.Frontier.flatSumsetExtractor_iff_sumsetBias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.flatSumsetExtractor_iff_sumsetBias

/-- info: 'Cslib.Circuits.Frontier.SumsetBias.of_many_good_fibers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.SumsetBias.of_many_good_fibers

/--
info: 'Cslib.Circuits.Frontier.fourthMoment_positive_tail_of_approx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.fourthMoment_positive_tail_of_approx

/--
info: 'Cslib.Circuits.Frontier.fourthMoment_negative_tail_of_approx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.fourthMoment_negative_tail_of_approx

/-- info: 'Cslib.Circuits.Frontier.signSum_fourth_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.signSum_fourth_moment

/-- info: 'Cslib.Circuits.Frontier.signSum_tails_of_parityBias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.signSum_tails_of_parityBias

/-- info: 'Cslib.Circuits.Frontier.strictMajority_eq_true_of_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.strictMajority_eq_true_of_margin

/-- info: 'Cslib.Circuits.Frontier.strictMajority_eq_false_of_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.strictMajority_eq_false_of_margin

/--
info: 'Cslib.Circuits.Frontier.strictMajority_mass_ge_of_parityBias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.strictMajority_mass_ge_of_parityBias

/-- info: 'Cslib.Circuits.Frontier.FlatSeededExtractor.sampler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.FlatSeededExtractor.sampler

/--
info: 'Cslib.Circuits.Frontier.FlatSeededExtractor.neighborCoverage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.FlatSeededExtractor.neighborCoverage

/-- info: 'Cslib.Circuits.Frontier.Sampler.amplify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.Sampler.amplify

/--
info: 'Cslib.Circuits.Frontier.affineSourceReduction_parity_bias_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.affineSourceReduction_parity_bias_eq

/-- info: 'Cslib.Circuits.Frontier.card_parityBadSeeds_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.card_parityBadSeeds_le

/-- info: 'Cslib.Circuits.Frontier.SomewhereSampler.parity_fibers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.SomewhereSampler.parity_fibers

/-- info: 'Cslib.Circuits.Frontier.sourceReduction_union_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.sourceReduction_union_budget

/-- info: 'Cslib.Circuits.Frontier.sourceReduction_moment_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.sourceReduction_moment_budget

/-- info: 'Cslib.Circuits.Frontier.sourceReduction_majority_guards' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.sourceReduction_majority_guards

/--
info: 'Cslib.Circuits.Frontier.sumsetBias_strictMajority_affineSourceReduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.sumsetBias_strictMajority_affineSourceReduction

/--
info: 'Cslib.Circuits.Frontier.sumsetDisperser_strictMajority_affineSourceReduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.sumsetDisperser_strictMajority_affineSourceReduction

/-- info: 'Cslib.Circuits.Frontier.ofSlices_strictMajority_mem_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.ofSlices_strictMajority_mem_P

/-- info: 'Cslib.Circuits.Frontier.ofSlices_parity_mem_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.ofSlices_parity_mem_P

/--
info: 'Cslib.Circuits.Frontier.exists_mem_P_eventually_lt_size_of_strictMajority_parity_fibers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  Cslib.Circuits.Frontier.exists_mem_P_eventually_lt_size_of_strictMajority_parity_fibers

/--
info: 'Cslib.Circuits.Frontier.exists_mem_P_eventually_agreement_le_of_strictMajority_parity_fibers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  Cslib.Circuits.Frontier.exists_mem_P_eventually_agreement_le_of_strictMajority_parity_fibers

/--
info: 'Cslib.Circuits.Frontier.exists_mem_P_eventually_lt_size_of_affineSourceReduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Frontier.exists_mem_P_eventually_lt_size_of_affineSourceReduction

end ComplexityTests.SourceReduction
