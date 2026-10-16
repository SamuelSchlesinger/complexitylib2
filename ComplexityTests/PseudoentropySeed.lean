/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Pseudoentropy.Seed
import Complexity.Tactic.PPT

/-! Saved-seed contracts, unused randomness and supported-score concentration. -/

namespace ComplexityTests.PseudoentropySeed

open Cslib Cslib.Probability Cslib.Probability.PMF Cslib.Crypto.Pseudoentropy
open Turing.MultiTapeTM

-- Arbitrary, possibly biased, independent bits: no uniformity assumption on the marginals.
example (count : ℕ) (p : Fin count → PMF Bool) {ε : ℝ} (hε : 0 ≤ ε) :
    ((pi p).toOuterMeasure {outcome |
      ε ≤ |(∑ i, if outcome i then (1 : ℝ) else 0) - ∑ i, (p i true).toReal|}).toReal ≤
      2 * Real.exp (-2 * ε ^ 2 / count) := by
  simpa [Fintype.sum_bool] using pi_sum_abs_sub_mean_ge p
    (fun _ bit => if bit then (1 : ℝ) else 0) (by norm_num : (0 : ℝ) ≤ 1)
    (fun _ bit _ => by cases bit <;> simp) hε

-- Zero coordinates and a zero score bound remain legitimate inputs to the theorem.
example :
    ((pi (fun _ : Fin 0 => PMF.pure false)).toOuterMeasure {outcome |
      (∑ i, if outcome i then (100 : ℝ) else 0) ≤ 0}).toReal = 1 := by
  rw [(PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (by intro outcome _; simp)]
  rfl

-- The bound is required only on supported values; the impossible score can be 100.
example (count : ℕ) :
    ((pi (fun _ : Fin count => PMF.pure false)).toOuterMeasure {outcome |
      (∑ i, if outcome i then (100 : ℝ) else 0) ≤ 0}).toReal ≤ 1 := by
  simpa using pi_sum_le_mean_sub (fun _ : Fin count => PMF.pure false)
    (fun _ bit => if bit then (100 : ℝ) else 0) (bound := 0) (ε := 0) le_rfl
    (fun _ bit h => by simpa using h) le_rfl

private noncomputable def fairPair : SamplablePair where
  Observation _ := Unit
  finite _ := inferInstance
  encode _ := ⟨fun _ => [], fun _ _ _ => Subsingleton.elim _ _⟩
  joint _ := (uniformOfFintype Bool).map ((), ·)
  sample _ := (fun bit => ([], bit)) <$> ProbComp.uniform Bool
  efficient := by ppt
  eval_sample _ := by
    simp only [ProbComp.eval_map, ProbComp.eval_uniform, PMF.map_comp, Function.comp_def]
    rfl

-- The evaluator reads one bit and deliberately ignores all remaining seed bits.
private noncomputable def paddedSeed : fairPair.SeedRealization where
  length n := n + 1
  length_isPolyTime := by fun_prop
  evaluate _ bits := ([], bits.headD false)
  efficient := by fun_prop
  distribution n := by
    simp only [BitString.uniformList_succ, Function.comp_def, List.headD_cons, PMF.map,
      PMF.bind_const, fairPair, PMF.bind_bind, PMF.pure_bind]
    rfl

example : Nonempty fairPair.SeedRealization := fairPair.exists_seedRealization

-- The evaluator is total on malformed seeds too; here an empty seed returns the default bit.
example : paddedSeed.evaluate 7 [] = ([], false) := rfl

-- The complete seed/output experiment is efficient under its ordinary pair encoding.
example : IsPPTOn encUnary (encPair (encPair encBits encBool) encBits)
    paddedSeed.sampleWithSeed := by ppt

-- Captured input and an alternative input encoding compose through the same certificate.
example : IsPPTOn (encPair encBool encUnary) (encPair (encPair encBits encBool) encBits)
    (fun input : Bool × ℕ => paddedSeed.sampleWithSeed input.2) := by ppt

-- An explicit bind spells the same sampler without a specialized tactic syntax rule.
example : IsPPTOn encUnary (encPair (encPair encBits encBool) encBits)
    (fun n => BitString.sampleList (n + 1) >>= fun bits =>
      pure (([], bits.headD false), bits)) := by
  ppt

example (n : ℕ) : ProbComp.eval (paddedSeed.sampleWithSeed n) =
    (paddedSeed.jointWithSeed n).map (fun result => (([], result.1.2), List.ofFn result.2)) :=
  paddedSeed.eval_sampleWithSeed n

-- Exactly n unused random bits remain after disclosing the hidden bit and the constant observation.
example (n : ℕ) : conditionalEntropy (paddedSeed.jointWithSeed n) = n := by
  have h := paddedSeed.entropy_chain_rule n
  change entropy (((uniformOfFintype Bool).map ((), ·)).map Prod.fst) +
    conditionalEntropy ((uniformOfFintype Bool).map ((), ·)) +
    conditionalEntropy (paddedSeed.jointWithSeed n) = ((n + 1 : ℕ) : ℝ) at h
  rw [conditionalEntropy_map_const, entropy_uniform] at h
  norm_num [PMF.map_comp, Function.comp_def, PMF.map, PMF.bind_const] at h
  linarith

end ComplexityTests.PseudoentropySeed
