/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.AC0
import Complexity.Computability.Learning.AC0

/-! Nonvacuity checks for learning from uniform random examples and the low-degree algorithm. -/

namespace ComplexityTests.FourierLearning

open Cslib Cslib.Learning Cslib.BitString Cslib.Circuits.Boolean Cslib.Probability
open Finset

-- Rounding to the sign: `-1/2` rounds to `true` (the sign `-1`), and `0` rounds to `false`.
example : signRound (fun _ : Fin 1 → Bool => (-1 / 2 : ℝ)) 0 = true := by
  norm_num [signRound]
example : signRound (fun _ : Fin 1 → Bool => (0 : ℝ)) 0 = false := by
  simp [signRound]

-- There are four sets of at most one of three coordinates, below the bound `(3 + 1) ^ 1`.
example : #{S : Finset (Fin 3) | #S ≤ 1} = 4 := by decide
example : #{S : Finset (Fin 3) | #S ≤ 1} ≤ (Fintype.card (Fin 3) + 1) ^ 1 :=
  card_filter_card_le_le 1

/-- The parities of at most `t` coordinates have no Fourier weight above degree `t`, so the
low-degree algorithm learns them, for every error and confidence, from enough examples. -/
example {n t : ℕ} {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    (lowDegreeLearner (Fin n) t ⌈4 * #{S : Finset (Fin n) | #S ≤ t} / ε *
      Real.log (2 * #{S : Finset (Fin n) | #S ≤ t} / δ)⌉₊).Learns
      {f | ∃ U : Finset (Fin n), #U ≤ t ∧ f = parityOn U} ε δ := by
  refine lowDegreeLearner_learns hε hδ (Nat.le_ceil _) ?_
  rintro f ⟨U, hU, rfl⟩
  refine le_of_eq_of_le (sum_eq_zero fun S hS => ?_) (by positivity)
  have hSU : S ≠ U := by
    rintro rfl
    have := (mem_filter.1 hS).2
    omega
  simp [fourierCoeff_signVal_parityOn, hSU]

/-- The circuits of depth at most one with one gate compute the constant functions. -/
example (n : ℕ) (b : Bool) :
    (fun _ : BitString n => b) ∈ {f | ∃ C : Circuits.Circuit Unbounded.signature n 1,
      C.Computes Unbounded.interpretation (Circuits.single f) ∧ C.depth ≤ 1 ∧ C.size ≤ 1} :=
  ⟨Unbounded.constCircuit (Circuits.Signature.Hom.id _) b, fun x => by
    funext j
    simp [Circuits.single], Unbounded.depth_constCircuit_le _,
    (Unbounded.size_constCircuit _).le⟩

/-- The low-degree algorithm learns circuits of constant depth for every number of inputs, depth,
size, error and confidence, from the number of examples it requires. -/
example (n d g : ℕ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    (lowDegreeLearner (Fin n) (Unbounded.lmnDegree d g ε)
      ⌈4 * #{S : Finset (Fin n) | #S ≤ Unbounded.lmnDegree d g ε} / ε *
        Real.log (2 * #{S : Finset (Fin n) | #S ≤ Unbounded.lmnDegree d g ε} / δ)⌉₊).Learns
      {f | ∃ C : Circuits.Circuit Unbounded.signature n 1,
        C.Computes Unbounded.interpretation (Circuits.single f) ∧ C.depth ≤ d ∧ C.size ≤ g} ε δ :=
  Unbounded.lowDegreeLearner_learns_lmnDegree hε hδ (Nat.le_ceil _)

/-- The hypotheses of the parametric form can be met: for one gate and error `1 / 2`, `s = 3`
gives `4 ≤ (1 / 2) 2 ^ 3`, and depth one needs degree `t = 2 · 8 · 49 - 1 = 783`. -/
example (n m : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hm : 4 * #{S : Finset (Fin n) | #S ≤ 783} / (1 / 2) *
      Real.log (2 * #{S : Finset (Fin n) | #S ≤ 783} / δ) ≤ m) :
    (lowDegreeLearner (Fin n) 783 m).Learns
      {f | ∃ C : Circuits.Circuit Unbounded.signature n 1,
        C.Computes Unbounded.interpretation (Circuits.single f) ∧ C.depth ≤ 1 ∧ C.size ≤ 1}
      (1 / 2) δ :=
  Unbounded.lowDegreeLearner_learns_of_depth_le (s := 3) (by norm_num) hδ (by norm_num)
    (by norm_num) (by norm_num) hm

/-- The failure bound of the low-degree algorithm, for the constant function `true`, whose weight
is all on the empty set. -/
example (n t m : ℕ) :
    (PMF.uniformOfFintype (Fin m → BitString n)).toOuterMeasure
      {x | 1 / 2 < error (fun _ => true) (lowDegreeHypothesis t (examples (fun _ => true) x))} ≤
        ENNReal.ofReal (2 * #{S : Finset (Fin n) | #S ≤ t} *
          Real.exp (-(m * (1 / 2)) / (4 * #{S : Finset (Fin n) | #S ≤ t}))) := by
  refine uniform_error_lowDegreeHypothesis_gt_le (ι := Fin n) (ε := 1 / 2) _ t m (by norm_num) ?_
  refine le_of_eq_of_le (sum_eq_zero fun S hS => ?_) (by norm_num)
  have hS : S ≠ ∅ := by
    rintro rfl
    simp at hS
  simp [fourierCoeff_const, hS]

/--
info: 'Cslib.BitString.signRound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signRound

/--
info: 'Cslib.BitString.hammingDist_signRound_sum_mul_chi_div_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hammingDist_signRound_sum_mul_chi_div_le

/--
info: 'Cslib.Learning.uniformExamples_eq_pi' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms uniformExamples_eq_pi

/--
info: 'Cslib.Learning.Learner.learns_ofHypothesis_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Learner.learns_ofHypothesis_iff

/--
info: 'Cslib.Learning.uniform_abs_empiricalCoeff_sub_ge_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms uniform_abs_empiricalCoeff_sub_ge_le

/--
info: 'Cslib.Learning.uniform_error_lowDegreeHypothesis_gt_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms uniform_error_lowDegreeHypothesis_gt_le

/--
info: 'Cslib.Learning.lowDegreeLearner_learns' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms lowDegreeLearner_learns

/--
info: 'Cslib.Circuits.Boolean.Unbounded.sum_fourierCoeff_sq_le_of_computes_of_depth_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Unbounded.sum_fourierCoeff_sq_le_of_computes_of_depth_le

/--
info: 'Cslib.Circuits.Boolean.Unbounded.lowDegreeLearner_learns_of_depth_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Unbounded.lowDegreeLearner_learns_of_depth_le

/--
info: 'Cslib.Circuits.Boolean.Unbounded.lowDegreeLearner_learns_lmnDegree' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Unbounded.lowDegreeLearner_learns_lmnDegree

end ComplexityTests.FourierLearning
