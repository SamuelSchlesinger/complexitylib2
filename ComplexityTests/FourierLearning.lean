/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.AC0
import Complexity.MachineLearning.UniformLearning.AC0
import Complexity.MachineLearning.UniformLearning.KushilevitzMansour

/-! Nonvacuity checks for learning from uniform random examples and the low-degree algorithm, and
for learning with membership queries and the Kushilevitz–Mansour algorithm. -/

namespace ComplexityTests.FourierLearning

open Cslib Cslib.MachineLearning Cslib.MachineLearning.UniformLearning Cslib.BitString
  Cslib.Circuits.Boolean Cslib.Probability
open Finset
open scoped NNReal

-- Rounding to the sign: `-1/2` rounds to `true` (the sign `-1`), and `0` rounds to `false`.
example : signRound (fun _ : Fin 1 → Bool => (-1 / 2 : ℝ)) 0 = true := by
  norm_num [signRound]
example : signRound (fun _ : Fin 1 → Bool => (0 : ℝ)) 0 = false := by
  simp [signRound]

-- There are four sets of at most one of three coordinates, below the bound `(3 + 1) ^ 1`.
example : #{S : Finset (Fin 3) | #S ≤ 1} = 4 := by decide
example : #{S : Finset (Fin 3) | #S ≤ 1} ≤ (Fintype.card (Fin 3) + 1) ^ 1 :=
  card_filter_card_le_le_pow 1

/-- The parities of at most `t` coordinates have no Fourier weight above degree `t`. -/
theorem parities_weight {n t : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∀ f ∈ ({f | ∃ U : Finset (Fin n), #U ≤ t ∧ f = parityOn U} :
      PACLearning.ConceptClass (BitString n) Bool),
      ∑ S with t < #S, fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤ ε / 2 := by
  rintro f ⟨U, hU, rfl⟩
  refine le_of_eq_of_le (sum_eq_zero fun S hS => ?_) (by positivity)
  have hSU : S ≠ U := by
    rintro rfl
    have := (mem_filter.1 hS).2
    omega
  simp [fourierCoeff_signVal_parityOn, hSU]

/-- The low-degree algorithm learns the parities of at most `t` coordinates, for every error and
confidence, from enough examples. -/
example {n t : ℕ} {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    Learns (lowDegreeLearner (Fin n) t ⌈4 * #{S : Finset (Fin n) | #S ≤ t} / ε *
      Real.log (2 * #{S : Finset (Fin n) | #S ≤ t} / δ)⌉₊)
      {f | ∃ U : Finset (Fin n), #U ≤ t ∧ f = parityOn U} ε δ :=
  lowDegreeLearner_learns hε hδ (Nat.le_ceil _) (parities_weight hε)

/-- Learning under the uniform distribution gives a PAC learner over the uniform realizable
family, here for the parities of at most `t` coordinates. -/
example {n t : ℕ} (ε δ : Set.Ioo (0 : ℝ≥0) 1) :
    PACLearning.IsPACLearnerFor ⌈4 * #{S : Finset (Fin n) | #S ≤ t} / (ε.val : ℝ) *
      Real.log (2 * #{S : Finset (Fin n) | #S ≤ t} / (δ.val : ℝ))⌉₊ ε δ
      {f | ∃ U : Finset (Fin n), #U ≤ t ∧ f = parityOn U}
      (uniformRealizable {f | ∃ U : Finset (Fin n), #U ≤ t ∧ f = parityOn U}) :=
  Learns.isPACLearnerFor (lowDegreeLearner_learns (by exact_mod_cast ε.2.1)
    (by exact_mod_cast δ.2.1) (Nat.le_ceil _) (parities_weight (by exact_mod_cast ε.2.1)))

/-- A negative client: the learner that always outputs the constant `false` does not learn the
parity of one bit with error below `1 / 2` and confidence above `0`, since its hypothesis always
has error `1 / 2`. -/
example (m : ℕ) {ε δ : ℝ} (hε : ε < 1 / 2) (hδ : δ < 1) :
    ¬ Learns (fun _ : PACLearning.LabeledSample (Fin 1 → Bool) Bool m => fun _ => false)
      {fun x : Fin 1 → Bool => x 0} ε δ := by
  intro h
  have herr : uniformError (fun x : Fin 1 → Bool => x 0) (fun _ => false) = 1 / 2 := by
    have : hammingDist (fun _ : Fin 1 → Bool => false) (fun x : Fin 1 → Bool => x 0) = 1 := by
      decide
    simp [uniformError, this]
  have h1 := h _ rfl
  have huniv : {S : PACLearning.LabeledSample (Fin 1 → Bool) Bool m |
      ε < uniformError (fun x : Fin 1 → Bool => x 0) (fun _ => false)} = Set.univ :=
    Set.eq_univ_of_forall fun _ => by
      rw [Set.mem_ofPred_eq, herr]
      exact hε
  rw [huniv, (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)] at h1
  exact absurd (ENNReal.one_le_ofReal.1 h1) (not_le.2 hδ)

/-- The circuits of depth at most one with one gate compute the constant functions. -/
example (n : ℕ) (b : Bool) : (fun _ : BitString n => b) ∈ circuitClass n 1 1 :=
  ⟨Unbounded.constCircuit (Circuits.Signature.Hom.id _) b, fun x => by
    funext j
    simp [Circuits.single], Unbounded.depth_constCircuit_le _,
    (Unbounded.size_constCircuit _).le⟩

/-- The low-degree algorithm learns circuits of constant depth for every number of inputs, depth,
size, error and confidence, from the number of examples it requires. -/
example (n d g : ℕ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    Learns (lowDegreeLearner (Fin n) (lmnDegree d g ε)
      ⌈4 * #{S : Finset (Fin n) | #S ≤ lmnDegree d g ε} / ε *
        Real.log (2 * #{S : Finset (Fin n) | #S ≤ lmnDegree d g ε} / δ)⌉₊)
      (circuitClass n d g) ε δ :=
  lowDegreeLearner_learns_lmnDegree hε hδ (Nat.le_ceil _)

/-- The hypotheses of the parametric form can be met: for one gate and error `1 / 2`, `s = 3`
gives `4 ≤ (1 / 2) 2 ^ 3`, and depth one needs degree `t = 2 · 8 · 49 - 1 = 783`. -/
example (n m : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hm : 4 * #{S : Finset (Fin n) | #S ≤ 783} / (1 / 2) *
      Real.log (2 * #{S : Finset (Fin n) | #S ≤ 783} / δ) ≤ m) :
    Learns (lowDegreeLearner (Fin n) 783 m) (circuitClass n 1 1) (1 / 2) δ :=
  lowDegreeLearner_learns_circuitClass (s := 3) (by norm_num) hδ (by norm_num)
    (by norm_num) (by norm_num) hm

/-- The failure bound of the low-degree algorithm, for the constant function `true`, whose weight
is all on the empty set. -/
example (n t m : ℕ) :
    (PMF.uniformOfFintype (Fin m → BitString n)).toOuterMeasure
      {x | 1 / 2 < uniformError (fun _ => true)
        (lowDegreeHypothesis t (examples (fun _ => true) x))} ≤
        ENNReal.ofReal (2 * #{S : Finset (Fin n) | #S ≤ t} *
          Real.exp (-(m * (1 / 2)) / (4 * #{S : Finset (Fin n) | #S ≤ t}))) := by
  refine uniform_error_lowDegreeHypothesis_gt_le (ι := Fin n) (ε := 1 / 2) _ t m (by norm_num) ?_
  refine le_of_eq_of_le (sum_eq_zero fun S hS => ?_) (by norm_num)
  have hS : S ≠ ∅ := by
    rintro rfl
    simp at hS
  simp [fourierCoeff_const, hS]

/-! ### The Kushilevitz–Mansour algorithm -/

-- For the set of all coordinates, a bucket holds a single set.
example (F : BitString 3 → ℝ) (S : Finset (Fin 3)) :
    bucketWeight F univ S = fourierCoeff F S ^ 2 :=
  bucketWeight_univ F S

-- The search over `n` coordinates weighs `n + 1` levels.
example : (searchLevels (List.finRange 3)).length = 4 := by simp

/-- The queries of the Kushilevitz–Mansour algorithm: `m (2 n + 3)` for `n` coordinates. -/
example (n m : ℕ) (θ : ℝ) :
    (kmLearner (Fin n) m θ).QueriesAtMost (m * (2 * n + 3)) := by
  simpa using kmLearner_queriesAtMost (ι := Fin n) (m := m) θ

/-- A parity has spectral norm one, so the Kushilevitz–Mansour algorithm learns all parities, for
every error and confidence, from the number of samples it requires. -/
example (n : ℕ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    (kmLearner (Fin n) ⌈512 * 1 ^ 4 / ε ^ 4 * Real.log (2 * (n + 2) * 2 ^ n / δ)⌉₊
      (ε / (2 * 1))).Learns (PMF.uniformOfFintype _) {f | ∃ U, f = parityOn U} ε δ := by
  refine (kmLearner_learns (L := 1) hε hδ (by simpa using Nat.le_ceil _)).mono ?_ le_rfl le_rfl
  rintro f ⟨U, rfl⟩
  simp [spectralNormClass, fourierCoeff_signVal_parityOn, apply_ite]

/-- The decision trees with one leaf compute the constant functions. -/
example (n : ℕ) (b : Bool) : (fun _ : BitString n => b) ∈ decisionTreeClass (Fin n) 1 :=
  ⟨.leaf b, fun _ => rfl, le_rfl⟩

/-- **Decision trees are learnable with membership queries**: for every number of inputs, size,
error and confidence, from the number of samples the algorithm requires. -/
example (n L : ℕ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    (kmLearner (Fin n) ⌈512 * (L : ℝ) ^ 4 / ε ^ 4 * Real.log (2 * (n + 2) * 2 ^ n / δ)⌉₊
      (ε / (2 * L))).Learns (PMF.uniformOfFintype _) (decisionTreeClass (Fin n) L) ε δ :=
  kmLearner_learns_decisionTree hε hδ (by simpa using Nat.le_ceil _)

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
info: 'Cslib.MachineLearning.UniformLearning.uniformExamples_eq_pi' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms uniformExamples_eq_pi

/--
info: 'Cslib.MachineLearning.UniformLearning.Learns.isPACLearnerFor' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Learns.isPACLearnerFor

/--
info: 'Cslib.MachineLearning.UniformLearning.uniform_abs_empiricalCoeff_sub_ge_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms uniform_abs_empiricalCoeff_sub_ge_le

/--
info: 'Cslib.MachineLearning.UniformLearning.uniform_error_lowDegreeHypothesis_gt_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms uniform_error_lowDegreeHypothesis_gt_le

/--
info: 'Cslib.MachineLearning.UniformLearning.lowDegreeLearner_learns' depends on axioms:
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
info: 'Cslib.MachineLearning.UniformLearning.lowDegreeLearner_learns_circuitClass'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms lowDegreeLearner_learns_circuitClass

/--
info: 'Cslib.MachineLearning.UniformLearning.lowDegreeLearner_learns_lmnDegree'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms lowDegreeLearner_learns_lmnDegree

/--
info: 'Cslib.BitString.expect_bucketWeight_sample'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitString.expect_bucketWeight_sample

/--
info: 'Cslib.MachineLearning.UniformLearning.inter_mem_bucketSearch'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms inter_mem_bucketSearch

/--
info: 'Cslib.MachineLearning.UniformLearning.card_bucketSearch_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms card_bucketSearch_le

/--
info: 'Cslib.MachineLearning.UniformLearning.uniformError_kmHypothesis_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms uniformError_kmHypothesis_le

/--
info: 'Cslib.MachineLearning.UniformLearning.uniform_not_accurate_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms uniform_not_accurate_le

/--
info: 'Cslib.MachineLearning.UniformLearning.kmLearner_queriesAtMost'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmLearner_queriesAtMost

/--
info: 'Cslib.MachineLearning.UniformLearning.kmLearner_learns'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmLearner_learns

/--
info: 'Cslib.MachineLearning.UniformLearning.kmLearner_learns_decisionTree'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmLearner_learns_decisionTree

end ComplexityTests.FourierLearning
