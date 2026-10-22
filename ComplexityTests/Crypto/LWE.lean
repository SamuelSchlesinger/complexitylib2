/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Lattice.LWE

/-!
# Tests and Non-Vacuity Witnesses for Lattice Problems and Regev's LWE Reduction
-/

namespace ComplexityTests.Crypto.LWE

open Cslib.Crypto Cslib.Complexity

noncomputable section

/-! ### Concrete Lattice Basis and Transference Bounds -/

/-- A concrete 10-dimensional lattice basis `2 • I_10`. -/
def testBasis10 : LatticeBasis 10 :=
  scaledIdentityBasis 10 2 zero_lt_two

example : lambda1 testBasis10 = 2 := by
  unfold testBasis10
  exact lambda1_scaledIdentityBasis 2 zero_lt_two

example : lambdaN testBasis10 = 2 := by
  unfold testBasis10
  exact lambdaN_scaledIdentityBasis 2 zero_lt_two

example : 0 < lambda1 testBasis10 :=
  lambda1_pos testBasis10

example : lambda1 testBasis10 ≤ lambdaN testBasis10 :=
  lambda1_le_lambdaN testBasis10

example : HasBanaszczykBound testBasis10 :=
  hasBanaszczykBound_scaledIdentityBasis 2 zero_lt_two

example :
    1 ≤ lambda1 testBasis10 * lambdaN (dualBasis testBasis10) ∧
    lambda1 testBasis10 * lambdaN (dualBasis testBasis10) ≤ 10 :=
  banaszczyk_transference_bounds testBasis10
    (hasBanaszczykBound_scaledIdentityBasis 2 zero_lt_two)

/-- `testBasis10` is a yes-instance of `GapSVP 10 4 2`. -/
example : testBasis10 ∈ (GapSVP 10 4 2).yes := by
  rw [mem_yes_GapSVP]
  unfold testBasis10
  exact ⟨hasBanaszczykBound_scaledIdentityBasis 2 zero_lt_two,
    (lambda1_scaledIdentityBasis 2 zero_lt_two).le⟩

/-- `scaledIdentityBasis 10 9` is a no-instance of `GapSVP 10 4 2`. -/
example : scaledIdentityBasis 10 9 (by norm_num) ∈ (GapSVP 10 4 2).no := by
  rw [mem_no_GapSVP_of_one_le (by norm_num) (by norm_num)]
  refine ⟨hasBanaszczykBound_scaledIdentityBasis 9 (by norm_num), ?_⟩
  rw [lambda1_scaledIdentityBasis]
  norm_num

/-! ### Concrete Regev Parameter Regimes (`2 * √n < α * q`) and Non-Vacuity of Oracles -/

/-- Explicit parameter regime in dimension `n = 10`, modulus `q = 105`, noise rate `α = 3 / √10`. -/
theorem testRegevParams10 : RegevParameters 10 105 (3 / Real.sqrt 10) :=
  regevParameters_explicit (by decide : 10 ≤ 10)

/-- Explicit parameter regime in dimension `n = 4`, modulus `q = 21`, and noise rate
`α = 3 / (√4 + 3)`. -/
theorem testRegevParams4 : RegevParameters 4 21 (3 / (Real.sqrt 4 + 3)) :=
  regevParameters_all_pos (by decide : 1 ≤ 4)

/-- Concrete `SearchLWEOracle` in dimension `n = 10`, modulus `q = 105`, and noise rate
`α = 3 / √10`. -/
def testSearchLWEOracle10 : SearchLWEOracle 10 105 (3 / Real.sqrt 10) :=
  canonicalSearchLWEOracle 10 105 (ne_of_gt testRegevParams10.α_pos)

example : Nonempty (SearchLWEOracle 10 105 (3 / Real.sqrt 10)) :=
  nonempty_searchLWEOracle (ne_of_gt testRegevParams10.α_pos)

example : Nonempty (RegevQuantumStepOracle 10 105 (3 / Real.sqrt 10)) :=
  nonempty_regevQuantumStepOracle testRegevParams10

example : regevShrinkFactor 10 105 (3 / Real.sqrt 10) < 1 :=
  regevShrinkFactor_lt_one testRegevParams10

example : 1 ≤ regevApproxFactor 10 (3 / Real.sqrt 10) :=
  one_le_regevApproxFactor testRegevParams10

/-! ### Discrete Gaussian Noise and Dual BDD Instance -/

example : ∑ e : ZMod 105, discreteGaussianProb 105 (3 / Real.sqrt 10) e = 1 :=
  sum_discreteGaussianProb 105 (3 / Real.sqrt 10)

/-- Concrete `DualBDDInstance` on `testBasis10` with zero offset. -/
def testDualBDD : DualBDDInstance testBasis10 (bddRadius 105 (3 / Real.sqrt 10) 2) where
  secretCoords := fun i => (i.val : ℤ)
  offset := 0
  offset_norm_le := by
    have h0 : euclideanNorm (0 : Fin 10 → ℝ) = 0 := by
      unfold euclideanNorm
      simp
    rw [h0]
    exact (bddRadius_pos testRegevParams10 zero_lt_two).le

example :
    solveDualBDDModQ testSearchLWEOracle10 testBasis10 testDualBDD.target =
      fun j => (testDualBDD.secretCoords j : ZMod 105) := by
  apply solveDualBDDModQ_eq_secretCoords
  intro i
  change |(testBasis10.matrix.mulVec _) ⬝ᵥ (0 : Fin 10 → ℝ)| < 1 / 2
  rw [dotProduct_zero, abs_zero]
  norm_num

example (a : Fin 10 → ℤ) :
    |(testBasis10.matrix.mulVec (fun j => (a j : ℝ))) ⬝ᵥ testDualBDD.offset| ≤
      (3 / Real.sqrt 10) * 105 / Real.sqrt 2 := by
  change |(testBasis10.matrix.mulVec (fun j => (a j : ℝ))) ⬝ᵥ (0 : Fin 10 → ℝ)| ≤ _
  rw [dotProduct_zero, abs_zero]
  positivity

/-! ### Axiom Guards for Headline Results -/

/--
info: 'Cslib.Crypto.lambda1_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.lambda1_pos

/--
info: 'Cslib.Crypto.lambda1_le_lambdaN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.lambda1_le_lambdaN

/--
info: 'Cslib.Crypto.one_le_lambda1_mul_lambdaN_dualBasis' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.one_le_lambda1_mul_lambdaN_dualBasis

/--
info: 'Cslib.Crypto.banaszczyk_transference_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.banaszczyk_transference_bounds

/--
info: 'Cslib.Crypto.regevParameters_explicit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.regevParameters_explicit

/--
info: 'Cslib.Crypto.regevParameters_all_pos' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.regevParameters_all_pos

/--
info: 'Cslib.Crypto.lweSamplePMF_injective' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.lweSamplePMF_injective

/--
info: 'Cslib.Crypto.nonempty_searchLWEOracle' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.nonempty_searchLWEOracle

/--
info: 'Cslib.Crypto.bddSampleFromTarget_eq_lweSampleFromNoise' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.bddSampleFromTarget_eq_lweSampleFromNoise

/--
info: 'Cslib.Crypto.solveDualBDDModQ_eq_secretCoords' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.solveDualBDDModQ_eq_secretCoords

/--
info: 'Cslib.Crypto.nonempty_regevQuantumStepOracle' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.nonempty_regevQuantumStepOracle

/--
info: 'Cslib.Crypto.regev_lwe_to_sivp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.regev_lwe_to_sivp

/--
info: 'Cslib.Crypto.regev_lwe_to_gapsvp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.regev_lwe_to_gapsvp

/--
info: 'Cslib.Crypto.regev_lwe_to_sivp_gapsvp' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.regev_lwe_to_sivp_gapsvp

end

end ComplexityTests.Crypto.LWE
