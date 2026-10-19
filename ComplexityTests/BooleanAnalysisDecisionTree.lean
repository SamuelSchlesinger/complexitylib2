/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.DecisionTree.Granularity
import Complexity.Computability.DecisionTree.Influence
import Complexity.Computability.DecisionTree.SpectralNorm
import Complexity.Computability.QueryComplexity.Degree
import Complexity.Computability.QueryComplexity.Monotone
import Complexity.Foundations.BooleanAnalysis.Decomposition
import Complexity.Foundations.BooleanAnalysis.Monotone
import Complexity.Foundations.BooleanAnalysis.RelevantCoordinates

/-! Clients and axiom guards for the Fourier analysis of decision trees, of low-degree Boolean
functions and of monotone Boolean functions. -/

namespace ComplexityTests.BooleanAnalysisDecisionTree

open Cslib Cslib.BitString Finset Function
open scoped BigOperators

/-- The conjunction of bits `0` and `1` of three, as a decision tree of depth two. -/
def andTree : DecisionTree (Fin 3) Bool :=
  .node 0 (.leaf false) (.node 1 (.leaf false) (.leaf true))

example : andTree.depth = 2 ∧ andTree.leafCount = 3 := ⟨rfl, rfl⟩

/-- The degree hypothesis of the low-degree results, discharged by the depth of a tree. -/
theorem fourierCoeff_andTree_eq_zero (S : Finset (Fin 3)) (hS : 2 < #S) :
    fourierCoeff (fun x => signVal (andTree.eval x)) S = 0 :=
  DecisionTree.fourierCoeff_eq_zero_of_depth_lt (fun b => signVal b) andTree hS

-- The degree hypothesis is satisfiable: the Nisan–Szegedy bound for a concrete tree.
example : #{i | ∃ x, andTree.eval (update x i !x i) ≠ andTree.eval x} ≤ 2 * 2 ^ (2 - 1) :=
  card_filter_exists_update_ne_le (fun x => andTree.eval x) fourierCoeff_andTree_eq_zero

example : totalInfluence (fun x => signVal (andTree.eval x)) ≤ 2 :=
  totalInfluence_signVal_le_of_degree (fun x => andTree.eval x) fourierCoeff_andTree_eq_zero

-- The tree reads only bits `0` and `1`, and the count of relevant coordinates is exact.
example : #{i | ∃ x, andTree.eval (update x i !x i) ≠ andTree.eval x} = 2 := by decide

-- Bit `2` is irrelevant, so it has influence zero.
example : influence 2 (fun x => signVal (andTree.eval x)) = 0 :=
  not_not.1 ((influence_signVal_ne_zero_iff (fun x => andTree.eval x) 2).not.2 (by decide))

-- Bit `0` is relevant, so it has nonzero influence, at least `2 ^ (1 - 2)`.
example : 1 ≤ 2 ^ (2 - 1) * influence 0 (fun x => signVal (andTree.eval x)) :=
  one_le_two_pow_mul_influence_of_degree (fun x => andTree.eval x) fourierCoeff_andTree_eq_zero 0
    ((influence_signVal_ne_zero_iff (fun x => andTree.eval x) 0).2 ⟨fun _ => true, by decide⟩)

-- The degree hypothesis also holds with `d = deg(f)` for every Boolean function.
example {n : ℕ} (f : BooleanFunction n) :
    #{i | ∃ x, f (update x i !x i) ≠ f x} ≤
      QueryComplexity.degree f * 2 ^ (QueryComplexity.degree f - 1) :=
  card_filter_exists_update_ne_le f fun _ hS => by
    by_contra h
    exact hS.not_ge (QueryComplexity.card_le_degree_of_fourierCoeff_ne_zero h)

-- Granularity, spectral norm and sparsity of the conjunction of two bits.
example (S : Finset (Fin 3)) :
    ∃ m : ℤ, fourierCoeff (fun x => signVal (andTree.eval x)) S = m / 2 := by
  have h :=
    DecisionTree.exists_fourierCoeff_signVal_eq_intCast_div_two_pow_depth_sub_one id andTree S
  rwa [show andTree.depth - 1 = 1 from rfl, pow_one] at h

example : ∑ S, |fourierCoeff (fun x => signVal (andTree.eval x)) S| ≤ 3 := by
  exact_mod_cast DecisionTree.sum_abs_fourierCoeff_signVal_le_leafCount id andTree

example : #{S | fourierCoeff (fun x => signVal (andTree.eval x)) S ≠ 0} ≤ 6 :=
  DecisionTree.card_filter_fourierCoeff_signVal_ne_zero_le id andTree

example : andTree.leafCount ≤ 2 ^ andTree.depth :=
  DecisionTree.leafCount_le_two_pow_depth andTree

example : totalInfluence (fun x => signVal (andTree.eval x)) ≤ andTree.depth :=
  DecisionTree.totalInfluence_le_depth id andTree

-- Majority is monotone, so its total influence is at most `√n`.
example (n : ℕ) : totalInfluence (fun x => signVal (majority n x)) ≤ √n := by
  have h := totalInfluence_le_sqrt_card_of_monotone (f := majority n) (monotone_threshold _)
  rwa [Fintype.card_fin] at h

-- Its negation is antitone, with the same bound.
example (n : ℕ) : totalInfluence (fun x => signVal (!majority n x)) ≤ √n := by
  have h := totalInfluence_le_sqrt_card_of_antitone (f := fun x => !majority n x)
    fun x y hxy => by
      have h := monotone_threshold (n := n) ((n + 1) / 2) hxy
      change (!threshold n ((n + 1) / 2) y) ≤ !threshold n ((n + 1) / 2) x
      revert h
      cases threshold n ((n + 1) / 2) x <;> cases threshold n ((n + 1) / 2) y <;> decide
  rwa [Fintype.card_fin] at h

-- The decomposition along a bit and the reindexing by a symmetric difference.
example (f : (Fin 3 → Bool) → ℝ) (x : Fin 3 → Bool) :
    f x = (f (update x 0 false) + f (update x 0 true)) / 2 + chi ℝ {0} x * derivative 0 f x :=
  eq_add_chi_mul_derivative 0 f x

example (f : (Fin 3 → Bool) → ℝ) : fourierCoeff f {0} = 𝔼 x, derivative 0 f x :=
  fourierCoeff_singleton_eq_expect_derivative 0 f

example (F : Finset (Fin 3) → ℝ) : ∑ S, F (symmDiff {0} S) = ∑ S, F S :=
  Fintype.sum_symmDiff {0} F

/-! ### Axiom guards -/

/-- info: 'Fintype.sum_symmDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Fintype.sum_symmDiff

/-- info: 'Cslib.BitString.fourierCoeff_cond' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BitString.fourierCoeff_cond

/-- info: 'Cslib.BitString.eq_add_chi_mul_derivative' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BitString.eq_add_chi_mul_derivative

/-- info: 'Cslib.BitString.fourierCoeff_singleton_eq_expect_derivative' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BitString.fourierCoeff_singleton_eq_expect_derivative

/-- info: 'Cslib.BitString.influence_signVal_ne_zero_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BitString.influence_signVal_ne_zero_iff

/-- info: 'Cslib.BitString.totalInfluence_le_sqrt_card_mul_of_monotone' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BitString.totalInfluence_le_sqrt_card_mul_of_monotone

/-- info: 'Cslib.BitString.totalInfluence_le_sqrt_card_of_antitone' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BitString.totalInfluence_le_sqrt_card_of_antitone

/-- info: 'Cslib.BitString.one_le_two_pow_mul_dens_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BitString.one_le_two_pow_mul_dens_ne_zero

/-- info: 'Cslib.BitString.card_filter_exists_update_ne_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BitString.card_filter_exists_update_ne_le

/-- info: 'Cslib.DecisionTree.card_filter_fourierCoeff_signVal_ne_zero_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecisionTree.card_filter_fourierCoeff_signVal_ne_zero_le

/-- info: 'Cslib.DecisionTree.leafCount_le_two_pow_depth' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms DecisionTree.leafCount_le_two_pow_depth

end ComplexityTests.BooleanAnalysisDecisionTree
