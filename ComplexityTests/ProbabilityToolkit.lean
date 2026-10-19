/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.Chernoff
import Complexity.Probability.KWiseIndependent.Polynomial
import Complexity.Probability.LocalLemma
import Complexity.Probability.PairwiseIndependentHash.Affine
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Multiplicative Chernoff bounds, `k`-wise independent hashing and the Lovász Local Lemma:
concrete instances, satisfiable hypotheses, a boundary case and axiom guards. -/

namespace ComplexityTests.ProbabilityToolkit

open Cslib Cslib.Probability Finset
open scoped BigOperators

/-! ### Chernoff bounds -/

/-- The fair-coin score `1` for `true`. -/
private def coin (_ : Fin 10) (b : Bool) : ℝ := if b then 1 else 0

private theorem coin_mem (i : Fin 10) (b : Bool) : coin i b ∈ Set.Icc 0 1 := by
  cases b <;> simp [coin]

private theorem mean_coin :
    ∑ i : Fin 10, ∑ b, ((PMF.uniformOfFintype Bool) b).toReal * coin i b = 5 := by
  simp [coin, PMF.uniformOfFintype_apply]
  norm_num

-- The upper tails for ten fair coins: the sharp and the simplified bounds apply.
example (δ : ℝ) (hδ : 0 ≤ δ) :
    ((PMF.pi fun _ : Fin 10 => PMF.uniformOfFintype Bool).toOuterMeasure
      {outcome | (1 + δ) * 5 ≤ ∑ i, coin i (outcome i)}).toReal ≤
        Real.exp (5 * (δ - (1 + δ) * Real.log (1 + δ))) :=
  PMF.pi_sum_ge_one_add_mul_le_exp_log (fun _ => PMF.uniformOfFintype Bool) coin
    (fun i b _ => coin_mem i b) mean_coin.le hδ

example (δ : ℝ) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    ((PMF.pi fun _ : Fin 10 => PMF.uniformOfFintype Bool).toOuterMeasure
      {outcome | (1 + δ) * 5 ≤ ∑ i, coin i (outcome i)}).toReal ≤
        Real.exp (-(δ ^ 2 * 5 / 3)) :=
  PMF.pi_sum_ge_one_add_mul_of_le_one (fun _ => PMF.uniformOfFintype Bool) coin
    (fun i b _ => coin_mem i b) mean_coin.le hδ hδ₁

-- The lower tail for ten fair coins: the hypotheses on the scores are satisfiable.
example (δ : ℝ) (hδ : 0 ≤ δ) :
    ((PMF.pi fun _ : Fin 10 => PMF.uniformOfFintype Bool).toOuterMeasure
      {outcome | ∑ i, coin i (outcome i) ≤ (1 - δ) * 5}).toReal ≤
        Real.exp (-(δ ^ 2 * 5 / 2)) :=
  PMF.pi_sum_le_one_sub_mul (fun _ => PMF.uniformOfFintype Bool) coin
    (fun i b _ => coin_mem i b) mean_coin.ge hδ

/-! ### `k`-wise independence -/

instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

-- The polynomials of degree less than three over `𝔽₅` form a 3-wise independent family.
example : IsKWiseIndependentHash 3 (polynomialHash : (Fin 3 → ZMod 5) → ZMod 5 → ZMod 5) :=
  isKWiseIndependentHash_polynomialHash 3

-- Pairwise independent families, such as the affine maps of bit vectors, are 2-wise independent.
example : IsKWiseIndependentHash 2
    (affineHash : Matrix (Fin 2) (Fin 3) (ZMod 2) × (Fin 2 → ZMod 2) → (Fin 3 → ZMod 2) →
      Fin 2 → ZMod 2) :=
  isKWiseIndependentHash_two_iff.2 ⟨isPairwiseIndependentHash_affineHash, ⟨0⟩⟩

-- Affine polynomials are pairwise independent ...
example : IsPairwiseIndependentHash (polynomialHash : (Fin 2 → ZMod 5) → ZMod 5 → ZMod 5) :=
  (isKWiseIndependentHash_polynomialHash 2).isPairwiseIndependentHash le_rfl

-- ... but not 3-wise independent: their 25 seeds cannot give a value pattern at three points
-- probability `1 / 125`.
example : ¬ IsKWiseIndependentHash 3 (polynomialHash : (Fin 2 → ZMod 5) → ZMod 5 → ZMod 5) := by
  intro hh
  have h := hh.dens_filter_restrict_eq (T := {0, 1, 2}) (by decide) fun _ => 0
  rw [dens_eq_card_div_card, show #({0, 1, 2} : Finset (ZMod 5)) = 3 by decide] at h
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card] at h
  have h' := congrArg (fun q : ℚ≥0 => (q : ℚ) * 125) h
  norm_num at h'
  have : ((#{c : Fin 2 → ZMod 5 | ({0, 1, 2} : Finset (ZMod 5)).restrict (polynomialHash c) =
      fun _ => 0} : ℕ) : ℚ) * 5 = 1 := by linarith
  norm_cast at this

-- The tail bound for 4-wise independent polynomial hashing of `[0, 1]`-valued scores.
example (S : Finset (ZMod 5)) (g : ZMod 5 → ZMod 5 → ℝ)
    (hg : ∀ x ∈ S, ∀ y, g x y ∈ Set.Icc 0 1) :
    (dens {c : Fin (2 * 2) → ZMod 5 |
      1 ≤ |∑ x ∈ S, (g x (polynomialHash c x) - 𝔼 y, g x y)|} : ℝ) ≤
        ((2 : ℕ) ^ 2 * #S / 1 ^ 2) ^ 2 :=
  (isKWiseIndependentHash_polynomialHash (2 * 2)).dens_filter_le_abs_sum_sub_expect S g hg
    one_pos

/-! ### The Lovász Local Lemma -/

/-- A coordinate of a uniform tuple of bits is `true` with probability `1 / 2`. -/
private theorem toReal_pi_eq_true {n : ℕ} (i : Fin n) :
    ((PMF.pi fun _ : Fin n => PMF.uniformOfFintype Bool).toOuterMeasure
      {ω | ω i = true}).toReal = 1 / 2 := by
  have h := PMF.toOuterMeasure_map_apply (fun ω : Fin n → Bool => ω i)
    (PMF.pi fun _ : Fin n => PMF.uniformOfFintype Bool) {true}
  rw [PMF.pi_map_eval] at h
  rw [show {ω : Fin n → Bool | ω i = true} = (fun ω => ω i) ⁻¹' {true} from rfl, ← h,
    PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply]
  simp

-- Two independent fair coins: the asymmetric bound `(1 - 1/2) (1 - 1/2)` for "no coin is
-- `true`" is attained.
example : (1 - 1 / 2 : ℝ) * (1 - 1 / 2) ≤
    ((PMF.pi fun _ : Fin 2 => PMF.uniformOfFintype Bool).toOuterMeasure
      (⋂ i, {ω | ω i = true}ᶜ)).toReal := by
  have h := PMF.prod_one_sub_le_pi_iInter_compl (fun _ : Fin 2 => PMF.uniformOfFintype Bool)
    (fun i => {ω | ω i = true}) (fun i => {i})
    (fun i ω ω' h => by simp only [Set.mem_ofPred_eq, h i (by simp)])
    (fun _ => ∅) (fun i j hji hij => absurd (disjoint_singleton.2 hji.symm) hij)
    (fun _ => 1 / 2) (fun _ => by norm_num) fun i => by
      rw [toReal_pi_eq_true, prod_empty, mul_one]
  simpa only [Fin.prod_univ_two] using h

/-- The first coin of each pair. -/
private def first : Fin 2 → Fin 4 := ![0, 2]

/-- The second coin of each pair. -/
private def second : Fin 2 → Fin 4 := ![1, 3]

-- Two events, each requiring both coins of its own pair out of four to be `true`, on disjoint
-- coordinates: the symmetric local lemma with `d = 0` and `q = 1 / 4` avoids both.
example : 0 < ((PMF.pi fun _ : Fin 4 => PMF.uniformOfFintype Bool).toOuterMeasure
    (⋂ i : Fin 2, {ω | ω (first i) = true ∧ ω (second i) = true}ᶜ)).toReal := by
  let p := fun _ : Fin 4 => PMF.uniformOfFintype Bool
  let vbl (i : Fin 2) : Finset (Fin 4) := {first i, second i}
  have hpair (i : Fin 2) : ((PMF.pi p).toOuterMeasure
      {ω | ω (first i) = true ∧ ω (second i) = true}).toReal = 1 / 4 := by
    have hne : first i ≠ second i := by fin_cases i <;> decide
    have h := PMF.toOuterMeasure_pi_inter_eq_mul p (S := {first i}) (T := {second i})
      (Set.disjoint_singleton.2 hne) (E := {ω | ω (first i) = true})
      (F := {ω | ω (second i) = true})
      (fun ω ω' h => by simp only [Set.mem_ofPred_eq, h _ rfl])
      (fun ω ω' h => by simp only [Set.mem_ofPred_eq, h _ rfl])
    rw [show {ω : Fin 4 → Bool | ω (first i) = true ∧ ω (second i) = true} =
      {ω | ω (first i) = true} ∩ {ω | ω (second i) = true} from rfl, h, ENNReal.toReal_mul,
      toReal_pi_eq_true, toReal_pi_eq_true]
    norm_num
  refine PMF.pi_iInter_compl_pos p _ vbl (fun i ω ω' h => ?_) (d := 0) (fun i => ?_)
    (q := 1 / 4) (fun i => (hpair i).le) ?_
  · simp only [Set.mem_ofPred_eq, h _ (by simp [vbl] : first i ∈ (vbl i : Set (Fin 4))),
      h _ (by simp [vbl] : second i ∈ (vbl i : Set (Fin 4)))]
  · fin_cases i <;> decide
  · have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith

/-! ### Axiom guards -/

/--
info: 'Cslib.Probability.PMF.pi_sum_ge_one_add_mul' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.PMF.pi_sum_ge_one_add_mul

/--
info: 'Cslib.Probability.PMF.pi_sum_le_one_sub_mul' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.PMF.pi_sum_le_one_sub_mul

/--
info: 'Cslib.Probability.PMF.pi_sum_abs_sub_mean_ge_mul' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.PMF.pi_sum_abs_sub_mean_ge_mul

/--
info: 'Cslib.Probability.PMF.pi_sum_ge_one_add_mul_le_exp_log' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.PMF.pi_sum_ge_one_add_mul_le_exp_log

/--
info: 'Cslib.Probability.PMF.pi_sum_ge_one_add_mul_of_le_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.PMF.pi_sum_ge_one_add_mul_of_le_one

/--
info: 'Cslib.Probability.isKWiseIndependentHash_two_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.isKWiseIndependentHash_two_iff

/--
info: 'Cslib.Probability.IsKWiseIndependentHash.expect_sum_pow_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.IsKWiseIndependentHash.expect_sum_pow_le

/--
info: 'Cslib.Probability.pow_le_measureReal_iInter_compl' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.pow_le_measureReal_iInter_compl

/--
info: 'Cslib.Probability.isKWiseIndependentHash_polynomialHash' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.isKWiseIndependentHash_polynomialHash

/--
info: 'Cslib.Probability.IsKWiseIndependentHash.dens_filter_le_abs_sum_sub_expect' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.IsKWiseIndependentHash.dens_filter_le_abs_sum_sub_expect

/--
info: 'Cslib.Probability.prod_one_sub_le_measureReal_iInter_compl' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.prod_one_sub_le_measureReal_iInter_compl

/--
info: 'Cslib.Probability.measureReal_iInter_compl_pos' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.measureReal_iInter_compl_pos

/--
info: 'Cslib.Probability.PMF.prod_one_sub_le_pi_iInter_compl' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.PMF.prod_one_sub_le_pi_iInter_compl

/--
info: 'Cslib.Probability.PMF.pi_iInter_compl_pos' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.PMF.pi_iInter_compl_pos

end ComplexityTests.ProbabilityToolkit
