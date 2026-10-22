/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Frontier.Extractor

/-!
# Tests for the sumset-extractor frontier lower-bound bridge

Non-vacuity and axiom checks for `Complexity.Computability.Circuit.Frontier.Extractor`,
`Complexity.Computability.Circuit.Frontier.FanInTwo`, and
`Complexity.Computability.Circuit.Frontier.Layouts.Gaussian.Coefficient`.
-/

namespace ComplexityTests.FrontierExtractor

open Cslib Cslib.Circuits Cslib.Circuits.Frontier Set
open scoped ProbabilityTheory ENNReal

/-! ### Non-vacuity of `SumsetBias`, `SumsetDisperser`, and `IsSumsetExtractor` -/

/-- The single-bit identity set `{z : Fin 1 → Bool | z 0 = true}` has `0` sumset bias at
threshold `2 = 2 ^ 1`. -/
theorem sumsetBias_bit0 : SumsetBias {z : Fin 1 → Bool | z 0 = true} 2 0 := by
  intro A B hA hB
  have hcard : Nat.card (Fin 1 → Bool) = 2 := by simp
  have hA_eq : A = univ :=
    eq_of_subset_of_ncard_le (subset_univ A) (by rw [ncard_univ, hcard]; omega)
  have hB_eq : B = univ :=
    eq_of_subset_of_ncard_le (subset_univ B) (by rw [ncard_univ, hcard]; omega)
  subst hA_eq hB_eq
  have hpair :
      ({p : (Fin 1 → Bool) × (Fin 1 → Bool) |
        p ∈ (univ : Set (Fin 1 → Bool)) ×ˢ (univ : Set (Fin 1 → Bool)) ∧
          p.1 + p.2 ∈ {z : Fin 1 → Bool | z 0 = true}}).ncard = 2 := by
    rw [ncard_univ_prod_univ_add_mem]
    have hS : ({z : Fin 1 → Bool | z 0 = true}).ncard = 1 := by
      have h_eq : {z : Fin 1 → Bool | z 0 = true} = {fun _ => true} := by
        ext z
        simp only [mem_ofPred, mem_singleton_iff, funext_iff, Fin.forall_fin_one]
      rw [h_eq, ncard_singleton]
    rw [hcard, hS]
  rw [hpair, ncard_univ, hcard]
  norm_num

/-- By the flat-source equivalence `isSumsetExtractor_iff_sumsetBias_two_pow`, the single-bit
projection `fun x : Fin 1 → Bool => x 0` is a `(1, 0)`-sumset extractor. -/
theorem isSumsetExtractor_bit0 :
    IsSumsetExtractor (fun x : Fin 1 → Bool => x 0) (1 : ℕ) 0 :=
  (isSumsetExtractor_iff_sumsetBias_two_pow (fun x : Fin 1 → Bool => x 0) 1 0).2
    (by simpa using sumsetBias_bit0)

/-- The induced rectangle bias and rectangle-freeness hold at threshold `2`. -/
example : RectangleBias {z : Fin 1 → Bool | z 0 = true} 2 0 :=
  sumsetBias_bit0.rectangleBias

example : SumsetDisperser {z : Fin 1 → Bool | z 0 = true} 2 :=
  sumsetBias_bit0.sumsetDisperser (by decide) (by norm_num)

example : RectangleFree {z : Fin 1 → Bool | z 0 = true} 2 :=
  sumsetBias_bit0.rectangleFree (by decide) (by norm_num)

/-- Zero-padding splits any bit-string across a coordinate subset and its complement. -/
example (X : Set (Fin 2)) [DecidablePred (· ∈ X)] (z : Fin 2 → Bool) :
    zeroPad X (X.domRestrict z) + zeroPad Xᶜ (Xᶜ.domRestrict z) = z :=
  zeroPad_domRestrict_add_zeroPad_compl_domRestrict X z

/-- Every circuit over `fullSignature 2 Bool` has fan-in at most `2` and inner size at most its
total gate count. -/
example {n m : ℕ} (c : Circuit (fullSignature 2 Bool) n m) :
    c.FanInAtMost 2 ∧ c.innerSize ≤ c.size :=
  ⟨c.fanInAtMost_fullSignature, c.innerSize_le_size⟩

/-! ### Axiom checks -/

/--
info: 'Cslib.Circuits.Frontier.Gaussian.circuitCoefficient_ge_456249' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Gaussian.circuitCoefficient_ge_456249

/--
info: 'Cslib.Circuits.Frontier.eventually_456249_div_100000_sub_mul_lt_innerSize'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_456249_div_100000_sub_mul_lt_innerSize

/--
info: 'Cslib.Circuits.Frontier.averageCaseBound_456249_div_100000' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.averageCaseBound_456249_div_100000

/--
info: 'Cslib.Circuits.Frontier.IsSumsetExtractor.rectangleBias_ceil' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.IsSumsetExtractor.rectangleBias_ceil

/--
info: 'Cslib.Circuits.Frontier.isSumsetExtractor_iff_sumsetBias_two_pow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.isSumsetExtractor_iff_sumsetBias_two_pow

/--
info: 'Cslib.Circuits.Frontier.eventually_agreement_le_of_isSumsetExtractor_fullSignature'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_agreement_le_of_isSumsetExtractor_fullSignature

/--
info: 'Cslib.Circuits.Frontier.eventually_456249_div_100000_sub_mul_lt_size_of_isSumsetExtractor_computes'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  Cslib.Circuits.Frontier.eventually_456249_div_100000_sub_mul_lt_size_of_isSumsetExtractor_computes

/--
info: 'Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_mul_innerSize_of_isSumsetExtractor'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_mul_innerSize_of_isSumsetExtractor

end ComplexityTests.FrontierExtractor
