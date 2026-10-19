/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Communication.Disjointness

/-!
# Randomized disjointness

Clients for majority amplification, the hard distribution for disjointness on three points (the
hypothesis `Fintype.card U = 2 m + 1` holds for `Fin 3` and `m = 1`, and `48 r ≤ m + 1` for
`r = 0`), and a concrete consequence of the `Ω(n)` lower bound: deciding disjointness of
`2 ^ 20`-bit strings with error `1 / 3` takes at least `16` bits, with public or private coins.
-/

namespace ComplexityTests.RandomizedDisjointness

open Cslib Cslib.Communication Cslib.Communication.Disjointness Finset

/-! ### Sequencing protocols and majority votes -/

/-- Alice sends her bit. -/
private def sendBit : Protocol Bool Bool Bool :=
  .alice id (.output false) (.output true)

/-- Bob sends his bit. -/
private def bobBit : Protocol Bool Bool Bool :=
  .bob id (.output false) (.output true)

example : (sendBit.bind fun b => if b then .bob id (.output false) (.output true)
    else .output false).run true true = true := rfl

example : (Protocol.runAll ![sendBit, bobBit, sendBit] (BitString.strictMajorityOn univ)).run
    true false = true := rfl

example : (Protocol.runAll ![sendBit, bobBit, sendBit] (BitString.strictMajorityOn univ)).depth
    ≤ 3 * 1 :=
  Protocol.depth_runAll_le fun i => by fin_cases i <;> rfl

example : BitString.strictMajorityOn univ ![true, false, true, false] = false := rfl

-- Two runs at error `1 / 3` give error `8 / 9`, four runs `(8 / 9) ^ 2`.
example (f : Bool → Bool → Bool) :
    PublicCoin.ecomplexityFun ((8 / 9) ^ 2) f ≤ 2 * (2 : ℕ) * PublicCoin.ecomplexityFun (1 / 3) f :=
  PublicCoin.ecomplexityFun_le_two_mul_mul_one_third 2

/-! ### The hard distribution on three points -/

example : Corrupted (hardDist 1 (Fintype.card_fin 3))
    (fun x y => decide (Disjoint x y)) true (1 / 18) ((27 / 32) ^ 0 / 2) :=
  corrupted_hardDist _ (by norm_num)

example : ((hardDist 1 (Fintype.card_fin 3)).toOuterMeasure
    {q | decide (Disjoint q.1 q.2) = true}).toReal = 1 / 2 :=
  hardDist_toOuterMeasure_disjoint _

-- The partitions of three points into a point and two singletons.
example : #(parts (Fin 3) 1) = 6 := by
  rw [card_parts (Fintype.card_fin 3), card_powersetCard, card_univ,
    Fintype.card_fin]
  rfl

example : ∑ q : Finset (Fin 3) × Finset (Fin 3), weight 1 q = 1 :=
  sum_weight (Fintype.card_fin 3)

-- A nontrivial instance of the corruption lemma: on `95` points (`m = 47`) the error term is
-- `(27 / 32) / 2` with `r = 1`.
example : Corrupted (hardDist 47 (Fintype.card_fin 95))
    (fun x y => decide (Disjoint x y)) true (1 / 18) ((27 / 32) ^ 1 / 2) :=
  corrupted_hardDist _ (by norm_num)

/-! ### Independent draws -/

-- Three independent fair coins all come up `true` with probability `1 / 8`.
example : Probability.PMF.iid (Probability.PMF.uniformOfFintype Bool) 3 (fun _ => true) = 8⁻¹ := by
  rw [Probability.PMF.iid_apply]
  simp only [Probability.PMF.uniformOfFintype_apply, Fintype.card_bool, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.inv_pow]
  norm_num

example (μ : PMF ℕ) (v : Fin 2 → ℕ) (hv : v ∈ (Probability.PMF.iid μ 2).support) :
    v 1 ∈ μ.support :=
  (Probability.PMF.mem_support_iid_iff μ v).mp hv 1

/-! ### Lower bounds -/

example : (16 : ℕ∞) ≤ PublicCoin.ecomplexityFun (1 / 3)
    (disjointness : BitString (2 ^ 20) → BitString (2 ^ 20) → Bool) := by
  have h := PublicCoin.le_mul_ecomplexityFun_disjointness_add (2 ^ 20)
  cases hc : PublicCoin.ecomplexityFun (1 / 3)
      (disjointness : BitString (2 ^ 20) → BitString (2 ^ 20) → Bool) using ENat.recTopCoe with
  | top => exact le_top
  | coe c =>
    rw [hc] at h
    have : 2 ^ 20 ≤ 2 ^ 16 * c + 2 ^ 12 := by exact_mod_cast h
    exact_mod_cast (show 16 ≤ c by omega)

example : (16 : ℕ∞) ≤ PrivateCoin.ecomplexityFun (1 / 3)
    (disjointness : BitString (2 ^ 20) → BitString (2 ^ 20) → Bool) := by
  have h := PrivateCoin.le_mul_ecomplexityFun_disjointness_add (2 ^ 20)
  cases hc : PrivateCoin.ecomplexityFun (1 / 3)
      (disjointness : BitString (2 ^ 20) → BitString (2 ^ 20) → Bool) using ENat.recTopCoe with
  | top => exact le_top
  | coe c =>
    rw [hc] at h
    have : 2 ^ 20 ≤ 2 ^ 16 * c + 2 ^ 12 := by exact_mod_cast h
    exact_mod_cast (show 16 ≤ c by omega)

-- Precomposition: disjointness of subsets of `Fin 3` is no harder than of `3`-bit strings.
example : PublicCoin.ecomplexityFun (1 / 3)
    (fun x y : Finset (Fin 3) => disjointness (fun i => decide (i ∈ x)) fun i => decide (i ∈ y)) ≤
      PublicCoin.ecomplexityFun (1 / 3) (disjointness : BitString 3 → BitString 3 → Bool) :=
  PublicCoin.ecomplexityFun_comap_le _ _ _

/-! ### Axioms -/

/--
info: 'Cslib.Communication.Disjointness.corrupted_hardDist' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Communication.Disjointness.corrupted_hardDist

/--
info: 'Finset.four_mul_sum_card_filter_notMem_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Finset.four_mul_sum_card_filter_notMem_le

/--
info: 'Cslib.Communication.PublicCoin.div_le_mul_ecomplexityFun_disjoint_add' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Communication.PublicCoin.div_le_mul_ecomplexityFun_disjoint_add

/--
info: 'Cslib.Communication.PublicCoin.le_mul_ecomplexityFun_disjointness_add_of_le' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Communication.PublicCoin.le_mul_ecomplexityFun_disjointness_add_of_le

/--
info: 'Cslib.Communication.PublicCoin.le_mul_ecomplexityFun_disjointness_add' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Communication.PublicCoin.le_mul_ecomplexityFun_disjointness_add

/--
info: 'Cslib.Communication.PrivateCoin.le_mul_ecomplexityFun_disjointness_add' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Communication.PrivateCoin.le_mul_ecomplexityFun_disjointness_add

/--
info: 'Cslib.Communication.PublicCoin.ecomplexity_le_two_mul_mul' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Communication.PublicCoin.ecomplexity_le_two_mul_mul

/--
info: 'Cslib.Probability.PMF.iid_card_ge_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.PMF.iid_card_ge_le

end ComplexityTests.RandomizedDisjointness
