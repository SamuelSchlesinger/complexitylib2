/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.Code.BerlekampWelch
import Complexity.Foundations.Data.Code.Hadamard
import Complexity.Foundations.Data.Code.HammingBound
import Complexity.Foundations.Data.Code.ReedMuller
import Complexity.Foundations.Data.Code.Singleton
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Tests: algebraic codes

The minimum distance of the binary repetition code and of codes with at most one word; the
Singleton and Hamming bounds on the repetition code, which meets both; the Gilbert–Varshamov
bound; the minimum distance of a Hadamard code; the Singleton bound on a Reed–Solomon code, which
meets it; the distance and
dimension of a Reed–Solomon code over `ZMod 5`, the zero code of dimension zero, and unique
decoding below half its distance; the distance of a Reed–Muller code over `ZMod 3`; a complete
Berlekamp–Welch decoding over `ZMod 7` with two errors, the largest number it corrects at that
length and dimension; and the axioms of the headline theorems.
-/

namespace ComplexityTests.Code

open Cslib Cslib.Code Polynomial

instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-! ### Minimum distance -/

/-- The binary repetition code of length three. -/
private def repetition : Finset (Fin 3 → Bool) := {fun _ => false, fun _ => true}

private theorem minDist_repetition : minDist (repetition : Set (Fin 3 → Bool)) = 3 := by
  refine le_antisymm ((minDist_le_hammingDist (x := fun _ => false) (y := fun _ => true)
    (by simp [repetition]) (by simp [repetition]) (by decide)).trans_eq ?_) ?_
  · rw [show hammingDist (fun _ : Fin 3 => false) (fun _ => true) = 3 by decide]
    rfl
  · rw [le_minDist_iff]
    rintro x hx y hy hxy
    simp only [repetition, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    all_goals first | exact absurd rfl hxy | (rw [show hammingDist _ _ = 3 by decide]; rfl)

example : minDist (∅ : Set (Fin 3 → Bool)) = ⊤ := minDist_empty

example : minDist ({fun _ => true} : Set (Fin 3 → Bool)) = ⊤ := minDist_singleton _

/-- The Singleton bound for the repetition code is tight: two words, `2 ^ (3 - 3 + 1)`. -/
example : repetition.card ≤ 2 ^ (3 - 3 + 1) := by
  simpa using card_le_pow_of_le_minDist (d := 3) minDist_repetition.ge

/-- The Hamming bound for the repetition code is tight: two balls of radius one, of four words
each, fill the eight words of length three. -/
example : repetition.card * ∑ j ∈ Finset.range 2, (3).choose j * (2 - 1) ^ j ≤ 2 ^ 3 := by
  simpa using card_mul_sum_choose_le_of_two_mul_lt_minDist (β := fun _ : Fin 3 => Bool) (q := 2)
    (fun _ => rfl) (r := 1) (by rw [minDist_repetition]; decide)

/-- The Gilbert–Varshamov bound: some binary code of length three and minimum distance at least
two has at least `8 / 4` words. -/
example : ∃ C : Finset (Fin 3 → Bool), (2 : ℕ∞) ≤ minDist (C : Set (Fin 3 → Bool)) ∧
    2 ^ 3 ≤ C.card * ∑ j ∈ Finset.range 2, (3).choose j * (2 - 1) ^ j := by
  simpa using exists_le_minDist_and_pow_le_card_mul_sum_choose (β := fun _ : Fin 3 => Bool)
    (q := 2) (fun _ => rfl) (d := 2) (by norm_num)

/-- The Hadamard code of messages of three bits has minimum distance four. -/
example : minDist (Set.range (BitString.hadamardCode (ι := Fin 3))) = 4 := by
  simpa using BitString.minDist_range_hadamardCode (ι := Fin 3)

/-! ### Reed–Solomon codes over `ZMod 5` -/

/-- The five points of `ZMod 5`. -/
private def points5 : Fin 5 → ZMod 5 := fun i => (i : ℕ)

private theorem points5_injective : Function.Injective points5 := by decide

private theorem minDist_rs : minDist (reedSolomon points5 2 : Set (Fin 5 → ZMod 5)) = 4 :=
  minDist_reedSolomon points5_injective (by norm_num) (by simp)

private theorem finrank_rs : Module.finrank (ZMod 5) (reedSolomon points5 2) = 2 :=
  finrank_reedSolomon points5_injective (by simp)

/-- The Reed–Solomon code is not the zero code: it contains the constant word `1`. -/
private theorem rs_ne_bot : reedSolomon points5 2 ≠ ⊥ := by
  intro h
  have h1 : (fun i => (1 : (ZMod 5)[X]).eval (points5 i)) ∈ reedSolomon points5 2 :=
    eval_mem_reedSolomon points5 (by rw [degree_one]; exact_mod_cast (by norm_num : 0 < 2))
  rw [h, Submodule.mem_bot] at h1
  exact absurd (congrFun h1 0) (by simp)

/-- **Reed–Solomon codes are maximum distance separable**: the Singleton bound holds with
equality. -/
example : Module.finrank (ZMod 5) (reedSolomon points5 2) + 4 = Fintype.card (Fin 5) + 1 := by
  rw [finrank_rs]
  simp

example : Module.finrank (ZMod 5) (reedSolomon points5 2) + 4 ≤ Fintype.card (Fin 5) + 1 :=
  finrank_add_le_card_add_one rs_ne_bot minDist_rs.ge

/-- The Reed–Solomon code of dimension zero is the zero code, whose minimum distance is `⊤`. -/
example : minDist (reedSolomon points5 0 : Set (Fin 5 → ZMod 5)) = ⊤ := by
  refine minDist_eq_top_iff.2 fun x hx y hy => ?_
  obtain ⟨p, hp, rfl⟩ := mem_reedSolomon.1 hx
  obtain ⟨q, hq, rfl⟩ := mem_reedSolomon.1 hy
  rw [Nat.cast_zero, Nat.WithBot.lt_zero_iff, degree_eq_bot] at hp hq
  rw [hp, hq]

/-- Unique decoding: a word within distance one of two codewords determines them, since
`2 * 1 < 4`. -/
example {x y w : Fin 5 → ZMod 5} (hx : x ∈ reedSolomon points5 2) (hy : y ∈ reedSolomon points5 2)
    (hxw : hammingDist x w ≤ 1) (hyw : hammingDist y w ≤ 1) : x = y :=
  eq_of_hammingDist_le_of_two_mul_lt_minDist (by rw [minDist_rs]; decide) hx hy hxw hyw

/-! ### Reed–Muller codes over `ZMod 3` -/

/-- The Reed–Muller code of degree one in two variables over `ZMod 3` has minimum distance
`(3 - 1) * 3 = 6`. -/
example : minDist (reedMuller (ZMod 3) 2 1 : Set ((Fin 2 → ZMod 3) → ZMod 3)) = 6 := by
  have := minDist_reedMuller (F := ZMod 3) (m := 1) (d := 1) (by simp [ZMod.card])
  simpa [ZMod.card] using this

/-- Distinct codewords of the Reed–Muller code of degree two in three variables over `ZMod 3`
differ on at least `(3 - 2) * 27 / 3 = 9` points. -/
example {f g : (Fin 3 → ZMod 3) → ZMod 3} (hf : f ∈ reedMuller (ZMod 3) 3 2)
    (hg : g ∈ reedMuller (ZMod 3) 3 2) (hfg : f ≠ g) : 9 ≤ hammingDist f g := by
  have := card_sub_mul_pow_le_mul_hammingDist_of_mem_reedMuller hf hg hfg
  simp only [ZMod.card] at this
  omega

/-! ### Berlekamp–Welch decoding over `ZMod 7` -/

/-- The seven points of `ZMod 7`. -/
private def points7 : Fin 7 → ZMod 7 := fun i => (i : ℕ)

private theorem points7_injective : Function.Injective points7 := by decide

/-- The values `1, 2, 5, 3, 3, 5, 2` of `X ^ 2 + 1` at the points, with errors at the points `2`
and `6`. -/
private def received : Fin 7 → ZMod 7 := ![1, 2, 0, 3, 3, 5, 4]

private theorem hammingDist_received :
    hammingDist (fun i => (X ^ 2 + 1 : (ZMod 7)[X]).eval (points7 i)) received ≤ 2 := by
  have : (fun i => (X ^ 2 + 1 : (ZMod 7)[X]).eval (points7 i)) = fun i => points7 i ^ 2 + 1 := by
    funext i
    simp
  rw [this]
  decide

private theorem degree_lt : (X ^ 2 + 1 : (ZMod 7)[X]).degree < (3 : ℕ) := by
  compute_degree!

/-- The key equations have a solution for the received word. -/
example : ∃ E Q, BerlekampWelch.IsSolution points7 received 2 3 E Q :=
  BerlekampWelch.exists_isSolution degree_lt hammingDist_received

/-- Two errors among seven points are corrected at dimension three, since `2 * 2 + 3 ≤ 7`. -/
example : berlekampWelch points7 2 3 received = some (X ^ 2 + 1) :=
  berlekampWelch_eq_some points7_injective (by simp) degree_lt hammingDist_received

/-! ### Axioms of the headline theorems -/

/--
info: 'Cslib.Code.exists_hammingDist_eq_minDist' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.exists_hammingDist_eq_minDist

/--
info: 'Cslib.Code.eq_of_hammingDist_le_of_two_mul_lt_minDist' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.eq_of_hammingDist_le_of_two_mul_lt_minDist

/--
info: 'Cslib.Code.card_mul_sum_choose_le_of_two_mul_lt_minDist' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.card_mul_sum_choose_le_of_two_mul_lt_minDist

/--
info: 'Cslib.Code.exists_le_minDist_and_pow_le_card_mul_sum_choose' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.exists_le_minDist_and_pow_le_card_mul_sum_choose

/--
info: 'Cslib.BitString.minDist_range_hadamardCode' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.minDist_range_hadamardCode

/--
info: 'Cslib.Code.le_minDist_iff_hammingNorm' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.le_minDist_iff_hammingNorm

/--
info: 'Cslib.Code.card_le_pow_of_le_minDist' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.card_le_pow_of_le_minDist

/--
info: 'Cslib.Code.finrank_add_le_card_add_one' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.finrank_add_le_card_add_one

/--
info: 'Cslib.Code.minDist_reedSolomon' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.minDist_reedSolomon

/--
info: 'Cslib.Code.finrank_reedSolomon' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.finrank_reedSolomon

/--
info: 'Cslib.Code.card_sub_mul_pow_le_mul_hammingDist_of_mem_reedMuller' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.card_sub_mul_pow_le_mul_hammingDist_of_mem_reedMuller

/--
info: 'Cslib.Code.minDist_reedMuller' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.minDist_reedMuller

/--
info: 'Cslib.Code.BerlekampWelch.IsSolution.eq_mul' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.BerlekampWelch.IsSolution.eq_mul

/--
info: 'Cslib.Code.berlekampWelch_eq_some' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.berlekampWelch_eq_some

/--
info: 'Cslib.Code.berlekampWelch_eq_some_of_mem_reedSolomon' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.berlekampWelch_eq_some_of_mem_reedSolomon

end ComplexityTests.Code
