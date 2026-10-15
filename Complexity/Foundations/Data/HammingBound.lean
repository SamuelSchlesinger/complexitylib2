/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib `InformationTheory/Coding/HammingBound.lean`)

public import Cslib.Init
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Hamming balls and the Hamming bound

Over an alphabet `α` with `q` letters, the words `ι → α` at Hamming distance exactly `r` from a
word `x` are obtained by choosing the `r` positions where they differ and a different letter at
each, so there are `C(n, r) (q - 1) ^ r` of them for `n` positions
(`card_filter_hammingDist_eq`). Balls of radius `r` around the words of a code whose distinct words
are at distance more than `2 r` are disjoint, so the code has at most `q ^ n / V` words, where
`V = ∑_{i ≤ r} C(n, i) (q - 1) ^ i` is the size of a ball: the **Hamming bound**
(`card_mul_sum_choose_le_of_two_mul_lt_hammingDist`) [Hamming1950],
[MacWilliams and Sloane, Chapter 1][MacWilliamsSloane1977].

## Main results

* `card_filter_hammingDist_eq`: the size of a Hamming sphere.
* `card_filter_hammingDist_le`: the size of a Hamming ball.
* `card_mul_sum_choose_le_of_two_mul_lt_hammingDist`: the Hamming bound.

## References

* [R. W. Hamming, *Error detecting and error correcting codes*][Hamming1950]
* [F. J. MacWilliams, N. J. A. Sloane, *The Theory of Error-Correcting Codes*]
  [MacWilliamsSloane1977]
-/

@[expose] public section

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- The words differing from `x` exactly at the positions `S`: a different letter at each position
of `S`. -/
theorem card_filter_filter_ne_eq (x : ι → α) (S : Finset ι) :
    #{y : ι → α | ({i | x i ≠ y i} : Finset ι) = S} = (Fintype.card α - 1) ^ #S := by
  classical
  have h : #{y : ι → α | ({i | x i ≠ y i} : Finset ι) = S} =
      Fintype.card (∀ i, {b : α // (i ∈ S ↔ x i ≠ b)}) := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr ((Equiv.subtypeEquivRight fun y => ?_).trans
      Equiv.subtypePiEquivPi)
    simp only [mem_filter, mem_univ, true_and, Finset.ext_iff]
    exact forall_congr' fun i => Iff.comm
  rw [h, Fintype.card_pi]
  have hi (i : ι) : Fintype.card {b : α // (i ∈ S ↔ x i ≠ b)} =
      if i ∈ S then Fintype.card α - 1 else 1 := by
    by_cases hiS : i ∈ S
    · simp only [hiS, true_iff, ↓reduceIte]
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq']
    · simp only [hiS, false_iff, not_not, ↓reduceIte]
      rw [Fintype.card_subtype_eq']
  simp only [hi]
  rw [prod_ite, prod_const, prod_const_one, mul_one, filter_mem_eq_inter, univ_inter]

/-- **The size of a Hamming sphere**: the words at distance `r` from `x`. -/
theorem card_filter_hammingDist_eq (x : ι → α) (r : ℕ) :
    #{y : ι → α | hammingDist x y = r} = (Fintype.card ι).choose r * (Fintype.card α - 1) ^ r := by
  have : #{y : ι → α | hammingDist x y = r} =
      ∑ S ∈ powersetCard r (univ : Finset ι), #{y : ι → α | ({i | x i ≠ y i} : Finset ι) = S} := by
    rw [← card_biUnion]
    · congr 1
      ext y
      simp [hammingDist, mem_powersetCard]
    · intro S _ T _ hST
      exact disjoint_left.2 fun y hS hT => hST ((mem_filter.1 hS).2.symm.trans (mem_filter.1 hT).2)
  rw [this, sum_congr rfl fun S hS => by rw [card_filter_filter_ne_eq, (mem_powersetCard.1 hS).2],
    sum_const, card_powersetCard, card_univ, smul_eq_mul]

/-- **The size of a Hamming ball**: the words at distance at most `r` from `x`. -/
theorem card_filter_hammingDist_le (x : ι → α) (r : ℕ) :
    #{y : ι → α | hammingDist x y ≤ r} =
      ∑ i ∈ range (r + 1), (Fintype.card ι).choose i * (Fintype.card α - 1) ^ i := by
  rw [← sum_congr rfl fun i _ => card_filter_hammingDist_eq x i, ← card_biUnion]
  · congr 1
    ext y
    simp
  · intro i _ j _ hij
    exact disjoint_left.2 fun y hi hj => hij ((mem_filter.1 hi).2.symm.trans (mem_filter.1 hj).2)

omit [DecidableEq ι] in
/-- **The Hamming bound**: a code whose distinct words are at distance more than `2 r` has at most
`q ^ n / V` words, where `V` is the size of a ball of radius `r`. -/
theorem card_mul_sum_choose_le_of_two_mul_lt_hammingDist {C : Finset (ι → α)} {r : ℕ}
    (hC : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 2 * r < hammingDist x y) :
    #C * ∑ i ∈ range (r + 1), (Fintype.card ι).choose i * (Fintype.card α - 1) ^ i ≤
      Fintype.card α ^ Fintype.card ι := by
  classical
  -- the balls around the codewords are disjoint
  have hdisj : (C : Set (ι → α)).PairwiseDisjoint
      fun x => ({y : ι → α | hammingDist x y ≤ r} : Finset (ι → α)) := by
    intro x hx y hy hxy
    refine disjoint_left.2 fun z hzx hzy => ?_
    have h₁ := (mem_filter.1 hzx).2
    have h₂ := (mem_filter.1 hzy).2
    have := hammingDist_triangle x z y
    rw [hammingDist_comm z y] at this
    have := hC x hx y hy hxy
    omega
  calc #C * ∑ i ∈ range (r + 1), (Fintype.card ι).choose i * (Fintype.card α - 1) ^ i
      = ∑ x ∈ C, #{y : ι → α | hammingDist x y ≤ r} := by
        rw [sum_congr rfl fun x _ => card_filter_hammingDist_le x r, sum_const, smul_eq_mul]
    _ = #(C.biUnion fun x => {y : ι → α | hammingDist x y ≤ r}) := (card_biUnion hdisj).symm
    _ ≤ #(univ : Finset (ι → α)) := card_le_univ _
    _ = Fintype.card α ^ Fintype.card ι := by simp
