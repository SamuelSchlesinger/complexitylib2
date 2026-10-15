/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib `InformationTheory/Coding/HammingBound.lean`)

public import Complexity.Init
public import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset

/-!
# Hamming balls, the Hamming bound and the Gilbert–Varshamov bound

The words `∀ i, β i` at Hamming distance exactly `r` from a word `x` are obtained by choosing the
`r` positions where they differ and a different letter at each, so there are
`∑_{|S| = r} ∏_{i ∈ S} (|β i| - 1)` of them, whatever `x` is (`card_filter_hammingDist_eq`); over an
alphabet of `q` letters at each of `n` positions this is `C(n, r) (q - 1) ^ r`
(`card_filter_hammingDist_eq_choose_mul_pow`). Balls of radius `r` around the words of a code whose
distinct words are at distance more than `2 r` are disjoint, so the code has at most `q ^ n / V`
words, where `V` is the size of a ball: the **Hamming bound**
(`card_mul_card_filter_hammingDist_le_le_prod`, `card_mul_sum_choose_le_of_two_mul_lt_hammingDist`)
[Hamming1950], [MacWilliams and Sloane, Chapter 1, Theorem 6][MacWilliamsSloane1977]. Conversely,
the balls of radius `d - 1` around a largest code of minimum distance `d` cover every word, so some
code of minimum distance `d` has at least `q ^ n / V` words, where `V` is the size of a ball of
radius `d - 1`: the **Gilbert–Varshamov bound**
(`exists_prod_le_card_mul_card_filter_hammingDist_lt`,
`exists_pow_le_card_mul_sum_choose_of_le_hammingDist`) [Gilbert1952], by Gilbert's greedy argument;
Varshamov proved the same bound for linear codes [Varshamov1957].

## Main results

* `card_filter_hammingDist_eq`: the size of a Hamming sphere.
* `card_filter_hammingDist_le_eq_sum`: the size of a Hamming ball, as a sum of sphere sizes.
* `card_mul_card_filter_hammingDist_le_le_prod`: the Hamming bound.
* `card_mul_sum_choose_le_of_two_mul_lt_hammingDist`: the Hamming bound over a `q`-letter
  alphabet.
* `exists_prod_le_card_mul_card_filter_hammingDist_lt`: the Gilbert–Varshamov bound.
* `exists_pow_le_card_mul_sum_choose_of_le_hammingDist`: the Gilbert–Varshamov bound over a
  `q`-letter alphabet.

## References

* [R. W. Hamming, *Error detecting and error correcting codes*][Hamming1950]
* [E. N. Gilbert, *A comparison of signalling alphabets*][Gilbert1952]
* [R. R. Varshamov, *Estimate of the number of signals in error correcting codes*][Varshamov1957]
* [F. J. MacWilliams, N. J. A. Sloane, *The Theory of Error-Correcting Codes*]
  [MacWilliamsSloane1977]
-/

@[expose] public section

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*} [∀ i, Fintype (β i)]
  [∀ i, DecidableEq (β i)]

/-- The words differing from `x` exactly at the positions `S`: a different letter at each position
of `S`. -/
private theorem card_filter_filter_ne_eq (x : ∀ i, β i) (S : Finset ι) :
    #{y : ∀ i, β i | ({i | x i ≠ y i} : Finset ι) = S} = ∏ i ∈ S, (Fintype.card (β i) - 1) := by
  have h : #{y : ∀ i, β i | ({i | x i ≠ y i} : Finset ι) = S} =
      Fintype.card (∀ i, {b : β i // (i ∈ S ↔ x i ≠ b)}) := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr ((Equiv.subtypeEquivRight fun y => ?_).trans
      Equiv.subtypePiEquivPi)
    simp only [mem_filter, mem_univ, true_and, Finset.ext_iff]
    exact forall_congr' fun i => Iff.comm
  rw [h, Fintype.card_pi]
  have hi (i : ι) : Fintype.card {b : β i // (i ∈ S ↔ x i ≠ b)} =
      if i ∈ S then Fintype.card (β i) - 1 else 1 := by
    by_cases hiS : i ∈ S
    · simp only [hiS, true_iff, ↓reduceIte]
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq']
    · simp only [hiS, false_iff, not_not, ↓reduceIte]
      rw [Fintype.card_subtype_eq']
  simp only [hi]
  rw [prod_ite, prod_const_one, mul_one, filter_mem_eq_inter, univ_inter]

/-- **The size of a Hamming sphere**: the words at distance `r` from `x`. It does not depend on
`x`. -/
theorem card_filter_hammingDist_eq (x : ∀ i, β i) (r : ℕ) :
    #{y : ∀ i, β i | hammingDist x y = r} =
      ∑ S ∈ powersetCard r (univ : Finset ι), ∏ i ∈ S, (Fintype.card (β i) - 1) := by
  rw [← sum_congr rfl fun S _ => card_filter_filter_ne_eq x S, ← card_biUnion]
  · congr 1
    ext y
    simp [hammingDist, mem_powersetCard]
  · intro S _ T _ hST
    exact disjoint_left.2 fun y hS hT => hST ((mem_filter.1 hS).2.symm.trans (mem_filter.1 hT).2)

/-- Over an alphabet of `q` letters at each of `n` positions, a Hamming sphere of radius `r` has
`C(n, r) (q - 1) ^ r` words. -/
theorem card_filter_hammingDist_eq_choose_mul_pow {q : ℕ} (hq : ∀ i, Fintype.card (β i) = q)
    (x : ∀ i, β i) (r : ℕ) :
    #{y : ∀ i, β i | hammingDist x y = r} = (Fintype.card ι).choose r * (q - 1) ^ r := by
  rw [card_filter_hammingDist_eq, sum_congr rfl fun S hS => by
    rw [prod_congr rfl fun i _ => by rw [hq i], prod_const, (mem_powersetCard.1 hS).2],
    sum_const, card_powersetCard, card_univ, smul_eq_mul]

/-- **The size of a Hamming ball** is the sum of the sizes of the spheres. -/
theorem card_filter_hammingDist_le_eq_sum (x : ∀ i, β i) (r : ℕ) :
    #{y : ∀ i, β i | hammingDist x y ≤ r} =
      ∑ j ∈ range (r + 1), #{y : ∀ i, β i | hammingDist x y = j} := by
  rw [← card_biUnion]
  · congr 1
    ext y
    simp
  · intro i _ j _ hij
    exact disjoint_left.2 fun y hi hj => hij ((mem_filter.1 hi).2.symm.trans (mem_filter.1 hj).2)

/-- **The Hamming bound**: a code whose distinct words are at distance more than `2 r` has at most
`∏ i, |β i|` words in all of its balls of radius `r` together. -/
theorem card_mul_card_filter_hammingDist_le_le_prod {C : Finset (∀ i, β i)} {r : ℕ}
    (hC : (C : Set (∀ i, β i)).Pairwise fun x y => 2 * r < hammingDist x y) (x₀ : ∀ i, β i) :
    #C * #{y : ∀ i, β i | hammingDist x₀ y ≤ r} ≤ ∏ i, Fintype.card (β i) := by
  -- the balls around the codewords are disjoint, and have the same size
  have hdisj : (C : Set (∀ i, β i)).PairwiseDisjoint
      fun x => ({y : ∀ i, β i | hammingDist x y ≤ r} : Finset (∀ i, β i)) := by
    intro x hx y hy hxy
    refine disjoint_left.2 fun z hzx hzy => ?_
    have h₁ := (mem_filter.1 hzx).2
    have h₂ := (mem_filter.1 hzy).2
    have := hammingDist_triangle x z y
    rw [hammingDist_comm z y] at this
    have := hC hx hy hxy
    omega
  have hsize (x : ∀ i, β i) : #{y : ∀ i, β i | hammingDist x y ≤ r} =
      #{y : ∀ i, β i | hammingDist x₀ y ≤ r} := by
    simp only [card_filter_hammingDist_le_eq_sum, card_filter_hammingDist_eq]
  calc #C * #{y : ∀ i, β i | hammingDist x₀ y ≤ r}
      = ∑ x ∈ C, #{y : ∀ i, β i | hammingDist x y ≤ r} := by
        rw [sum_congr rfl fun x _ => hsize x, sum_const, smul_eq_mul]
    _ = #(C.biUnion fun x => {y : ∀ i, β i | hammingDist x y ≤ r}) := (card_biUnion hdisj).symm
    _ ≤ #(univ : Finset (∀ i, β i)) := card_le_univ _
    _ = ∏ i, Fintype.card (β i) := by rw [card_univ, Fintype.card_pi]

omit [DecidableEq ι] in
/-- **The Hamming bound** over a `q`-letter alphabet at each of `n` positions: a code whose
distinct words are at distance more than `2 r` has at most `q ^ n / V` words, where
`V = ∑_{j ≤ r} C(n, j) (q - 1) ^ j` is the size of a ball of radius `r`. -/
theorem card_mul_sum_choose_le_of_two_mul_lt_hammingDist {q : ℕ}
    (hq : ∀ i, Fintype.card (β i) = q) {C : Finset (∀ i, β i)} {r : ℕ}
    (hC : (C : Set (∀ i, β i)).Pairwise fun x y => 2 * r < hammingDist x y) :
    #C * ∑ j ∈ range (r + 1), (Fintype.card ι).choose j * (q - 1) ^ j ≤ q ^ Fintype.card ι := by
  classical
  rcases C.eq_empty_or_nonempty with rfl | ⟨x₀, -⟩
  · simp
  have h := card_mul_card_filter_hammingDist_le_le_prod hC x₀
  rwa [card_filter_hammingDist_le_eq_sum, sum_congr rfl fun j _ =>
    card_filter_hammingDist_eq_choose_mul_pow hq x₀ j, prod_congr rfl fun i _ => hq i,
    prod_const, card_univ] at h

/-- The balls of radius less than `d ≥ 1` all have the size of the ball of radius `d - 1`. -/
private theorem card_filter_hammingDist_lt_eq_sum {d : ℕ} (hd : 0 < d) (x : ∀ i, β i) :
    #{y : ∀ i, β i | hammingDist x y < d} =
      ∑ j ∈ range d, #{y : ∀ i, β i | hammingDist x y = j} := by
  simp only [Nat.lt_iff_le_pred hd, card_filter_hammingDist_le_eq_sum, Nat.sub_add_cancel hd]

/-- **The Gilbert–Varshamov bound** [Gilbert1952]: for `d ≥ 1` there is a code whose distinct
words are at distance at least `d` and which has at least `∏ i, |β i| / V` words, where `V` is the
size of a ball of radius `d - 1`. A largest such code works: its balls of radius `d - 1` cover every
word, since a word at distance at least `d` from every codeword could be added to it. -/
theorem exists_prod_le_card_mul_card_filter_hammingDist_lt {d : ℕ} (hd : 0 < d) (x₀ : ∀ i, β i) :
    ∃ C : Finset (∀ i, β i), (C : Set (∀ i, β i)).Pairwise (fun x y => d ≤ hammingDist x y) ∧
      ∏ i, Fintype.card (β i) ≤ #C * #{y : ∀ i, β i | hammingDist x₀ y < d} := by
  classical
  -- a largest code of minimum distance `d`
  obtain ⟨C, hC, hmax⟩ := (univ.filter fun C : Finset (∀ i, β i) =>
      (C : Set (∀ i, β i)).Pairwise fun x y => d ≤ hammingDist x y).exists_max_image card
    ⟨∅, by simp⟩
  have hCd := (mem_filter.1 hC).2
  refine ⟨C, hCd, ?_⟩
  -- its balls of radius `d - 1` cover every word
  have hcover : (univ : Finset (∀ i, β i)) ⊆ C.biUnion fun x => {y | hammingDist x y < d} := by
    intro y _
    by_contra hy
    simp only [mem_biUnion, mem_filter, mem_univ, true_and, not_exists, not_and, not_lt] at hy
    have hyC : y ∉ C := fun h => by simpa [hd.ne'] using hy y h
    have hins : ((insert y C : Finset (∀ i, β i)) : Set (∀ i, β i)).Pairwise
        fun x y => d ≤ hammingDist x y := by
      rw [coe_insert]
      exact hCd.insert fun x hx _ => ⟨by rw [hammingDist_comm]; exact hy x hx, hy x hx⟩
    have := hmax _ (mem_filter.2 ⟨mem_univ _, hins⟩)
    rw [card_insert_of_notMem hyC] at this
    omega
  have hsize (x : ∀ i, β i) : #{y : ∀ i, β i | hammingDist x y < d} =
      #{y : ∀ i, β i | hammingDist x₀ y < d} := by
    simp only [card_filter_hammingDist_lt_eq_sum hd, card_filter_hammingDist_eq]
  calc ∏ i, Fintype.card (β i)
      = #(univ : Finset (∀ i, β i)) := by rw [card_univ, Fintype.card_pi]
    _ ≤ #(C.biUnion fun x => {y : ∀ i, β i | hammingDist x y < d}) := card_le_card hcover
    _ ≤ ∑ x ∈ C, #{y : ∀ i, β i | hammingDist x y < d} := card_biUnion_le
    _ = #C * #{y : ∀ i, β i | hammingDist x₀ y < d} := by
        rw [sum_congr rfl fun x _ => hsize x, sum_const, smul_eq_mul]

omit [DecidableEq ι] in
/-- **The Gilbert–Varshamov bound** [Gilbert1952] over a `q`-letter alphabet at each of `n`
positions: for `d ≥ 1` there is a code whose distinct words are at distance at least `d` and which
has at least `q ^ n / V` words, where `V = ∑_{j < d} C(n, j) (q - 1) ^ j` is the size of a ball of
radius `d - 1`. -/
theorem exists_pow_le_card_mul_sum_choose_of_le_hammingDist {q : ℕ}
    (hq : ∀ i, Fintype.card (β i) = q) {d : ℕ} (hd : 0 < d) :
    ∃ C : Finset (∀ i, β i), (C : Set (∀ i, β i)).Pairwise (fun x y => d ≤ hammingDist x y) ∧
      q ^ Fintype.card ι ≤ #C * ∑ j ∈ range d, (Fintype.card ι).choose j * (q - 1) ^ j := by
  classical
  have hprod : ∏ i, Fintype.card (β i) = q ^ Fintype.card ι := by
    rw [prod_congr rfl fun i _ => hq i, prod_const, card_univ]
  rcases isEmpty_or_nonempty (∀ i, β i) with hempty | hne
  · refine ⟨∅, by simp, ?_⟩
    rw [← hprod, ← Fintype.card_pi, Fintype.card_eq_zero]
    exact Nat.zero_le _
  obtain ⟨x₀⟩ := hne
  obtain ⟨C, hCd, hC⟩ := exists_prod_le_card_mul_card_filter_hammingDist_lt hd x₀
  refine ⟨C, hCd, ?_⟩
  rwa [card_filter_hammingDist_lt_eq_sum hd, sum_congr rfl fun j _ =>
    card_filter_hammingDist_eq_choose_mul_pow hq x₀ j, hprod] at hC
