/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.Amplification
public import Complexity.Computability.Communication.Corruption
public import Complexity.Computability.Communication.Functions
import Complexity.Foundations.Combinatorics.PowersetTail
import Complexity.Probability.PMF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Randomized communication complexity of disjointness

Deciding whether Alice's and Bob's subsets of an `n`-element set are disjoint needs `Ω(n)` bits
even with randomness and bounded error
[Kalyanasundaram and Schnitger][KalyanasundaramSchnitger1992].
We follow Razborov's corruption argument [Razborov1992],
[Kushilevitz and Nisan, Chapter 4][KushilevitzNisan1997], with a variant of his distribution.

The hard distribution `disjointnessDist` lives on pairs of subsets of `2 m + 1` points. It draws a
uniformly random partition `(i, Tx, Ty)` of the points into a point and two sets of `m` points
(`disjointnessParts`) and uniformly random subsets `x ⊆ Tx` and `y ⊆ Ty`, and outputs the disjoint
pair `(x, y)` or, with probability `1 / 2`, the pair `(x ∪ {i}, y ∪ {i})`, which meets in exactly
`i`. Razborov's distribution instead draws sets of size about `n / 4` and gives the disjoint pairs
probability `3 / 4`. Given the partition, the two sets are independent, so on a rectangle `A × B`
the disjoint pairs have mass the average of `a₀ b₀` over the partitions, where `a₀` and `b₀` are
the fractions of the subsets of `Tx` in `A` and of `Ty` in `B`, and the intersecting pairs have
mass the average of `a₁ b₁`, where `a₁` and `b₁` are the fractions of the subsets of `Tx ∪ {i}`
containing `i` in `A` and of `Ty ∪ {i}` in `B`. Call the partition bad for `A` if
`a₁ < a₀ / 3`. Once `Ty` is fixed, `i` is a uniformly random point outside `Ty` and `b₀` is fixed,
and a family of subsets of the complement of `Ty` for which many points are bad is small
(`four_mul_sum_card_filter_le`, proved by Markov's inequality and counting subsets of a cube). So
the partitions bad for `A` or, symmetrically, for `B` carry at most half of the mass of the disjoint
pairs, up to an exponentially small error, while on the others `a₁ b₁ ≥ a₀ b₀ / 9`. This is
*Razborov's corruption lemma* (`corrupted_disjointnessDist`): on every rectangle the intersecting
pairs carry at least `1 / 18` of the mass of the disjoint pairs, up to `(27 / 32) ^ r / 2` when
`48 r ≤ m + 1`.

By the corruption bound (`Corrupted.mul_sub_le_of_ecomplexityFun_le`), public-coin protocols with
error `1 / 64` send at least `((m + 1) / 48 - 29) / 5` bits
(`PublicCoin.div_le_ecomplexityFun_disjoint`). Embedding the points into the positions of `n`-bit
strings gives `n ≤ 2 ^ 9 R + 2 ^ 12` for the public-coin complexity `R` of `disjointness` with
error `ε ≤ 1 / 64` (`PublicCoin.le_mul_ecomplexityFun_disjointness_add_of_le`), and majority votes
of `72` runs (`PublicCoin.ecomplexityFun_le_two_mul_mul_one_third`) give
`n ≤ 2 ^ 16 R + 2 ^ 12` with error `1 / 3`, for public coins
(`PublicCoin.le_mul_ecomplexityFun_disjointness_add`) and private coins
(`PrivateCoin.le_mul_ecomplexityFun_disjointness_add`). The constants are not optimized.

## Main definitions

* `Cslib.Communication.disjointnessParts`: the partitions of the points.
* `Cslib.Communication.disjointnessDist`: the hard distribution.

## Main results

* `Cslib.Communication.four_mul_sum_card_filter_le`: families avoiding many points are small.
* `Cslib.Communication.corrupted_disjointnessDist`: Razborov's corruption lemma.
* `Cslib.Communication.PublicCoin.div_le_ecomplexityFun_disjoint`: the public-coin lower bound
  for subsets of `2 m + 1` points.
* `Cslib.Communication.PublicCoin.le_mul_ecomplexityFun_disjointness_add_of_le`,
  `Cslib.Communication.PublicCoin.le_mul_ecomplexityFun_disjointness_add`,
  `Cslib.Communication.PrivateCoin.le_mul_ecomplexityFun_disjointness_add`: disjointness of `n`
  bits needs `Ω(n)` bits with bounded error.

## References

* [B. Kalyanasundaram and G. Schnitger, *The probabilistic communication complexity of set
  intersection*][KalyanasundaramSchnitger1992]
* [A. A. Razborov, *On the distributional complexity of disjointness*][Razborov1992]
* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Communication

open Finset

variable {U : Type*} [DecidableEq U]

/-! ### Families of sets that avoid many points -/

omit [DecidableEq U] in
/-- Double counting incidences between points of `T` and members of `A`. -/
private theorem sum_card_filter_comm (A : Finset (Finset U)) (T : Finset U)
    (P : U → Finset U → Prop) [∀ i x, Decidable (P i x)] :
    ∑ i ∈ T, #{x ∈ A | P i x} = ∑ x ∈ A, #{i ∈ T | P i x} := by
  simp only [card_filter]
  exact sum_comm

/-- **A family of sets that avoid many points is small.** Let `A` be a family of sets and `S` a
finite set, and call a point `i ∈ S` *bad* if the members of `A` inside `S` containing `i` are
fewer than a third of those avoiding it. Then the pairs of a member of `A` inside `S` and a bad
point it avoids are at most a quarter of the pairs of a member inside `S` and a point of `S` it
avoids, up to `2 ^ #S (8 #S (27 / 32) ^ r + (j + 1) 2 ^ j (3 / 4) ^ #S)`, a small fraction of
`2 ^ #S` when `#S ≥ 48 r` and `j = 12 r`. If at least `3 r` points are bad, at least a quarter
of the members of `A` inside `S` meet a set `K` of `3 r` bad points in fewer than `r` points, by
Markov's inequality, and few subsets of `S` do (`Finset.two_pow_mul_card_filter_card_inter_le`).
Otherwise, the bad points are fewer than `(j + 1) / 4` and most members inside `S` avoid more than
`j` points, unless few subsets of `S` miss at most `j` points
(`Finset.two_pow_mul_card_filter_card_sdiff_le`). This is the key step of Razborov's corruption
lemma for `disjointnessDist` [Razborov1992]. -/
theorem four_mul_sum_card_filter_le (A : Finset (Finset U)) (S : Finset U) {r j : ℕ}
    (hrj : 12 * r ≤ j + 1) :
    4 * ∑ i ∈ S with 3 * #{x ∈ A | i ∈ x ∧ x ⊆ S} < #{x ∈ A | x ⊆ S ∧ i ∉ x},
        (#{x ∈ A | x ⊆ S ∧ i ∉ x} : ℝ) ≤
      ∑ i ∈ S, (#{x ∈ A | x ⊆ S ∧ i ∉ x} : ℝ) +
        2 ^ #S * (8 * #S * (27 / 32) ^ r + (j + 1) * 2 ^ j * (3 / 4) ^ #S) := by
  set AS := A.filter (· ⊆ S) with hAS
  set N := #AS with hNdef
  have hASsub : AS ⊆ S.powerset := fun x hx => mem_powerset.mpr (mem_filter.mp hx).2
  have hN : N ≤ 2 ^ #S := (card_le_card hASsub).trans (card_powerset S).le
  have havoid (i : U) : #{x ∈ A | x ⊆ S ∧ i ∉ x} = #{x ∈ AS | i ∉ x} := by
    rw [hAS, filter_filter]
  have hcontain (i : U) : #{x ∈ A | i ∈ x ∧ x ⊆ S} = #{x ∈ AS | i ∈ x} := by
    rw [hAS, filter_filter]
    congr 1
    exact filter_congr fun x _ => and_comm
  have hsplit (i : U) : #{x ∈ AS | i ∈ x} + #{x ∈ AS | i ∉ x} = N :=
    card_filter_add_card_filter_not _
  have havoid_le (i : U) : #{x ∈ A | x ⊆ S ∧ i ∉ x} ≤ N := by
    have := hsplit i
    rw [havoid]
    omega
  set bad := S.filter fun i => 3 * #{x ∈ A | i ∈ x ∧ x ⊆ S} < #{x ∈ A | x ⊆ S ∧ i ∉ x}
    with hbaddef
  have hsum_bad : ∑ i ∈ bad, #{x ∈ A | x ⊆ S ∧ i ∉ x} ≤ #bad * N :=
    (sum_le_sum fun i _ => havoid_le i).trans_eq (by rw [sum_const, smul_eq_mul])
  have hpos : (0 : ℝ) ≤ ∑ i ∈ S, (#{x ∈ A | x ⊆ S ∧ i ∉ x} : ℝ) :=
    sum_nonneg fun _ _ => Nat.cast_nonneg _
  by_cases hbad : 3 * r ≤ #bad
  · -- Many bad points: the family is small.
    have hsmall : N * 32 ^ r ≤ 2 * 27 ^ r * 2 ^ #S := by
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp only [pow_zero, mul_one]
        omega
      obtain ⟨K, hKbad, hKcard⟩ := exists_subset_card_eq hbad
      have hKS : K ⊆ S := hKbad.trans (filter_subset _ _)
      have hK4 (i : U) (hi : i ∈ K) : 4 * #{x ∈ AS | i ∈ x} ≤ N := by
        have := (mem_filter.mp (hKbad hi)).2
        have := hsplit i
        rw [hcontain, havoid] at *
        omega
      have hsumK : ∑ i ∈ K, #{x ∈ AS | i ∈ x} = ∑ x ∈ AS, #(K ∩ x) := by
        rw [sum_card_filter_comm]
        exact sum_congr rfl fun x _ => by rw [filter_mem_eq_inter]
      have h4sum : 4 * ∑ x ∈ AS, #(K ∩ x) ≤ 3 * r * N := by
        rw [← hsumK, mul_sum]
        calc ∑ i ∈ K, 4 * #{x ∈ AS | i ∈ x} ≤ ∑ _i ∈ K, N := sum_le_sum hK4
          _ = 3 * r * N := by rw [sum_const, hKcard, smul_eq_mul]
      -- Markov's inequality: few members meet `K` in at least `r` points.
      set G := AS.filter fun x => r ≤ #(K ∩ x)
      have hG : r * #G ≤ ∑ x ∈ AS, #(K ∩ x) := by
        rw [mul_comm, ← smul_eq_mul]
        exact (card_nsmul_le_sum _ _ _ fun x hx => (mem_filter.mp hx).2).trans
          (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.zero_le _)
      have h4G : 4 * #G ≤ 3 * N :=
        Nat.le_of_mul_le_mul_left (by nlinarith) hr
      have hGL : #G + #{x ∈ AS | ¬r ≤ #(K ∩ x)} = N := card_filter_add_card_filter_not _
      have hL : #{x ∈ AS | ¬r ≤ #(K ∩ x)} ≤ #{x ∈ S.powerset | #(K ∩ x) ≤ r - 1} := by
        refine card_le_card fun x hx => ?_
        obtain ⟨hx, hxr⟩ := mem_filter.mp hx
        exact mem_filter.mpr ⟨hASsub hx, by omega⟩
      have hcount := two_pow_mul_card_filter_card_inter_le hKS (r - 1)
      rw [hKcard, show 3 * r - (r - 1) = 2 * r + 1 by omega] at hcount
      have h3r : 3 * r ≤ #S := hKcard ▸ card_le_card hKS
      have key : 2 ^ (2 * r + 1) * N ≤ 4 * (3 ^ (3 * r) * 2 ^ (#S - 3 * r)) := by
        calc 2 ^ (2 * r + 1) * N ≤ 2 ^ (2 * r + 1) * (4 * #{x ∈ S.powerset | #(K ∩ x) ≤ r - 1}) :=
              Nat.mul_le_mul_left _ (by omega)
          _ ≤ 4 * (3 ^ (3 * r) * 2 ^ (#S - 3 * r)) := by
              rw [mul_left_comm]
              exact Nat.mul_le_mul_left _ hcount
      have h2S : 2 ^ (#S - 3 * r) * 2 ^ (3 * r) = 2 ^ #S := by
        rw [← pow_add, Nat.sub_add_cancel h3r]
      have h32 : (32 : ℕ) ^ r = 2 ^ (2 * r) * 2 ^ (3 * r) := by
        rw [← pow_add, show 2 * r + 3 * r = 5 * r by ring, pow_mul]
        norm_num
      have h27 : (27 : ℕ) ^ r = 3 ^ (3 * r) := by
        rw [pow_mul]
        norm_num
      have h := Nat.mul_le_mul_right (2 ^ (3 * r)) key
      rw [h32, h27]
      refine Nat.le_of_mul_le_mul_left ?_ (two_pos : 0 < 2)
      calc 2 * (N * (2 ^ (2 * r) * 2 ^ (3 * r))) = 2 ^ (2 * r + 1) * N * 2 ^ (3 * r) := by ring
        _ ≤ 4 * (3 ^ (3 * r) * 2 ^ (#S - 3 * r)) * 2 ^ (3 * r) := h
        _ = 2 * (2 * 3 ^ (3 * r) * (2 ^ (#S - 3 * r) * 2 ^ (3 * r))) := by ring
        _ = 2 * (2 * 3 ^ (3 * r) * 2 ^ #S) := by rw [h2S]
    have hNr : (N : ℝ) ≤ 2 * (27 / 32) ^ r * 2 ^ #S := by
      have h : (N : ℝ) * 32 ^ r ≤ 2 * 27 ^ r * 2 ^ #S := by exact_mod_cast hsmall
      rw [div_pow, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    have hbadS : #bad ≤ #S := card_le_card (filter_subset _ _)
    have h1 : (∑ i ∈ bad, (#{x ∈ A | x ⊆ S ∧ i ∉ x} : ℝ)) ≤ #S * N := by
      have : (∑ i ∈ bad, (#{x ∈ A | x ⊆ S ∧ i ∉ x} : ℝ)) ≤ #bad * N := by
        exact_mod_cast hsum_bad
      exact this.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hbadS) (by positivity))
    have h2 : (0 : ℝ) ≤ 2 ^ #S * ((j + 1) * 2 ^ j * (3 / 4) ^ #S) := by positivity
    have h3 : (#S : ℝ) * N ≤ #S * (2 * (27 / 32) ^ r * 2 ^ #S) :=
      mul_le_mul_of_nonneg_left hNr (by positivity)
    nlinarith
  · -- Few bad points: most members of the family avoid many points.
    push Not at hbad
    have hS : ∑ i ∈ S, #{x ∈ A | x ⊆ S ∧ i ∉ x} = ∑ x ∈ AS, #(S \ x) := by
      simp only [havoid]
      rw [sum_card_filter_comm]
      exact sum_congr rfl fun x _ => by rw [sdiff_eq_filter]
    set H := AS.filter fun x => j < #(S \ x)
    have hH : (j + 1) * #H ≤ ∑ x ∈ AS, #(S \ x) := by
      rw [mul_comm, ← smul_eq_mul]
      exact (card_nsmul_le_sum _ _ _ fun x hx => (mem_filter.mp hx).2).trans
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.zero_le _)
    have hHH : #H + #{x ∈ AS | ¬j < #(S \ x)} = N := card_filter_add_card_filter_not _
    have hH' : #{x ∈ AS | ¬j < #(S \ x)} ≤ #{x ∈ S.powerset | #(S \ x) ≤ j} := by
      refine card_le_card fun x hx => ?_
      obtain ⟨hx, hxj⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨hASsub hx, by omega⟩
    have hcount := two_pow_mul_card_filter_card_sdiff_le S j
    have hcount' : 2 ^ #S * #{x ∈ S.powerset | #(S \ x) ≤ j} ≤ 2 ^ j * 3 ^ #S := by
      calc 2 ^ #S * #{x ∈ S.powerset | #(S \ x) ≤ j}
          ≤ 2 ^ j * 2 ^ (#S - j) * #{x ∈ S.powerset | #(S \ x) ≤ j} :=
            Nat.mul_le_mul_right _ (by
              rw [← pow_add]
              exact Nat.pow_le_pow_right two_pos (by omega))
        _ ≤ 2 ^ j * 3 ^ #S := by rw [mul_assoc]; exact Nat.mul_le_mul_left _ hcount
    -- The bad points carry at most `3 r N ≤ (j + 1) N / 4` incidences.
    have hmain : 4 * ∑ i ∈ bad, #{x ∈ A | x ⊆ S ∧ i ∉ x} ≤
        ∑ i ∈ S, #{x ∈ A | x ⊆ S ∧ i ∉ x} + (j + 1) * #{x ∈ S.powerset | #(S \ x) ≤ j} := by
      rw [hS]
      have h12 : 4 * (#bad * N) ≤ (j + 1) * N := by
        rw [← mul_assoc]
        exact Nat.mul_le_mul_right _ (by omega)
      calc 4 * ∑ i ∈ bad, #{x ∈ A | x ⊆ S ∧ i ∉ x} ≤ 4 * (#bad * N) :=
            Nat.mul_le_mul_left _ hsum_bad
        _ ≤ (j + 1) * N := h12
        _ = (j + 1) * #H + (j + 1) * #{x ∈ AS | ¬j < #(S \ x)} := by rw [← hHH, mul_add]
        _ ≤ ∑ x ∈ AS, #(S \ x) + (j + 1) * #{x ∈ S.powerset | #(S \ x) ≤ j} :=
            Nat.add_le_add hH (Nat.mul_le_mul_left _ hH')
    have hmainR : 4 * ∑ i ∈ bad, (#{x ∈ A | x ⊆ S ∧ i ∉ x} : ℝ) ≤
        ∑ i ∈ S, (#{x ∈ A | x ⊆ S ∧ i ∉ x} : ℝ) +
          (j + 1) * #{x ∈ S.powerset | #(S \ x) ≤ j} := by
      exact_mod_cast hmain
    have hcountR : (2 : ℝ) ^ #S * #{x ∈ S.powerset | #(S \ x) ≤ j} ≤ 2 ^ j * 3 ^ #S := by
      exact_mod_cast hcount'
    have h34 : (2 : ℝ) ^ #S * (2 ^ #S * (3 / 4) ^ #S) = 3 ^ #S := by
      rw [← mul_assoc, ← mul_pow, ← mul_pow]
      norm_num
    have hQ : ((j : ℝ) + 1) * #{x ∈ S.powerset | #(S \ x) ≤ j} ≤
        2 ^ #S * ((j + 1) * 2 ^ j * (3 / 4) ^ #S) := by
      have h2pos : (0 : ℝ) < 2 ^ #S := by positivity
      rw [← mul_le_mul_iff_of_pos_left h2pos]
      calc (2 : ℝ) ^ #S * (((j : ℝ) + 1) * #{x ∈ S.powerset | #(S \ x) ≤ j})
          = ((j : ℝ) + 1) * (2 ^ #S * #{x ∈ S.powerset | #(S \ x) ≤ j}) := by ring
        _ ≤ ((j : ℝ) + 1) * (2 ^ j * 3 ^ #S) :=
            mul_le_mul_of_nonneg_left hcountR (by positivity)
        _ = 2 ^ #S * (2 ^ #S * ((j + 1) * 2 ^ j * (3 / 4) ^ #S)) := by
            rw [← h34]
            ring
    have h8 : (0 : ℝ) ≤ 2 ^ #S * (8 * #S * (27 / 32) ^ r) := by positivity
    nlinarith

/-! ### Partitions of the points -/

section Partitions

variable [Fintype U] {m : ℕ}

variable (U) in
/-- The triples `(i, Tx, Ty)` of a point `i` and two disjoint sets `Tx`, `Ty` of `m` points that
avoid it. When there are `2 m + 1` points, these are the ordered partitions of the points into
parts of sizes `1`, `m` and `m`. -/
def disjointnessParts (m : ℕ) : Finset (U × Finset U × Finset U) :=
  {T | T.1 ∉ T.2.1 ∧ T.1 ∉ T.2.2 ∧ Disjoint T.2.1 T.2.2 ∧ #T.2.1 = m ∧ #T.2.2 = m}

theorem mem_disjointnessParts {T : U × Finset U × Finset U} :
    T ∈ disjointnessParts U m ↔
      T.1 ∉ T.2.1 ∧ T.1 ∉ T.2.2 ∧ Disjoint T.2.1 T.2.2 ∧ #T.2.1 = m ∧ #T.2.2 = m := by
  simp only [disjointnessParts, mem_filter, mem_univ, true_and]

/-- In a partition `(i, Tx, Ty)` of `2 m + 1` points, `Tx` is the complement of `Ty` and `i`. -/
theorem compl_insert_eq_of_mem_disjointnessParts (hU : Fintype.card U = 2 * m + 1)
    {T : U × Finset U × Finset U} (hT : T ∈ disjointnessParts U m) :
    (insert T.1 T.2.2)ᶜ = T.2.1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mem_disjointnessParts.mp hT
  symm
  refine eq_of_subset_of_card_le (fun a ha => ?_) ?_
  · rw [mem_compl, mem_insert, not_or]
    exact ⟨fun h => h1 (h ▸ ha), fun h => disjoint_left.mp h3 ha h⟩
  · rw [card_compl, card_insert_of_notMem h2, hU, h4, h5]
    omega

private theorem mem_disjointnessParts_of_mem_compl (hU : Fintype.card U = 2 * m + 1)
    {Ty : Finset U} (hTy : #Ty = m) {i : U} (hi : i ∈ Tyᶜ) :
    (i, (insert i Ty)ᶜ, Ty) ∈ disjointnessParts U m := by
  rw [mem_compl] at hi
  refine mem_disjointnessParts.mpr ⟨by simp, hi, ?_, ?_, hTy⟩
  · exact disjoint_left.mpr fun a ha haTy => mem_compl.mp ha (mem_insert_of_mem haTy)
  · rw [card_compl, card_insert_of_notMem hi, hU, hTy]
    omega

/-- Summing over the partitions `(i, Tx, Ty)` of `2 m + 1` points is summing over the sets `Ty`
of `m` points and the points `i` outside them. -/
theorem sum_disjointnessParts (hU : Fintype.card U = 2 * m + 1) {M : Type*} [AddCommMonoid M]
    (F : U × Finset U × Finset U → M) :
    ∑ T ∈ disjointnessParts U m, F T =
      ∑ Ty ∈ powersetCard m univ, ∑ i ∈ Tyᶜ, F (i, (insert i Ty)ᶜ, Ty) := by
  rw [sum_sigma']
  refine sum_nbij' (fun T => ⟨T.2.2, T.1⟩) (fun x => (x.2, (insert x.2 x.1)ᶜ, x.1)) ?_ ?_ ?_
    (fun _ _ => rfl) ?_
  · intro T hT
    obtain ⟨-, h2, -, -, h5⟩ := mem_disjointnessParts.mp hT
    exact mem_sigma.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, h5⟩, mem_compl.mpr h2⟩
  · rintro ⟨Ty, i⟩ hx
    obtain ⟨hTy, hi⟩ := mem_sigma.mp hx
    exact mem_disjointnessParts_of_mem_compl hU (mem_powersetCard.mp hTy).2 hi
  · intro T hT
    simp only [compl_insert_eq_of_mem_disjointnessParts hU hT]
  · intro T hT
    simp only [compl_insert_eq_of_mem_disjointnessParts hU hT]

/-- Exchanging the two sets of a partition. -/
theorem sum_disjointnessParts_swap {M : Type*} [AddCommMonoid M]
    (F : U × Finset U × Finset U → M) :
    ∑ T ∈ disjointnessParts U m, F T = ∑ T ∈ disjointnessParts U m, F (T.1, T.2.2, T.2.1) := by
  refine sum_nbij' (fun T => (T.1, T.2.2, T.2.1)) (fun T => (T.1, T.2.2, T.2.1)) ?_ ?_
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) <;>
  · intro T hT
    obtain ⟨h1, h2, h3, h4, h5⟩ := mem_disjointnessParts.mp hT
    exact mem_disjointnessParts.mpr ⟨h2, h1, h3.symm, h5, h4⟩

theorem card_disjointnessParts (hU : Fintype.card U = 2 * m + 1) :
    #(disjointnessParts U m) = #(powersetCard m (univ : Finset U)) * (m + 1) := by
  rw [card_eq_sum_ones, sum_disjointnessParts hU]
  simp only [sum_const, smul_eq_mul, mul_one]
  rw [sum_congr rfl fun Ty hTy => by
    rw [card_compl, hU, (mem_powersetCard.mp hTy).2]]
  rw [sum_const, smul_eq_mul]
  congr 1
  omega

theorem card_disjointnessParts_pos (hU : Fintype.card U = 2 * m + 1) :
    0 < #(disjointnessParts U m) := by
  rw [card_disjointnessParts hU, card_powersetCard, card_univ, hU]
  exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.succ_pos m)

end Partitions

/-! ### The corruption inequality over partitions -/

section Corruption

variable [Fintype U] {m : ℕ}

/-- The members of `A` inside `s`. -/
private def low (A : Finset (Finset U)) (s : Finset U) : ℕ :=
  #{x ∈ A | x ⊆ s}

/-- The members of `A` containing `i` and avoiding `s`. -/
private def high (A : Finset (Finset U)) (i : U) (s : Finset U) : ℕ :=
  #{x ∈ A | i ∈ x ∧ x ⊆ sᶜ}

private theorem low_compl_insert (A : Finset (Finset U)) (i : U) (s : Finset U) :
    low A (insert i s)ᶜ = #{x ∈ A | x ⊆ sᶜ ∧ i ∉ x} := by
  unfold low
  congr 1
  refine filter_congr fun x _ => ?_
  simp only [subset_iff, mem_compl, mem_insert, not_or]
  exact ⟨fun h => ⟨fun a ha => (h ha).2, fun hi => (h hi).1 rfl⟩,
    fun h a ha => ⟨fun hai => h.2 (hai ▸ ha), h.1 ha⟩⟩

omit [Fintype U] in
private theorem low_le_two_pow (A : Finset (Finset U)) (s : Finset U) : low A s ≤ 2 ^ #s := by
  rw [← card_powerset]
  exact card_le_card fun x hx => mem_powerset.mpr (mem_filter.mp hx).2

/-- The error terms of `four_mul_sum_card_filter_le` for `j = 12 r` and `#S ≥ 48 r`. -/
private theorem slack_le {r s : ℕ} (hs : 48 * r ≤ s) (hs1 : 1 ≤ s) :
    8 * s * (27 / 32 : ℝ) ^ r + (((12 * r : ℕ) : ℝ) + 1) * 2 ^ (12 * r) * (3 / 4) ^ s ≤
      9 * s * (27 / 32) ^ r := by
  have h1 : ((12 * r : ℕ) : ℝ) + 1 ≤ s := by exact_mod_cast (show 12 * r + 1 ≤ s by omega)
  have h2 : (3 / 4 : ℝ) ^ s ≤ (3 / 4) ^ (48 * r) := pow_le_pow_of_le_one (by norm_num)
    (by norm_num) hs
  have h3 : (2 : ℝ) ^ (12 * r) * (3 / 4) ^ (48 * r) ≤ (27 / 32) ^ r := by
    rw [pow_mul, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by norm_num) r
  have h4 : (((12 * r : ℕ) : ℝ) + 1) * 2 ^ (12 * r) * (3 / 4) ^ s ≤ s * (27 / 32) ^ r := by
    calc (((12 * r : ℕ) : ℝ) + 1) * 2 ^ (12 * r) * (3 / 4) ^ s
        ≤ s * (2 ^ (12 * r) * (3 / 4) ^ (48 * r)) := by
          rw [mul_assoc]
          exact mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity)
            (by positivity)
      _ ≤ s * (27 / 32) ^ r := mul_le_mul_of_nonneg_left h3 (by positivity)
  linarith

/-- **The corruption inequality on one side.** Over the partitions `(i, Tx, Ty)` of `2 m + 1`
points, the products `low A Tx * low B Ty` with `i` bad for `A` relative to `Ty` add up to at most
a quarter of all of them, up to an exponentially small error. -/
private theorem four_mul_sum_filter_le (hU : Fintype.card U = 2 * m + 1)
    (A B : Finset (Finset U)) {r : ℕ} (hr : 48 * r ≤ m + 1) :
    4 * ∑ T ∈ disjointnessParts U m with 3 * high A T.1 T.2.2 < low A T.2.1,
        ((low A T.2.1 : ℝ) * low B T.2.2) ≤
      ∑ T ∈ disjointnessParts U m, ((low A T.2.1 : ℝ) * low B T.2.2) +
        18 * #(disjointnessParts U m) * 4 ^ m * (27 / 32) ^ r := by
  rw [sum_filter, sum_disjointnessParts hU, sum_disjointnessParts hU, card_disjointnessParts hU,
    mul_sum]
  have hconst : (18 : ℝ) * ((#(powersetCard m (univ : Finset U)) * (m + 1) : ℕ) : ℝ) * 4 ^ m *
      (27 / 32) ^ r = ∑ _Ty ∈ powersetCard m (univ : Finset U),
        18 * ((m : ℝ) + 1) * 4 ^ m * (27 / 32) ^ r := by
    rw [sum_const, nsmul_eq_mul]
    push_cast
    ring
  rw [hconst, ← sum_add_distrib]
  refine sum_le_sum fun Ty hTy => ?_
  have hTy : #Ty = m := (mem_powersetCard.mp hTy).2
  have hS : #Tyᶜ = m + 1 := by
    rw [card_compl, hU, hTy]
    omega
  have hb : (low B Ty : ℝ) ≤ 2 ^ m := by
    have := low_le_two_pow B Ty
    rw [hTy] at this
    exact_mod_cast this
  have hKL := four_mul_sum_card_filter_le A Tyᶜ (r := r) (j := 12 * r) (by omega)
  rw [hS] at hKL
  have hsl := slack_le (r := r) (s := m + 1) hr (by omega)
  push_cast at hsl
  simp only [low_compl_insert, high]
  rw [← sum_filter, ← sum_mul, ← sum_mul]
  set a := ∑ i ∈ Tyᶜ with 3 * #{x ∈ A | i ∈ x ∧ x ⊆ Tyᶜ} < #{x ∈ A | x ⊆ Tyᶜ ∧ i ∉ x},
    (#{x ∈ A | x ⊆ Tyᶜ ∧ i ∉ x} : ℝ)
  set a' := ∑ i ∈ Tyᶜ, (#{x ∈ A | x ⊆ Tyᶜ ∧ i ∉ x} : ℝ)
  have hb0 : (0 : ℝ) ≤ low B Ty := Nat.cast_nonneg _
  have hpow : (2 : ℝ) ^ (m + 1) * 2 ^ m = 2 * 4 ^ m := by
    rw [pow_succ, show (4 : ℝ) ^ m = 2 ^ m * 2 ^ m by rw [← mul_pow]; norm_num]
    ring
  have hE : (2 : ℝ) ^ (m + 1) * (8 * ((m : ℝ) + 1) * (27 / 32) ^ r +
      (((12 * r : ℕ) : ℝ) + 1) * 2 ^ (12 * r) * (3 / 4) ^ (m + 1)) ≤
      2 ^ (m + 1) * (9 * ((m : ℝ) + 1) * (27 / 32) ^ r) :=
    mul_le_mul_of_nonneg_left (by push_cast; linarith) (by positivity)
  push_cast at hKL hE
  have h1 : 4 * a * low B Ty ≤ (a' + 2 ^ (m + 1) * (9 * ((m : ℝ) + 1) * (27 / 32) ^ r)) *
      low B Ty := mul_le_mul_of_nonneg_right (by linarith) hb0
  have h2 : (2 : ℝ) ^ (m + 1) * (9 * ((m : ℝ) + 1) * (27 / 32) ^ r) * low B Ty ≤
      2 ^ (m + 1) * (9 * ((m : ℝ) + 1) * (27 / 32) ^ r) * 2 ^ m :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  have h3 : (2 : ℝ) ^ (m + 1) * (9 * ((m : ℝ) + 1) * (27 / 32) ^ r) * 2 ^ m =
      18 * ((m : ℝ) + 1) * 4 ^ m * (27 / 32) ^ r := by
    rw [mul_comm _ ((2 : ℝ) ^ m), ← mul_assoc, mul_comm ((2 : ℝ) ^ m), hpow]
    ring
  nlinarith

/-- **The corruption inequality over partitions.** Over the partitions `(i, Tx, Ty)` of `2 m + 1`
points, the members of `A` inside `Tx` times the members of `B` inside `Ty` add up to at most `18`
times the members of `A` containing `i` inside `Tx ∪ {i}` times the members of `B` containing `i`
inside `Ty ∪ {i}`, up to an exponentially small error. -/
private theorem sum_low_mul_low_le (hU : Fintype.card U = 2 * m + 1) (A B : Finset (Finset U))
    {r : ℕ} (hr : 48 * r ≤ m + 1) :
    ∑ T ∈ disjointnessParts U m, ((low A T.2.1 : ℝ) * low B T.2.2) ≤
      18 * ∑ T ∈ disjointnessParts U m, ((high A T.1 T.2.2 : ℝ) * high B T.1 T.2.1) +
        18 * #(disjointnessParts U m) * 4 ^ m * (27 / 32) ^ r := by
  have hX := four_mul_sum_filter_le hU A B hr
  have hY := four_mul_sum_filter_le hU B A hr
  rw [sum_filter] at hX hY
  rw [sum_disjointnessParts_swap, sum_disjointnessParts_swap (fun T => (low B T.2.1 : ℝ) *
    low A T.2.2)] at hY
  have hpt : ∀ T ∈ disjointnessParts U m, (low A T.2.1 : ℝ) * low B T.2.2 ≤
      9 * ((high A T.1 T.2.2 : ℝ) * high B T.1 T.2.1) +
        ((if 3 * high A T.1 T.2.2 < low A T.2.1 then (low A T.2.1 : ℝ) * low B T.2.2 else 0) +
          (if 3 * high B T.1 T.2.1 < low B T.2.2 then (low B T.2.2 : ℝ) * low A T.2.1
            else 0)) := by
    intro T _
    have h0 : (0 : ℝ) ≤ (low A T.2.1 : ℝ) * low B T.2.2 := by positivity
    have h0' : (0 : ℝ) ≤ (high A T.1 T.2.2 : ℝ) * high B T.1 T.2.1 := by positivity
    by_cases hx : 3 * high A T.1 T.2.2 < low A T.2.1
    · by_cases hy : 3 * high B T.1 T.2.1 < low B T.2.2
      · simp only [hx, hy, ↓reduceIte]
        nlinarith
      · simp only [hx, hy, ↓reduceIte]
        linarith
    · by_cases hy : 3 * high B T.1 T.2.1 < low B T.2.2
      · simp only [hx, hy, ↓reduceIte]
        nlinarith
      · simp only [hx, hy, ↓reduceIte, add_zero]
        push Not at hx hy
        have hx' : (low A T.2.1 : ℝ) ≤ 3 * high A T.1 T.2.2 := by exact_mod_cast hx
        have hy' : (low B T.2.2 : ℝ) ≤ 3 * high B T.1 T.2.1 := by exact_mod_cast hy
        have := mul_le_mul hx' hy' (Nat.cast_nonneg _) (by positivity)
        linarith
  have h := sum_le_sum hpt
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum] at h
  have hcomm : ∑ T ∈ disjointnessParts U m, (low B T.2.2 : ℝ) * low A T.2.1 =
      ∑ T ∈ disjointnessParts U m, (low A T.2.1 : ℝ) * low B T.2.2 :=
    sum_congr rfl fun _ _ => mul_comm _ _
  simp only at hY
  rw [hcomm] at hY
  linarith

/-! ### The hard distribution -/

variable (m) in
/-- The mass of a pair of sets under `disjointnessDist`: the probability that a uniformly random
partition `(i, Tx, Ty)` from `disjointnessParts` and a fair coin produce it, where on heads the
pair is a uniformly random pair of subsets of `Tx` and `Ty`, and on tails it is such a pair with
`i` added to both sets. -/
noncomputable def disjointnessWeight (q : Finset U × Finset U) : ℝ :=
  (∑ T ∈ disjointnessParts U m,
    ((if q.1 ⊆ T.2.1 then 1 else 0) * (if q.2 ⊆ T.2.2 then 1 else 0) +
      (if T.1 ∈ q.1 ∧ q.1 ⊆ T.2.2ᶜ then 1 else 0) * (if T.1 ∈ q.2 ∧ q.2 ⊆ T.2.1ᶜ then 1 else 0))) /
    (2 * #(disjointnessParts U m) * 4 ^ m)

theorem disjointnessWeight_nonneg (q : Finset U × Finset U) : 0 ≤ disjointnessWeight m q := by
  unfold disjointnessWeight
  refine div_nonneg (sum_nonneg fun T _ => ?_) (by positivity)
  split_ifs <;> norm_num

/-- On disjoint pairs the weight counts the partitions placing the sets inside `Tx` and `Ty`;
on intersecting pairs, those placing them inside `Tx ∪ {i}` and `Ty ∪ {i}` with `i` common. -/
private theorem ite_disjointnessWeight (x y : Finset U) :
    (if decide (Disjoint x y) = true then disjointnessWeight m (x, y) else 0) =
        (∑ T ∈ disjointnessParts U m,
          (if x ⊆ T.2.1 then 1 else 0) * (if y ⊆ T.2.2 then 1 else 0)) /
          (2 * #(disjointnessParts U m) * 4 ^ m) ∧
      (if decide (Disjoint x y) = true then 0 else disjointnessWeight m (x, y)) =
        (∑ T ∈ disjointnessParts U m,
          (if T.1 ∈ x ∧ x ⊆ T.2.2ᶜ then 1 else 0) * (if T.1 ∈ y ∧ y ⊆ T.2.1ᶜ then 1 else 0)) /
          (2 * #(disjointnessParts U m) * 4 ^ m) := by
  unfold disjointnessWeight
  by_cases h : Disjoint x y
  · simp only [h, decide_true, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · congr 1
      refine sum_congr rfl fun T _ => ?_
      have : ¬(T.1 ∈ x ∧ T.1 ∈ y) := fun hT => disjoint_left.mp h hT.1 hT.2
      by_cases h1 : T.1 ∈ x ∧ x ⊆ T.2.2ᶜ
      · have h2 : ¬(T.1 ∈ y ∧ y ⊆ T.2.1ᶜ) := fun h2 => this ⟨h1.1, h2.1⟩
        simp only [h2, ↓reduceIte, mul_zero, add_zero]
      · simp only [h1, ↓reduceIte, zero_mul, add_zero]
    · symm
      refine div_eq_zero_iff.mpr (Or.inl (sum_eq_zero fun T _ => ?_))
      have : ¬(T.1 ∈ x ∧ T.1 ∈ y) := fun hT => disjoint_left.mp h hT.1 hT.2
      by_cases h1 : T.1 ∈ x ∧ x ⊆ T.2.2ᶜ
      · have h2 : ¬(T.1 ∈ y ∧ y ⊆ T.2.1ᶜ) := fun h2 => this ⟨h1.1, h2.1⟩
        simp only [h2, ↓reduceIte, mul_zero]
      · simp only [h1, ↓reduceIte, zero_mul]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · symm
      refine div_eq_zero_iff.mpr (Or.inl (sum_eq_zero fun T hT => ?_))
      have hT := (mem_disjointnessParts.mp hT).2.2.1
      by_cases h1 : x ⊆ T.2.1
      · have h2 : ¬y ⊆ T.2.2 := fun h2 => h (hT.mono h1 h2)
        simp only [h2, ↓reduceIte, mul_zero]
      · simp only [h1, ↓reduceIte, zero_mul]
    · congr 1
      refine sum_congr rfl fun T hT => ?_
      have hT := (mem_disjointnessParts.mp hT).2.2.1
      by_cases h1 : x ⊆ T.2.1
      · have h2 : ¬y ⊆ T.2.2 := fun h2 => h (hT.mono h1 h2)
        simp only [h2, ↓reduceIte, mul_zero, zero_add]
      · simp only [h1, ↓reduceIte, zero_mul, zero_add]

/-- Summing products of indicators over a rectangle. -/
private theorem sum_sum_ite_mul_ite (A B : Finset (Finset U)) (p : U × Finset U × Finset U →
    Finset U → Prop) (q : U × Finset U × Finset U → Finset U → Prop) [∀ T x, Decidable (p T x)]
    [∀ T y, Decidable (q T y)] (D : ℝ) :
    ∑ x ∈ A, ∑ y ∈ B, (∑ T ∈ disjointnessParts U m,
        (if p T x then (1 : ℝ) else 0) * (if q T y then 1 else 0)) / D =
      (∑ T ∈ disjointnessParts U m, (#{x ∈ A | p T x} : ℝ) * #{y ∈ B | q T y}) / D := by
  simp only [← sum_div]
  congr 1
  calc ∑ x ∈ A, ∑ y ∈ B, ∑ T ∈ disjointnessParts U m,
        (if p T x then (1 : ℝ) else 0) * (if q T y then 1 else 0)
      = ∑ x ∈ A, ∑ T ∈ disjointnessParts U m, ∑ y ∈ B,
          (if p T x then (1 : ℝ) else 0) * (if q T y then 1 else 0) :=
        sum_congr rfl fun _ _ => sum_comm
    _ = ∑ T ∈ disjointnessParts U m, ∑ x ∈ A, ∑ y ∈ B,
          (if p T x then (1 : ℝ) else 0) * (if q T y then 1 else 0) := sum_comm
    _ = _ := by
        refine sum_congr rfl fun T _ => ?_
        rw [← sum_mul_sum, sum_boole, sum_boole]

/-- The weight of the disjoint pairs in a rectangle. -/
private theorem sum_sum_ite_disjointnessWeight (A B : Finset (Finset U)) :
    ∑ x ∈ A, ∑ y ∈ B, (if decide (Disjoint x y) = true then disjointnessWeight m (x, y) else 0) =
      (∑ T ∈ disjointnessParts U m, ((low A T.2.1 : ℝ) * low B T.2.2)) /
        (2 * #(disjointnessParts U m) * 4 ^ m) := by
  simp only [fun x y => (ite_disjointnessWeight (m := m) x y).1]
  exact sum_sum_ite_mul_ite A B (fun T x => x ⊆ T.2.1) (fun T y => y ⊆ T.2.2) _

/-- The weight of the intersecting pairs in a rectangle. -/
private theorem sum_sum_ite_disjointnessWeight' (A B : Finset (Finset U)) :
    ∑ x ∈ A, ∑ y ∈ B, (if decide (Disjoint x y) = true then 0 else disjointnessWeight m (x, y)) =
      (∑ T ∈ disjointnessParts U m, ((high A T.1 T.2.2 : ℝ) * high B T.1 T.2.1)) /
        (2 * #(disjointnessParts U m) * 4 ^ m) := by
  simp only [fun x y => (ite_disjointnessWeight (m := m) x y).2]
  exact sum_sum_ite_mul_ite A B (fun T x => T.1 ∈ x ∧ x ⊆ T.2.2ᶜ)
    (fun T y => T.1 ∈ y ∧ y ⊆ T.2.1ᶜ) _

omit [Fintype U] in
private theorem low_univ (s : Finset U) [Fintype U] : low univ s = 2 ^ #s := by
  unfold low
  rw [← card_powerset]
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and, mem_powerset]

private theorem high_univ {i : U} {s : Finset U} (hi : i ∉ s) :
    high univ i s = 2 ^ (#sᶜ - 1) := by
  unfold high
  have hi' : i ∈ sᶜ := mem_compl.mpr hi
  have h1 : #{x ∈ (univ : Finset (Finset U)) | i ∈ x ∧ x ⊆ sᶜ} = #{x ∈ sᶜ.powerset | i ∈ x} := by
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_powerset]
    exact and_comm
  have h2 : {x ∈ sᶜ.powerset | i ∉ x} = (sᶜ.erase i).powerset := by
    ext x
    simp only [mem_filter, mem_powerset, subset_erase]
  have h3 := (card_filter_add_card_filter_not (s := sᶜ.powerset) fun x => i ∈ x).trans
    (card_powerset sᶜ)
  have h4 : #(sᶜ.erase i).powerset = 2 ^ (#sᶜ - 1) := by
    rw [card_powerset, card_erase_of_mem hi']
  have h5 : 2 ^ #sᶜ = 2 ^ (#sᶜ - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel (card_pos.mpr ⟨i, hi'⟩)]
  rw [h2, h4, h5] at h3
  rw [h1]
  omega

/-- Half of the weight lies on disjoint pairs. -/
private theorem sum_sum_ite_disjointnessWeight_univ (hU : Fintype.card U = 2 * m + 1) :
    ∑ x : Finset U, ∑ y : Finset U,
        (if decide (Disjoint x y) = true then disjointnessWeight m (x, y) else 0) = 1 / 2 ∧
      ∑ x : Finset U, ∑ y : Finset U,
        (if decide (Disjoint x y) = true then 0 else disjointnessWeight m (x, y)) = 1 / 2 := by
  have hP : (0 : ℝ) < #(disjointnessParts U m) := by
    exact_mod_cast card_disjointnessParts_pos hU
  have hcompl {s : Finset U} (hs : #s = m) : #sᶜ - 1 = m := by
    rw [card_compl, hU, hs]
    omega
  refine ⟨?_, ?_⟩
  · rw [sum_sum_ite_disjointnessWeight]
    rw [sum_congr rfl fun T hT => by
      rw [low_univ, low_univ, (mem_disjointnessParts.mp hT).2.2.2.1,
        (mem_disjointnessParts.mp hT).2.2.2.2]]
    rw [sum_const, nsmul_eq_mul]
    field_simp
    push_cast
    rw [show (4 : ℝ) ^ m = 2 ^ m * 2 ^ m by rw [← mul_pow]; norm_num]
    ring
  · rw [sum_sum_ite_disjointnessWeight']
    rw [sum_congr rfl fun T hT => by
      obtain ⟨h1, h2, -, h4, h5⟩ := mem_disjointnessParts.mp hT
      rw [high_univ h2, high_univ h1, hcompl h4, hcompl h5]]
    rw [sum_const, nsmul_eq_mul]
    field_simp
    push_cast
    rw [show (4 : ℝ) ^ m = 2 ^ m * 2 ^ m by rw [← mul_pow]; norm_num]
    ring

theorem sum_disjointnessWeight (hU : Fintype.card U = 2 * m + 1) :
    ∑ q : Finset U × Finset U, disjointnessWeight m q = 1 := by
  obtain ⟨h1, h2⟩ := sum_sum_ite_disjointnessWeight_univ hU
  rw [Fintype.sum_prod_type]
  calc ∑ x : Finset U, ∑ y : Finset U, disjointnessWeight m (x, y)
      = ∑ x : Finset U, ∑ y : Finset U,
          ((if decide (Disjoint x y) = true then disjointnessWeight m (x, y) else 0) +
            (if decide (Disjoint x y) = true then 0 else disjointnessWeight m (x, y))) := by
        refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
        split_ifs <;> simp
    _ = 1 := by
        simp only [sum_add_distrib, h1, h2]
        norm_num

variable (m) in
/-- **A hard distribution for disjointness**, a variant of Razborov's distribution
[Razborov1992] on pairs of subsets of `2 m + 1` points. Draw a uniformly random partition
`(i, Tx, Ty)` of the points into a point and two sets of `m` points, and uniformly random subsets
`x ⊆ Tx` and `y ⊆ Ty`; with probability `1 / 2` output the disjoint pair `(x, y)`, and otherwise
the pair `(x ∪ {i}, y ∪ {i})`, which meets in exactly `i`. Razborov draws subsets of fixed size
`m / 2` instead; drawing all subsets lets the corruption bound be proved by counting subsets of
a cube (`four_mul_sum_card_filter_le`) instead of with entropy. -/
noncomputable def disjointnessDist (hU : Fintype.card U = 2 * m + 1) :
    PMF (Finset U × Finset U) :=
  PMF.ofFintype (fun q => ENNReal.ofReal (disjointnessWeight m q)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun q _ => disjointnessWeight_nonneg q,
      sum_disjointnessWeight hU, ENNReal.ofReal_one])

theorem disjointnessDist_apply_toReal (hU : Fintype.card U = 2 * m + 1)
    (q : Finset U × Finset U) : (disjointnessDist m hU q).toReal = disjointnessWeight m q := by
  rw [disjointnessDist, PMF.ofFintype_apply, ENNReal.toReal_ofReal (disjointnessWeight_nonneg q)]

/-- Under `disjointnessDist`, the sets are disjoint with probability `1 / 2`. -/
theorem disjointnessDist_toOuterMeasure_disjoint (hU : Fintype.card U = 2 * m + 1) :
    ((disjointnessDist m hU).toOuterMeasure
      {q | decide (Disjoint q.1 q.2) = true}).toReal = 1 / 2 := by
  rw [Probability.PMF.toOuterMeasure_apply_toReal, Fintype.sum_prod_type]
  simp only [Set.mem_ofPred_eq, disjointnessDist_apply_toReal]
  exact (sum_sum_ite_disjointnessWeight_univ hU).1

/-- **Razborov's corruption lemma** for `disjointnessDist` [Razborov1992]: on every rectangle
`A × B` of pairs of subsets of `2 m + 1` points, the intersecting pairs carry at least `1 / 18`
of the mass of the disjoint pairs, up to `(27 / 32) ^ r / 2` whenever `48 r ≤ m + 1`. -/
theorem corrupted_disjointnessDist (hU : Fintype.card U = 2 * m + 1) {r : ℕ}
    (hr : 48 * r ≤ m + 1) :
    Corrupted (disjointnessDist m hU) (fun x y => decide (Disjoint x y)) true (1 / 18)
      ((27 / 32) ^ r / 2) := by
  intro A B
  simp only [disjointnessDist_apply_toReal]
  rw [sum_sum_ite_disjointnessWeight, sum_sum_ite_disjointnessWeight']
  have h := sum_low_mul_low_le hU A B hr
  have hP : (0 : ℝ) < #(disjointnessParts U m) := by
    exact_mod_cast card_disjointnessParts_pos hU
  have hD : (0 : ℝ) < 2 * #(disjointnessParts U m) * 4 ^ m := by positivity
  set P := ∑ T ∈ disjointnessParts U m, ((low A T.2.1 : ℝ) * low B T.2.2)
  set Q := ∑ T ∈ disjointnessParts U m, ((high A T.1 T.2.2 : ℝ) * high B T.1 T.2.1)
  have key : P / (2 * #(disjointnessParts U m) * 4 ^ m) ≤
      18 * (Q / (2 * #(disjointnessParts U m) * 4 ^ m)) + 9 * (27 / 32) ^ r := by
    rw [div_le_iff₀ hD]
    have : (18 * (Q / (2 * #(disjointnessParts U m) * 4 ^ m)) + 9 * (27 / 32) ^ r) *
        (2 * #(disjointnessParts U m) * 4 ^ m) =
          18 * Q + 18 * #(disjointnessParts U m) * 4 ^ m * (27 / 32) ^ r := by
      field_simp
      ring
    linarith
  linarith

end Corruption

/-! ### Randomized lower bounds -/

section LowerBounds

variable [Fintype U] {m : ℕ}

/-- The arithmetic behind the lower bound: `(32 / 27) ^ 5 ≥ 2`, so
`13 * 32 ^ r ≤ 576 * 2 ^ c * 27 ^ r` forces `r / 5 < c + 6`. -/
private theorem le_of_mul_pow_le {r c : ℕ} (h : 13 * 32 ^ r ≤ 576 * 2 ^ c * 27 ^ r) :
    r ≤ 5 * c + 29 := by
  set q := r / 5
  set t := r % 5
  have hr : r = 5 * q + t := (Nat.div_add_mod r 5).symm
  have h1 : 2 ^ q * 27 ^ (5 * q) ≤ 32 ^ (5 * q) := by
    rw [pow_mul, pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (by norm_num) q
  have h2 : 27 ^ t ≤ 32 ^ t := Nat.pow_le_pow_left (by norm_num) t
  have h3 : 13 * 2 ^ q * 27 ^ r ≤ 576 * 2 ^ c * 27 ^ r :=
    calc 13 * 2 ^ q * 27 ^ r = 13 * (2 ^ q * 27 ^ (5 * q)) * 27 ^ t := by
          rw [hr, pow_add]
          ring
      _ ≤ 13 * 32 ^ (5 * q) * 32 ^ t := by gcongr
      _ = 13 * 32 ^ r := by
          rw [hr, pow_add]
          ring
      _ ≤ 576 * 2 ^ c * 27 ^ r := h
  have h4 : 13 * 2 ^ q ≤ 576 * 2 ^ c := Nat.le_of_mul_le_mul_right h3 (by positivity)
  have h5 : q < c + 6 := by
    by_contra hq
    have h6 : 2 ^ c * 2 ^ 6 ≤ 2 ^ q := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right two_pos (by omega)
    have : 0 < 2 ^ c := by positivity
    omega
  omega

/-- **Disjointness needs `Ω(m)` bits with public coins**, for subsets of `2 m + 1` points: a
public-coin protocol deciding whether two such subsets are disjoint with error `1 / 64` sends at
least `((m + 1) / 48 - 29) / 5` bits. -/
theorem PublicCoin.div_le_ecomplexityFun_disjoint (hU : Fintype.card U = 2 * m + 1) :
    (((m + 1) / 48 : ℕ) : ℕ∞) ≤
      5 * PublicCoin.ecomplexityFun (1 / 64) (fun x y : Finset U => decide (Disjoint x y)) +
        29 := by
  cases h : PublicCoin.ecomplexityFun (1 / 64) (fun x y : Finset U => decide (Disjoint x y))
    using ENat.recTopCoe with
  | top => simp
  | coe c =>
    set r := (m + 1) / 48
    have hr : 48 * r ≤ m + 1 := Nat.mul_div_le (m + 1) 48
    have hbound := (corrupted_disjointnessDist hU hr).mul_sub_le_of_ecomplexityFun_le
      (by norm_num) h.le
    rw [disjointnessDist_toOuterMeasure_disjoint] at hbound
    have hreal : (13 : ℝ) * 32 ^ r ≤ 576 * 2 ^ c * 27 ^ r := by
      have h32 : (0 : ℝ) < 32 ^ r := by positivity
      have hdiv : (2 : ℝ) ^ c * ((27 / 32) ^ r / 2) = 2 ^ c * 27 ^ r / (2 * 32 ^ r) := by
        rw [div_pow]
        ring
      rw [hdiv] at hbound
      have : (13 : ℝ) / 1152 ≤ 2 ^ c * 27 ^ r / (2 * 32 ^ r) := by linarith
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    have hnat : 13 * 32 ^ r ≤ 576 * 2 ^ c * 27 ^ r := by exact_mod_cast hreal
    have := le_of_mul_pow_le hnat
    exact_mod_cast this

/-- Disjointness of subsets of `Fin k` is disjointness of their indicators as bit strings of
length `n`, along an embedding of `Fin k` into `Fin n`. -/
private theorem disjointness_indicator {k n : ℕ} (e : Fin k ↪ Fin n) (x y : Finset (Fin k)) :
    disjointness (fun i => decide (i ∈ x.map e)) (fun i => decide (i ∈ y.map e)) =
      decide (Disjoint x y) := by
  unfold disjointness
  refine decide_eq_decide.mpr ?_
  rw [← disjoint_map e, disjoint_left]
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
  exact forall_congr' fun i => by tauto

end LowerBounds

/-- **Disjointness needs `Ω(n)` bits with public coins and small error** [Razborov1992],
[Kalyanasundaram and Schnitger][KalyanasundaramSchnitger1992]: a public-coin protocol deciding
whether two `n`-bit strings have disjoint supports with error `ε ≤ 1 / 64` sends at least
`(n - 2 ^ 12) / 2 ^ 9` bits. -/
theorem PublicCoin.le_mul_ecomplexityFun_disjointness_add_of_le {ε : ℝ} (hε : ε ≤ 1 / 64)
    (n : ℕ) :
    (n : ℕ∞) ≤ 2 ^ 9 * PublicCoin.ecomplexityFun ε
      (disjointness : BitString n → BitString n → Bool) + 2 ^ 12 := by
  have hanti : PublicCoin.ecomplexityFun (1 / 64)
      (disjointness : BitString n → BitString n → Bool) ≤
        PublicCoin.ecomplexityFun ε (disjointness : BitString n → BitString n → Bool) :=
    PublicCoin.ecomplexity_anti hε
  refine le_trans ?_ (add_le_add_left (mul_le_mul_right hanti _) _)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  set m := (n - 1) / 2
  have hmn : 2 * m + 1 ≤ n := by omega
  have h1 := PublicCoin.div_le_ecomplexityFun_disjoint (Fintype.card_fin (2 * m + 1))
  have h2 : PublicCoin.ecomplexityFun (1 / 64)
      (fun x y : Finset (Fin (2 * m + 1)) => decide (Disjoint x y)) ≤
        PublicCoin.ecomplexityFun (1 / 64) (disjointness : BitString n → BitString n → Bool) := by
    have := PublicCoin.ecomplexityFun_comap_le (ε := 1 / 64)
      (disjointness : BitString n → BitString n → Bool)
      (fun x : Finset (Fin (2 * m + 1)) => fun i => decide (i ∈ x.map (Fin.castLEEmb hmn)))
      (fun y : Finset (Fin (2 * m + 1)) => fun i => decide (i ∈ y.map (Fin.castLEEmb hmn)))
    simpa only [disjointness_indicator] using this
  cases h : PublicCoin.ecomplexityFun (1 / 64) (disjointness : BitString n → BitString n → Bool)
    using ENat.recTopCoe with
  | top => simp
  | coe c =>
    rw [h] at h2
    have h3 : (((m + 1) / 48 : ℕ) : ℕ∞) ≤ ((5 * c + 29 : ℕ) : ℕ∞) := by
      refine h1.trans ?_
      push_cast
      gcongr
    have h4 : (m + 1) / 48 ≤ 5 * c + 29 := by exact_mod_cast h3
    have : n ≤ 2 ^ 9 * c + 2 ^ 12 := by omega
    exact_mod_cast this

/-- **Disjointness needs `Ω(n)` bits with public coins** [Kalyanasundaram and
Schnitger][KalyanasundaramSchnitger1992], [Razborov1992]: a public-coin protocol deciding whether
two `n`-bit strings have disjoint supports with error `1 / 3` sends at least `(n - 2 ^ 12) / 2 ^ 16`
bits. Majority votes of `72` runs reduce the error to `(8 / 9) ^ 36 ≤ 1 / 64`
(`PublicCoin.ecomplexityFun_le_two_mul_mul_one_third`). -/
theorem PublicCoin.le_mul_ecomplexityFun_disjointness_add (n : ℕ) :
    (n : ℕ∞) ≤ 2 ^ 16 * PublicCoin.ecomplexityFun (1 / 3)
      (disjointness : BitString n → BitString n → Bool) + 2 ^ 12 := by
  have h1 := PublicCoin.le_mul_ecomplexityFun_disjointness_add_of_le (ε := (8 / 9) ^ 36)
    (by norm_num) n
  have h2 := PublicCoin.ecomplexityFun_le_two_mul_mul_one_third
    (f := (disjointness : BitString n → BitString n → Bool)) 36
  refine h1.trans ?_
  calc 2 ^ 9 * PublicCoin.ecomplexityFun ((8 / 9) ^ 36)
        (disjointness : BitString n → BitString n → Bool) + 2 ^ 12
      ≤ 2 ^ 9 * (2 * (36 : ℕ) * PublicCoin.ecomplexityFun (1 / 3)
        (disjointness : BitString n → BitString n → Bool)) + 2 ^ 12 := by gcongr
    _ ≤ 2 ^ 16 * PublicCoin.ecomplexityFun (1 / 3)
        (disjointness : BitString n → BitString n → Bool) + 2 ^ 12 := by
        rw [← mul_assoc]
        gcongr
        norm_num

/-- **Disjointness needs `Ω(n)` bits with private coins** [Kalyanasundaram and
Schnitger][KalyanasundaramSchnitger1992], [Razborov1992]: a private-coin protocol deciding whether
two `n`-bit strings have disjoint supports with error `1 / 3` sends at least `(n - 2 ^ 12) / 2 ^ 16`
bits. -/
theorem PrivateCoin.le_mul_ecomplexityFun_disjointness_add (n : ℕ) :
    (n : ℕ∞) ≤ 2 ^ 16 * PrivateCoin.ecomplexityFun (1 / 3)
      (disjointness : BitString n → BitString n → Bool) + 2 ^ 12 :=
  (PublicCoin.le_mul_ecomplexityFun_disjointness_add n).trans
    (by gcongr; exact PublicCoin.ecomplexityFun_le_privateCoin)

end Cslib.Communication
