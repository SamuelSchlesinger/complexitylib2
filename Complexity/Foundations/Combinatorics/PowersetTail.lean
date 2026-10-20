/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Few subsets meet a fixed set in few points

A uniformly random subset `x` of a finite set `S` meets a fixed `K ⊆ S` in about `#K / 2` points.
Weighting each subset `x` by `2 ^ #(K \ x)` gives total weight `3 ^ #K 2 ^ #(S \ K)`
(`Finset.sum_powerset_two_pow_card_sdiff`), and every subset meeting `K` in at most `j` points has
weight at least `2 ^ (#K - j)`. So at most a `(3 / 4) ^ #K 2 ^ j` fraction of the subsets of `S`
meet `K` in at most `j` points (`Finset.two_pow_mul_card_filter_card_inter_le`); for instance at
most a `(27 / 32) ^ r / 2` fraction meet a set of `3 r` points in fewer than `r` points. Weighting
by `2 ^ #x` instead bounds the subsets missing at most `j` points of `S`
(`Finset.two_pow_mul_card_filter_card_sdiff_le`). This is the exponential-moment (Chernoff) bound
with the single weight `2` [Alon and Spencer, Appendix A][AlonSpencer2016], stated by counting; for
the subsets of `K` itself, Hoeffding's bound for fair coins
(`Cslib.BitString.card_filter_le_card_filter_sub_half_le`) is sharper.

A family of sets for which many points of `S` are avoided by most of its members inside `S` is
therefore small (`Finset.four_mul_sum_card_filter_notMem_le`): by Markov's inequality, many of its
members meet the avoided points in few points, or miss few points of `S`. This is the counting
step of Razborov's corruption bound for disjointness [Razborov1992].

## Main results

* `Finset.two_pow_mul_card_filter_card_inter_le`: few subsets of `S` meet `K` in few points.
* `Finset.two_pow_mul_card_filter_card_sdiff_le`: few subsets of `S` miss few of its points.
* `Finset.four_mul_sum_card_filter_notMem_le`: families avoiding many points are small.

## References

* [N. Alon and J. H. Spencer, *The Probabilistic Method*][AlonSpencer2016]
* [A. A. Razborov, *On the distributional complexity of disjointness*][Razborov1992]
-/

@[expose] public section

namespace Finset

variable {U : Type*} [DecidableEq U]

/-- Weighting each subset `x` of `S` by `2 ^ #(K \ x)` gives total weight `3 ^ #K 2 ^ #(S \ K)`. -/
theorem sum_powerset_two_pow_card_sdiff {K S : Finset U} (hKS : K ⊆ S) :
    ∑ x ∈ S.powerset, 2 ^ #(K \ x) = 3 ^ #K * 2 ^ (#S - #K) := by
  have h := prod_add (fun _ => (1 : ℕ)) (fun i => if i ∈ K then 2 else 1) S
  simp only [prod_const_one, one_mul, prod_ite_mem] at h
  have hl : ∏ i ∈ S, (1 + if i ∈ K then 2 else 1) = 3 ^ #K * 2 ^ (#S - #K) := by
    have : ∀ i ∈ S, (1 + if i ∈ K then 2 else 1) = if i ∈ K then 3 else 2 := by
      intro i _
      split_ifs <;> rfl
    have hK : S.filter (· ∈ K) = K := by
      rw [filter_mem_eq_inter, inter_eq_right.mpr hKS]
    have hK' : S.filter (· ∉ K) = S \ K := by
      ext i
      simp only [mem_filter, mem_sdiff]
    rw [prod_congr rfl this, prod_ite, prod_const, prod_const, hK, hK',
      card_sdiff_of_subset hKS]
  rw [← hl, h]
  refine sum_congr rfl fun t _ => ?_
  rw [prod_const]
  congr 2
  ext i
  have := @hKS i
  simp only [mem_inter, mem_sdiff]
  tauto

/-- Few subsets of `S` meet `K ⊆ S` in at most `j` points: `2 ^ (#K - j)` times their number is at
most `3 ^ #K 2 ^ #(S \ K)`. -/
theorem two_pow_mul_card_filter_card_inter_le {K S : Finset U} (hKS : K ⊆ S) (j : ℕ) :
    2 ^ (#K - j) * #{x ∈ S.powerset | #(K ∩ x) ≤ j} ≤ 3 ^ #K * 2 ^ (#S - #K) := by
  rw [← sum_powerset_two_pow_card_sdiff hKS, mul_comm, ← smul_eq_mul]
  refine (card_nsmul_le_sum _ _ _ fun x hx => ?_).trans
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.zero_le _)
  refine Nat.pow_le_pow_right (Nat.succ_pos 1) ?_
  have h := card_sdiff_add_card_inter K x
  have := (mem_filter.mp hx).2
  omega

/-- Few subsets of `S` miss at most `j` of its points: `2 ^ (#S - j)` times their number is at
most `3 ^ #S`. -/
theorem two_pow_mul_card_filter_card_sdiff_le (S : Finset U) (j : ℕ) :
    2 ^ (#S - j) * #{x ∈ S.powerset | #(S \ x) ≤ j} ≤ 3 ^ #S := by
  have h := sum_pow_mul_eq_add_pow (2 : ℕ) 1 S
  simp only [one_pow, mul_one] at h
  rw [show (3 : ℕ) = 2 + 1 from rfl, ← h, mul_comm, ← smul_eq_mul]
  refine (card_nsmul_le_sum _ _ _ fun x hx => ?_).trans
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.zero_le _)
  refine Nat.pow_le_pow_right (Nat.succ_pos 1) ?_
  obtain ⟨hx, hj⟩ := mem_filter.mp hx
  have := card_sdiff_add_card_eq_card (mem_powerset.mp hx)
  omega

/-! ### Families of sets that avoid many points -/

/-- **A family of sets that avoid many points is small.** Let `A` be a family of sets and `S` a
finite set, and call a point `i ∈ S` *bad* if the members of `A` inside `S` containing `i` are
fewer than a third of those avoiding it. Then the pairs of a member of `A` inside `S` and a bad
point it avoids are at most a quarter of the pairs of a member inside `S` and a point of `S` it
avoids, up to `2 ^ #S (8 #S (27 / 32) ^ r + (j + 1) 2 ^ j (3 / 4) ^ #S)`, which is a small
fraction of `#S 2 ^ #S` when `#S ≥ 48 r` and `j = 12 r`. If at least `3 r` points are bad, at
least a quarter of the members of `A` inside `S` meet a set `K` of `3 r` bad points in fewer than
`r` points, by Markov's inequality, and few subsets of `S` do
(`two_pow_mul_card_filter_card_inter_le`). Otherwise, the bad points are fewer than `(j + 1) / 4`
and most members inside `S` avoid more than `j` points, unless few subsets of `S` miss at most `j`
points (`two_pow_mul_card_filter_card_sdiff_le`). This is the key counting step of the
corruption bound for disjointness (`Cslib.Communication.Disjointness.corrupted_hardDist`)
[Razborov1992]. -/
theorem four_mul_sum_card_filter_notMem_le (A : Finset (Finset U)) (S : Finset U) {r j : ℕ}
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
        rw [show ∑ i ∈ K, #{x ∈ AS | i ∈ x} = ∑ x ∈ AS, #{i ∈ K | i ∈ x} from
          sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _]
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
      rw [show ∑ i ∈ S, #{x ∈ AS | i ∉ x} = ∑ x ∈ AS, #{i ∈ S | i ∉ x} from
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _]
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

@[deprecated (since := "2026-10-19")]
alias _root_.Cslib.Communication.four_mul_sum_card_filter_le := four_mul_sum_card_filter_notMem_le

end Finset
