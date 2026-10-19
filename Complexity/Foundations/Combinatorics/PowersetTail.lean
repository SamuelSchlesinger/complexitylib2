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
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Few subsets meet a fixed set in few points

A uniformly random subset `x` of a finite set `S` meets a fixed `K ⊆ S` in about `#K / 2` points.
Weighting each subset `x` by `2 ^ #(K \ x)` gives total weight `3 ^ #K 2 ^ #(S \ K)`
(`Finset.sum_powerset_two_pow_card_sdiff`), and every subset meeting `K` in at most `j` points has
weight at least `2 ^ (#K - j)`. So at most a `(3 / 4) ^ #K 2 ^ j` fraction of the subsets of `S`
meet `K` in at most `j` points (`Finset.two_pow_mul_card_filter_card_inter_le`); for instance at
most a `(27 / 32) ^ r / 2` fraction meet a set of `3 r` points in fewer than `r` points. Weighting
by `2 ^ #x` instead bounds the subsets missing at most `j` points of `S`
(`Finset.two_pow_mul_card_filter_card_sdiff_le`).

## Main results

* `Finset.two_pow_mul_card_filter_card_inter_le`: few subsets of `S` meet `K` in few points.
* `Finset.two_pow_mul_card_filter_card_sdiff_le`: few subsets of `S` miss few of its points.
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

end Finset
