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
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Random subsets meet a fixed set in about its expected size

For a set `U` of `u` elements of an `n`-element set `s` and a uniformly random `ℓ`-subset `J` of
`s`, the size of `U ∩ J` has mean `μ = u ℓ / n` and variance at most `μ`
(a hypergeometric distribution). By Chebyshev's inequality it is below `μ / 2` with probability
at most `4 / μ`, so at most half of the `ℓ`-subsets meet `U` in fewer than `μ / 2` elements once
`μ ≥ 8` (`two_mul_card_filter_card_inter_lt_le`). The moments are computed by double counting:
the `ℓ`-subsets containing a fixed `t`-subset `A` are the `(ℓ - t)`-subsets of `s \ A`
(`card_filter_subset_powersetCard`).

## Main results

* `Finset.card_filter_subset_powersetCard`: the subsets of size `ℓ` containing a given set.
* `Finset.two_mul_card_filter_card_inter_lt_le`: most `ℓ`-subsets meet `U` in at least
  half the expected number of elements.
-/

@[expose] public section

namespace Finset

variable {α : Type*} [DecidableEq α]

/-- The `ℓ`-subsets of `s` containing `A ⊆ s` are the `(ℓ - #A)`-subsets of `s \ A`, with `A`
added. -/
theorem card_filter_subset_powersetCard {s A : Finset α} (hA : A ⊆ s) {ℓ : ℕ} (hℓ : #A ≤ ℓ) :
    #{J ∈ s.powersetCard ℓ | A ⊆ J} = (#s - #A).choose (ℓ - #A) := by
  rw [← card_sdiff_of_subset hA, ← card_powersetCard]
  refine card_nbij' (· \ A) (· ∪ A) (fun J hJ => ?_) (fun K hK => ?_) (fun J hJ => ?_)
    (fun K hK => ?_)
  · obtain ⟨hJ, hAJ⟩ := mem_filter.1 hJ
    obtain ⟨hJs, hJc⟩ := mem_powersetCard.1 hJ
    exact mem_powersetCard.2 ⟨sdiff_subset_sdiff hJs le_rfl, by
      rw [card_sdiff_of_subset hAJ, hJc]⟩
  · obtain ⟨hKs, hKc⟩ := mem_powersetCard.1 hK
    have hdisj : Disjoint K A := disjoint_of_subset_left hKs disjoint_sdiff_self_left
    refine mem_filter.2 ⟨mem_powersetCard.2 ⟨union_subset (hKs.trans sdiff_subset) hA, ?_⟩,
      subset_union_right⟩
    rw [card_union_of_disjoint hdisj, hKc]
    omega
  · exact sdiff_union_of_subset (mem_filter.1 hJ).2
  · exact union_sdiff_cancel_right (disjoint_of_subset_left (mem_powersetCard.1 hK).1
      disjoint_sdiff_self_left)

variable {s U : Finset α} {ℓ : ℕ}

/-- `#(U ∩ J)` counts the elements of `U` in `J`. -/
private theorem card_inter_eq_sum (U J : Finset α) :
    #(U ∩ J) = ∑ i ∈ U, if i ∈ J then 1 else 0 := by
  rw [sum_boole, filter_mem_eq_inter, Nat.cast_id]

/-- The `ℓ`-subsets of `s` containing `i ∈ s`. -/
private theorem card_filter_mem_powersetCard (hi : i ∈ s) (hℓ : 1 ≤ ℓ) :
    #{J ∈ s.powersetCard ℓ | i ∈ J} = (#s - 1).choose (ℓ - 1) := by
  simpa using card_filter_subset_powersetCard (A := {i}) (singleton_subset_iff.2 hi)
    (by simpa using hℓ)

/-- The `ℓ`-subsets of `s` containing distinct `i, j ∈ s`. -/
private theorem card_filter_mem_mem_powersetCard {i j : α} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (hℓ : 2 ≤ ℓ) : #{J ∈ s.powersetCard ℓ | i ∈ J ∧ j ∈ J} = (#s - 2).choose (ℓ - 2) := by
  have h := card_filter_subset_powersetCard (A := {i, j}) (ℓ := ℓ) (insert_subset hi
    (singleton_subset_iff.2 hj)) (by rw [card_pair hij]; exact hℓ)
  rw [card_pair hij] at h
  rw [← h]
  congr 1
  exact filter_congr fun J _ => by simp [insert_subset_iff]

/-- **The first moment**: summed over the `ℓ`-subsets `J`, `#(U ∩ J)` counts every element of `U`
once for each `ℓ`-subset containing it. -/
theorem sum_card_inter_powersetCard (hU : U ⊆ s) (hℓ : 1 ≤ ℓ) :
    ∑ J ∈ s.powersetCard ℓ, #(U ∩ J) = #U * (#s - 1).choose (ℓ - 1) := by
  simp only [card_inter_eq_sum]
  rw [sum_comm, sum_congr rfl fun i hi => by rw [sum_boole, Nat.cast_id,
    card_filter_mem_powersetCard (hU hi) hℓ], sum_const, smul_eq_mul]

/-- **The second moment** of `#(U ∩ J)` over the `ℓ`-subsets `J`. -/
theorem sum_card_inter_sq_powersetCard (hU : U ⊆ s) (hℓ : 2 ≤ ℓ) :
    ∑ J ∈ s.powersetCard ℓ, #(U ∩ J) ^ 2 =
      #U * (#s - 1).choose (ℓ - 1) + #U * (#U - 1) * (#s - 2).choose (ℓ - 2) := by
  have hsq (J : Finset α) : #(U ∩ J) ^ 2 =
      ∑ i ∈ U, ∑ j ∈ U, if i ∈ J ∧ j ∈ J then 1 else 0 := by
    rw [sq, card_inter_eq_sum, sum_mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by
      by_cases hi : i ∈ J <;> by_cases hj : j ∈ J <;> simp [hi, hj]
  simp only [hsq]
  rw [sum_comm]
  calc ∑ i ∈ U, ∑ J ∈ s.powersetCard ℓ, ∑ j ∈ U, (if i ∈ J ∧ j ∈ J then 1 else 0)
      = ∑ i ∈ U, (#{J ∈ s.powersetCard ℓ | i ∈ J} +
          ∑ j ∈ U.erase i, #{J ∈ s.powersetCard ℓ | i ∈ J ∧ j ∈ J}) := by
        refine sum_congr rfl fun i hi => ?_
        rw [sum_comm, ← add_sum_erase _ _ hi]
        simp only [and_self, sum_boole, Nat.cast_id]
    _ = ∑ i ∈ U, ((#s - 1).choose (ℓ - 1) + (#U - 1) * (#s - 2).choose (ℓ - 2)) := by
        refine sum_congr rfl fun i hi => ?_
        rw [card_filter_mem_powersetCard (hU hi) (by omega),
          sum_congr rfl fun j hj => card_filter_mem_mem_powersetCard (hU hi)
            (hU (mem_of_mem_erase hj)) (ne_of_mem_erase hj).symm hℓ,
          sum_const, card_erase_of_mem hi, smul_eq_mul]
    _ = _ := by rw [sum_const, smul_eq_mul]; ring

/-- **Most `ℓ`-subsets meet `U` in at least half the expected number of elements**: if the
expected size `μ = #U ℓ / #s` of `U ∩ J` is at least `8`, at most half of the `ℓ`-subsets `J` of
`s` meet `U` in fewer than `m ≤ μ / 2` elements. -/
theorem two_mul_card_filter_card_inter_lt_le (hU : U ⊆ s) (hℓs : ℓ ≤ #s) (hs : 0 < #s)
    (hμ : 8 * #s ≤ #U * ℓ) {m : ℕ} (hm : 2 * m * #s ≤ #U * ℓ) :
    2 * #{J ∈ s.powersetCard ℓ | #(U ∩ J) < m} ≤ (#s).choose ℓ := by
  have hun : #U ≤ #s := card_le_card hU
  have hℓ8 : 8 ≤ ℓ := by nlinarith
  -- the binomial identities `n C(n-1, ℓ-1) = ℓ C(n, ℓ)` and `(n-1) C(n-2, ℓ-2) = (ℓ-1) C(n-1, ℓ-1)`
  have c₁ := Nat.add_one_mul_choose_eq (#s - 1) (ℓ - 1)
  have c₂ := Nat.add_one_mul_choose_eq (#s - 2) (ℓ - 2)
  rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)] at c₁
  rw [show #s - 2 + 1 = #s - 1 by omega, show ℓ - 2 + 1 = ℓ - 1 by omega] at c₂
  have h₁ := sum_card_inter_powersetCard hU (show 1 ≤ ℓ by omega)
  have h₂ := sum_card_inter_sq_powersetCard hU (show 2 ≤ ℓ by omega)
  have hu1 : 1 ≤ #U := by nlinarith
  -- the facts in the reals
  have hc₁ : ((#s : ℕ) : ℝ) * ((#s - 1).choose (ℓ - 1) : ℕ) = ((#s).choose ℓ : ℕ) * (ℓ : ℝ) := by
    exact_mod_cast c₁
  have hc₂ : ((#s : ℝ) - 1) * ((#s - 2).choose (ℓ - 2) : ℕ) =
      ((#s - 1).choose (ℓ - 1) : ℕ) * ((ℓ : ℝ) - 1) := by
    have h' : ((#s - 1 : ℕ) : ℝ) * ((#s - 2).choose (ℓ - 2) : ℕ) =
        ((#s - 1).choose (ℓ - 1) : ℕ) * ((ℓ - 1 : ℕ) : ℝ) := by exact_mod_cast c₂
    rwa [Nat.cast_sub (show 1 ≤ #s by omega), Nat.cast_sub (show 1 ≤ ℓ by omega),
      Nat.cast_one] at h'
  have hS₁ : ∑ J ∈ s.powersetCard ℓ, ((#(U ∩ J) : ℕ) : ℝ) =
      (#U : ℝ) * ((#s - 1).choose (ℓ - 1) : ℕ) := by exact_mod_cast h₁
  have hS₂ : ∑ J ∈ s.powersetCard ℓ, ((#(U ∩ J) : ℕ) : ℝ) ^ 2 =
      (#U : ℝ) * ((#s - 1).choose (ℓ - 1) : ℕ) +
        (#U : ℝ) * ((#U : ℝ) - 1) * ((#s - 2).choose (ℓ - 2) : ℕ) := by
    have h' : ∑ J ∈ s.powersetCard ℓ, ((#(U ∩ J) : ℕ) : ℝ) ^ 2 =
        (#U : ℝ) * ((#s - 1).choose (ℓ - 1) : ℕ) +
          (#U : ℝ) * ((#U - 1 : ℕ) : ℝ) * ((#s - 2).choose (ℓ - 2) : ℕ) := by exact_mod_cast h₂
    rwa [Nat.cast_sub hu1, Nat.cast_one] at h'
  have hN : ((#(s.powersetCard ℓ) : ℕ) : ℝ) = ((#s).choose ℓ : ℕ) := by rw [card_powersetCard]
  have hμR : (8 : ℝ) * #s ≤ (#U : ℝ) * ℓ := by exact_mod_cast hμ
  have hmR : 2 * (m : ℝ) * #s ≤ (#U : ℝ) * ℓ := by exact_mod_cast hm
  have hunR : (#U : ℝ) ≤ #s := by exact_mod_cast hun
  have hℓsR : (ℓ : ℝ) ≤ #s := by exact_mod_cast hℓs
  have hℓ1R : (1 : ℝ) ≤ ℓ := by exact_mod_cast (show 1 ≤ ℓ by omega)
  have hu1R : (1 : ℝ) ≤ #U := by exact_mod_cast hu1
  have hbadX : ∀ J ∈ {J ∈ s.powersetCard ℓ | #(U ∩ J) < m}, ((#(U ∩ J) : ℕ) : ℝ) + 1 ≤ m :=
    fun J hJ => by exact_mod_cast (mem_filter.1 hJ).2
  -- abbreviations: `c = #s`, `a = #U`, `b = ℓ`, `M = C(c, b)`
  set c : ℝ := ((#s : ℕ) : ℝ)
  set a : ℝ := ((#U : ℕ) : ℝ)
  set b : ℝ := ((ℓ : ℕ) : ℝ)
  set M : ℝ := (((#s).choose ℓ : ℕ) : ℝ)
  set A : ℝ := (((#s - 1).choose (ℓ - 1) : ℕ) : ℝ)
  set B : ℝ := (((#s - 2).choose (ℓ - 2) : ℕ) : ℝ)
  set K : ℝ := ((#{J ∈ s.powersetCard ℓ | #(U ∩ J) < m} : ℕ) : ℝ)
  have hc : (8 : ℝ) ≤ c := by nlinarith
  have hM : 0 ≤ M := by positivity
  have hK : 0 ≤ K := by positivity
  -- the sum of `(c X - a b)²` over all `ℓ`-subsets is at most `c a b M`
  have hsum : ∑ J ∈ s.powersetCard ℓ, (c * ((#(U ∩ J) : ℕ) : ℝ) - a * b) ^ 2 ≤ c * a * b * M := by
    have hpt (J : Finset α) : (c * ((#(U ∩ J) : ℕ) : ℝ) - a * b) ^ 2 =
        c ^ 2 * ((#(U ∩ J) : ℕ) : ℝ) ^ 2 - (2 * c * a * b) * ((#(U ∩ J) : ℕ) : ℝ) +
          a ^ 2 * b ^ 2 := by ring
    simp only [hpt, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul, hS₁, hS₂,
      hN]
    -- `c A = b M` and `c (c - 1) B = (b - 1) b M`
    have hB : c * (c - 1) * B = (b - 1) * b * M := by
      calc c * (c - 1) * B = c * ((c - 1) * B) := by ring
        _ = c * (A * (b - 1)) := by rw [hc₂]
        _ = (c * A) * (b - 1) := by ring
        _ = (b - 1) * b * M := by rw [hc₁]; ring
    have hE : c ^ 2 * (a * A + a * (a - 1) * B) - 2 * c * a * b * (a * A) + a ^ 2 * (M * b ^ 2) =
        c * a * b * M + a * (a - 1) * (c * (c * B)) - a ^ 2 * b ^ 2 * M := by
      calc _ = c * a * (c * A) + a * (a - 1) * (c * (c * B)) - 2 * a ^ 2 * b * (c * A) +
            a ^ 2 * b ^ 2 * M := by ring
        _ = _ := by rw [hc₁]; ring
    rw [hE]
    -- after multiplying by `c - 1 > 0`, the claim is `c (a - 1) (b - 1) ≤ (c - 1) a b`
    have hc1 : 0 < c - 1 := by linarith
    refine le_of_mul_le_mul_left ?_ hc1
    have key : c * (a - 1) * (b - 1) ≤ (c - 1) * a * b := by nlinarith
    have hkey := mul_le_mul_of_nonneg_right key (show 0 ≤ a * b * M by positivity)
    calc (c - 1) * (c * a * b * M + a * (a - 1) * (c * (c * B)) - a ^ 2 * b ^ 2 * M)
        = (c - 1) * (c * a * b * M) + a * (a - 1) * c * (c * (c - 1) * B) -
            (c - 1) * (a ^ 2 * b ^ 2 * M) := by ring
      _ = (c - 1) * (c * a * b * M) + a * (a - 1) * c * ((b - 1) * b * M) -
            (c - 1) * (a ^ 2 * b ^ 2 * M) := by rw [hB]
      _ ≤ (c - 1) * (c * a * b * M) := by nlinarith [hkey]
  -- each bad subset contributes at least `(a b / 2)²`
  have hbad : K * (a * b / 2) ^ 2 ≤
      ∑ J ∈ s.powersetCard ℓ, (c * ((#(U ∩ J) : ℕ) : ℝ) - a * b) ^ 2 := by
    rw [show K * (a * b / 2) ^ 2 =
      ∑ J ∈ {J ∈ s.powersetCard ℓ | #(U ∩ J) < m}, (a * b / 2) ^ 2 by
        rw [sum_const, nsmul_eq_mul]]
    refine (sum_le_sum fun J hJ => ?_).trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun _ _ _ => sq_nonneg _)
    have hXJ := hbadX J hJ
    have hpos : 0 ≤ a * b / 2 := by positivity
    have : a * b / 2 ≤ a * b - c * ((#(U ∩ J) : ℕ) : ℝ) := by nlinarith
    nlinarith
  -- conclude: `K (a b)² / 4 ≤ c a b M` and `a b ≥ 8 c`
  have h := hbad.trans hsum
  have hab0 : 0 < a * b := by nlinarith
  have hK' : K * (a * b) ≤ 4 * c * M := by
    have h' : K * (a * b) * (a * b) ≤ 4 * c * M * (a * b) := by nlinarith
    exact le_of_mul_le_mul_right h' hab0
  have hfinal : 2 * K ≤ M := by nlinarith
  have : ((2 * #{J ∈ s.powersetCard ℓ | #(U ∩ J) < m} : ℕ) : ℝ) ≤ ((#s).choose ℓ : ℕ) := by
    push_cast
    exact hfinal
  exact_mod_cast this

end Finset
