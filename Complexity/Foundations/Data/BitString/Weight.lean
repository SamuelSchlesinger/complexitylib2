/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Parity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset

/-!
# Hamming weight and symmetric Boolean functions

The weight of a Boolean vector is its number of true coordinates (`BitString.weight`). The
threshold function `threshold n j` says that at least `j` of `n` bits are true, and majority
(`majority`, at least half) and strict majority (`strictMajority`, more than half) are threshold
functions. A Boolean function is *symmetric* when it depends only on the weight of its input
(`BooleanFunction.IsSymmetric`), and then it factors through the weight
(`BooleanFunction.IsSymmetric.exists_eq_comp_weight`).

## Main definitions

* `Cslib.BitString.weight`: the number of true coordinates.
* `Cslib.threshold`, `Cslib.majority`, `Cslib.strictMajority`: threshold functions.
* `Cslib.BooleanFunction.IsSymmetric`: Boolean functions depending only on the weight.

## Main results

* `Cslib.BitString.card_filter_weight_eq`: there are `n.choose r` strings of `n` bits of weight
  `r`.
* `Cslib.strictMajority_not`: strict majority of the negated bits is the negation of majority.
* `Cslib.isSymmetric_threshold`, `Cslib.isSymmetric_parity`: threshold functions and parity are
  symmetric.
-/

@[expose] public section

namespace Cslib

open Finset

namespace BitString

variable {ι : Type*} [Fintype ι]

/-- The Hamming weight of a Boolean vector: its number of true coordinates. -/
def weight (x : ι → Bool) : ℕ :=
  #{i | x i = true}

theorem weight_eq_sum_toNat (x : ι → Bool) : weight x = ∑ i, (x i).toNat := by
  rw [weight, card_filter]
  exact sum_congr rfl fun i _ => by cases x i <;> rfl

theorem weight_le (x : ι → Bool) : weight x ≤ Fintype.card ι :=
  card_filter_le _ _

/-- Complementary vectors have weights adding up to the number of coordinates. -/
theorem weight_not_add (x : ι → Bool) :
    weight (fun i => !x i) + weight x = Fintype.card ι := by
  rw [weight, weight, add_comm]
  simpa using card_filter_add_card_filter_not (s := univ) (fun i => x i = true)

theorem weight_not (x : ι → Bool) : weight (fun i => !x i) = Fintype.card ι - weight x := by
  have := weight_not_add x
  omega

@[simp] theorem weight_sum_elim {κ : Type*} [Fintype κ] (x : ι → Bool) (y : κ → Bool) :
    weight (Sum.elim x y) = weight x + weight y := by
  simp only [weight_eq_sum_toNat, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

/-- Setting a false coordinate to true adds one to the weight. -/
theorem weight_update_true [DecidableEq ι] {x : ι → Bool} {i : ι} (hi : x i = false) :
    weight (Function.update x i true) = weight x + 1 := by
  have he : univ.filter (fun j => Function.update x i true j = true) =
      insert i (univ.filter fun j => x j = true) := by
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [weight, he, card_insert_of_notMem (by simp [hi]), weight]

/-- Setting a true coordinate to false takes one from the weight. -/
theorem weight_update_false [DecidableEq ι] {x : ι → Bool} {i : ι} (hi : x i = true) :
    weight (Function.update x i false) + 1 = weight x := by
  have he : univ.filter (fun j => Function.update x i false j = true) =
      (univ.filter fun j => x j = true).erase i := by
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [weight, he, weight]
  exact card_erase_add_one (by simp [hi])

/-- The strings of `n` bits of weight `r` number `n.choose r`. -/
theorem card_filter_weight_eq (n r : ℕ) :
    #{x : BitString n | weight x = r} = n.choose r := by
  refine (?_ : #{x : BitString n | weight x = r} = #(powersetCard r (univ : Finset (Fin n)))).trans
    (by rw [card_powersetCard, card_univ, Fintype.card_fin])
  refine card_nbij' (fun x => ({i | x i = true} : Finset (Fin n))) (fun s i => decide (i ∈ s))
    (fun x hx => ?_) (fun s hs => ?_) (fun x _ => ?_) (fun s _ => ?_)
  · exact mem_powersetCard.2 ⟨subset_univ _, (mem_filter.1 hx).2⟩
  · refine mem_filter.2 ⟨mem_univ _, ?_⟩
    rw [← (mem_powersetCard.1 hs).2, weight]
    congr 1
    ext i
    simp
  · funext i
    simp
  · ext i
    simp

end BitString

open BitString

variable {n : ℕ}

/-- The threshold function `Th^n_j` on `n` bits: whether at least `j` of them are true. -/
def threshold (n j : ℕ) : BooleanFunction n :=
  fun x => decide (j ≤ weight x)

/-- The majority function on `n` bits: whether at least half of them are true, that is, the
threshold function `Th^n_⌈n/2⌉`. -/
def majority (n : ℕ) : BooleanFunction n :=
  threshold n ((n + 1) / 2)

/-- The strict majority function on `n` bits: whether more than half of them are true, so that a
tie is false. It is the threshold function `Th^n_{⌊n/2⌋+1}`. -/
def strictMajority (n : ℕ) : BooleanFunction n :=
  threshold n (n / 2 + 1)

theorem threshold_apply (j : ℕ) (x : BitString n) :
    threshold n j x = decide (j ≤ #{i | x i = true}) :=
  rfl

theorem threshold_eq_true_iff {j : ℕ} {x : BitString n} :
    threshold n j x = true ↔ j ≤ weight x := by
  simp [threshold]

theorem majority_eq_true_iff {x : BitString n} :
    majority n x = true ↔ (n + 1) / 2 ≤ weight x :=
  threshold_eq_true_iff

theorem strictMajority_eq_true_iff {x : BitString n} :
    strictMajority n x = true ↔ n / 2 < weight x :=
  threshold_eq_true_iff

theorem strictMajority_eq_false_iff {x : BitString n} :
    strictMajority n x = false ↔ weight x ≤ n / 2 := by
  rw [← Bool.not_eq_true, strictMajority_eq_true_iff, not_lt]

/-- Strict majority of the negated bits is the negation of majority: fewer than half of the bits
are true exactly when not at least half of them are. -/
theorem strictMajority_not (x : BitString n) :
    strictMajority n (fun i => !x i) = !majority n x := by
  have h := weight_not x
  have hle := weight_le x
  simp only [Fintype.card_fin] at h hle
  rw [Bool.eq_iff_iff, strictMajority_eq_true_iff, Bool.not_eq_true', ← Bool.not_eq_true,
    majority_eq_true_iff, h]
  omega

namespace BooleanFunction

/-- A Boolean function is *symmetric* when it depends only on the weight of its input. -/
def IsSymmetric (f : BooleanFunction n) : Prop :=
  ∀ x y, weight x = weight y → f x = f y

/-- A symmetric function factors through the weight. -/
theorem IsSymmetric.exists_eq_comp_weight {f : BooleanFunction n} (hf : f.IsSymmetric) :
    ∃ a : ℕ → Bool, ∀ x, a (weight x) = f x := by
  classical
  refine ⟨fun w => decide (∃ x, weight x = w ∧ f x = true), fun x => Bool.eq_iff_iff.2 ?_⟩
  simp only [decide_eq_true_eq]
  exact ⟨fun ⟨y, hy, hfy⟩ => hf y x hy ▸ hfy, fun hx => ⟨x, rfl, hx⟩⟩

end BooleanFunction

/-- Threshold functions are symmetric. -/
theorem isSymmetric_threshold (j : ℕ) : (threshold n j).IsSymmetric := fun x y h => by
  simp only [threshold, h]

theorem isSymmetric_majority : (majority n).IsSymmetric :=
  isSymmetric_threshold _

theorem isSymmetric_strictMajority : (strictMajority n).IsSymmetric :=
  isSymmetric_threshold _

/-- Parity is symmetric. -/
theorem isSymmetric_parity : (parity n).IsSymmetric := fun x y h => by
  simp only [weight] at h
  simp only [parity, parityOn, h]

end Cslib
