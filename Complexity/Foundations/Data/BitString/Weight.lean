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
public import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset

/-!
# Hamming weight and symmetric Boolean functions

The weight of a Boolean vector is its number of true coordinates (`BitString.weight`), Mathlib's
Hamming norm with `false` as `0` (`BitString.weight_eq_hammingNorm`), so the Hamming distance of two
bit strings is the weight of their sum (`BitString.hammingDist_eq_weight_add`)
[MacWilliams and Sloane, Chapter 1][MacWilliamsSloane1977]. The threshold function
`threshold n j` says that at least `j` of `n` bits are true, and majority (`majority`, at least
half) and strict majority (`strictMajority`, more than half) are threshold functions. A Boolean
function is *symmetric* when it depends only on the weight of its input
(`BooleanFunction.IsSymmetric`), and then it factors through the weight
(`BooleanFunction.IsSymmetric.exists_eq_comp_weight`) [Jukna, Chapter 1][Jukna2012].

## Main definitions

* `Cslib.BitString.weight`: the number of true coordinates, and `Cslib.BitString.weightLayer` the
  strings of a given weight.
* `Cslib.threshold`, `Cslib.majority`, `Cslib.strictMajority`: threshold functions.
* `Cslib.BooleanFunction.IsSymmetric`: Boolean functions depending only on the weight.

## Main results

* `Cslib.BitString.weight_eq_hammingNorm`, `Cslib.BitString.hammingDist_eq_weight_add`: the
  weight is the Hamming norm.
* `Cslib.BitString.card_weightLayer`: there are `n.choose k` strings of `n` bits of weight `k`.
* `Cslib.strictMajority_not`: strict majority of the negated bits is the negation of majority.
* `Cslib.isSymmetric_threshold`, `Cslib.isSymmetric_parity`: threshold functions and parity are
  symmetric.

## References

* [F. J. MacWilliams, N. J. A. Sloane, *The Theory of Error-Correcting Codes*]
  [MacWilliamsSloane1977]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
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

/-- The weight is Mathlib's Hamming norm, the bit `false` being `0`. -/
theorem weight_eq_hammingNorm (x : ι → Bool) : weight x = hammingNorm x := by
  simp only [weight, hammingNorm, Bool.zero_eq_false, ne_eq, Bool.not_eq_false]

/-- The Hamming distance between two bit strings is the weight of their sum. -/
theorem hammingDist_eq_weight_add (x y : ι → Bool) : hammingDist x y = weight (x + y) := by
  rw [hammingDist_eq_hammingNorm, weight_eq_hammingNorm]
  exact congrArg hammingNorm (funext fun i => BooleanRing.sub_eq_add (x i) (y i))

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
  have he : ({j | Function.update x i true j = true} : Finset ι) =
      insert i ({j | x j = true} : Finset ι) := by
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [weight, he, card_insert_of_notMem (by simp [hi]), weight]

/-- Setting a true coordinate to false takes one from the weight. -/
theorem weight_update_false [DecidableEq ι] {x : ι → Bool} {i : ι} (hi : x i = true) :
    weight (Function.update x i false) + 1 = weight x := by
  have he : ({j | Function.update x i false j = true} : Finset ι) =
      ({j | x j = true} : Finset ι).erase i := by
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [weight, he, weight]
  exact card_erase_add_one (by simp [hi])

/-- The words `ι → Bool` of weight `r` number `|ι|.choose r`: they are the indicators of the
`r`-element sets of coordinates. -/
theorem card_filter_weight_eq [DecidableEq ι] (r : ℕ) :
    #{x : ι → Bool | weight x = r} = (Fintype.card ι).choose r := by
  refine (?_ : #{x : ι → Bool | weight x = r} = #(powersetCard r (univ : Finset ι))).trans
    (by rw [card_powersetCard, card_univ])
  refine card_nbij' (fun x => ({i | x i = true} : Finset ι)) (fun s i => decide (i ∈ s))
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

/-- The weight of `x` as a number of true coordinates. -/
theorem weight_eq_card_subtype (x : ι → Bool) : weight x = Fintype.card {i // x i = true} :=
  (Fintype.card_subtype _).symm

/-- The *layer* of weight `k` of the cube: the strings of `n` bits with `k` true bits. -/
def weightLayer (n k : ℕ) : Finset (BitString n) :=
  {x | weight x = k}

@[simp] theorem mem_weightLayer {n k : ℕ} {x : BitString n} : x ∈ weightLayer n k ↔ weight x = k :=
  by simp [weightLayer]

/-- The layer of weight `k` has `n.choose k` strings. -/
theorem card_weightLayer (n k : ℕ) : #(weightLayer n k) = n.choose k := by
  rw [weightLayer, card_filter_weight_eq, Fintype.card_fin]

theorem weightLayer_nonempty {n k : ℕ} (hk : k ≤ n) : (weightLayer n k).Nonempty :=
  card_pos.1 (by rw [card_weightLayer]; exact Nat.choose_pos hk)

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

theorem threshold_apply (j : ℕ) (x : BitString n) : threshold n j x = decide (j ≤ weight x) :=
  rfl

theorem threshold_eq_true_iff {j : ℕ} {x : BitString n} :
    threshold n j x = true ↔ j ≤ weight x := by
  simp [threshold]

/-- With cutoff `0`, the threshold function is the constant `true`. -/
@[simp] theorem threshold_zero_right (x : BitString n) : threshold n 0 x = true :=
  threshold_eq_true_iff.2 (Nat.zero_le _)

/-- With a cutoff above `n`, the threshold function is the constant `false`. -/
theorem threshold_eq_false_of_lt {j : ℕ} (h : n < j) (x : BitString n) :
    threshold n j x = false := by
  have : weight x ≤ n := by simpa using weight_le x
  rw [← Bool.not_eq_true, threshold_eq_true_iff]
  omega

/-- With cutoff `1`, the threshold function is the disjunction. -/
theorem threshold_one_right (x : BitString n) : threshold n 1 x = decide (∃ i, x i = true) := by
  rw [Bool.eq_iff_iff, threshold_eq_true_iff, decide_eq_true_iff, weight, one_le_card,
    filter_nonempty_iff]
  simp

/-- With cutoff `n`, the threshold function is the conjunction. -/
theorem threshold_self (x : BitString n) : threshold n n x = decide (∀ i, x i = true) := by
  have h : weight x ≤ n := by simpa using weight_le x
  have key : #{i | x i = true} = n ↔ ({i | x i = true} : Finset (Fin n)) = univ := by
    rw [← card_eq_iff_eq_univ, Fintype.card_fin]
  rw [Bool.eq_iff_iff, threshold_eq_true_iff, decide_eq_true_iff,
    show n ≤ weight x ↔ weight x = n by omega, weight, key, filter_eq_self]
  simp

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

/-- Parity is the parity of the weight. -/
theorem parity_eq_decide_weight (x : BitString n) : parity n x = decide (weight x % 2 = 1) :=
  rfl

/-- Parity is symmetric. -/
theorem isSymmetric_parity : (parity n).IsSymmetric := fun x y h => by
  simp only [weight] at h
  simp only [parity, parityOn, h]

end Cslib
