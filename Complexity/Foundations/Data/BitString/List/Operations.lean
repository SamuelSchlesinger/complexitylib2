/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.List
public import Complexity.Foundations.Data.BitString.Weight
public import Mathlib.Data.Matrix.Mul

/-!
# Algebraic operations on lists of bits

Finite bit strings and ordinary lists agree under pointwise XOR, Boolean dot products, basis
vectors, subset sums and strict majority. List algorithms are total: an out-of-range basis index
produces zeros, missing selectors are false, and XOR truncates to the shorter list.

## Main definitions

* `Cslib.BitString.listStrictMajority`: strict majority, returning false on a tie.
* `Cslib.BitString.listSingle`, `Cslib.BitString.listSingles`: basis vectors in coordinate order.
* `Cslib.BitString.listXorSelected`: sum selected rows using an ordinary fold.

## Main results

* `Cslib.BitString.ofFn_add`, `Cslib.BitString.dotProduct_eq_foldl`: algebraic representation laws.
* `Cslib.BitString.listStrictMajority_map`: a list with distinct voting indices agrees with
  finite-set strict majority.
* `Cslib.BitString.listXorSelected_eq_ofFn_sum`: the selector fold computes the finite mask sum.

## References

Adapted from `Probability/WordBits.lean` and `Crypto/Computational/GoldreichLevin/WordDecoder.lean`
on the cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.BitString

/-- Adding finite masks is exactly coordinatewise XOR of their word representations. -/
theorem ofFn_add {n : ℕ} (left right : BitString n) :
    List.ofFn (left + right) = (List.ofFn left).zipWith Bool.xor (List.ofFn right) := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp [List.getElem_zipWith, Bool.add_eq_xor]

/-- A Boolean dot product is a pointwise AND followed by a parity fold on words. -/
theorem dotProduct_eq_foldl {n : ℕ} (left right : BitString n) :
    left ⬝ᵥ right = ((List.ofFn left).zipWith Bool.and (List.ofFn right)).foldl Bool.xor false := by
  have hzip : (List.ofFn left).zipWith Bool.and (List.ofFn right) =
      List.ofFn (fun i => left i * right i) := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp [List.getElem_zipWith, Bool.mul_eq_and]
  rw [hzip, dotProduct, ← List.sum_ofFn]
  simp [List.sum_eq_foldl, Bool.add_eq_xor, Bool.zero_eq_false]

/-- Strict majority of a word of votes, choosing false on a tie. -/
def listStrictMajority (votes : List Bool) : Bool :=
  decide (votes.length < 2 * (votes.filter id).length)

/-- Listing each voting index once gives exactly finite-set strict majority. -/
theorem listStrictMajority_map {ι : Type} [DecidableEq ι]
    (indices : List ι) (hnodup : indices.Nodup)
    (vote : ι → Bool) :
    listStrictMajority (indices.map vote) = strictMajorityOn indices.toFinset vote := by
  rw [listStrictMajority, strictMajorityOn, ← List.toFinset_filter,
    List.toFinset_card_of_nodup hnodup,
    List.toFinset_card_of_nodup (hnodup.filter vote)]
  simp [List.filter_map, Nat.div_lt_iff_lt_mul, Nat.mul_comm]

/-- A coordinate mask, with all zeros when the index is outside the requested dimension. -/
def listSingle (dimension index : ℕ) : List Bool :=
  (List.range dimension).map (fun coordinate => decide (index = coordinate))

/-- The coordinate-mask program agrees with the finite basis vector. -/
theorem listSingle_eq_ofFn_single {n : ℕ} (index : Fin n) :
    listSingle n index = List.ofFn (Pi.single index true) := by
  apply List.ext_getElem (by simp [listSingle])
  intro coordinate hleft hright
  simp [listSingle, Pi.single_apply, Fin.ext_iff, Bool.zero_eq_false, eq_comm]

/-- All coordinate queries in their ordinary increasing order. -/
def listSingles (dimension : ℕ) : List (List Bool) :=
  (List.range dimension).map (listSingle dimension)

/-- The coordinate masks list the finite basis vectors in increasing index order. -/
theorem listSingles_eq_ofFn (dimension : ℕ) :
    listSingles dimension =
      List.ofFn (fun index : Fin dimension => List.ofFn (Pi.single index true)) := by
  apply List.ext_getElem (by simp [listSingles])
  intro index hleft hright
  simpa [listSingles] using
    listSingle_eq_ofFn_single (⟨index, by simpa using hright⟩ : Fin dimension)

/-- XOR the rows selected by a word of bits. Missing selector bits are false. The accumulator
starts at the requested dimension; rows of that dimension preserve its length. -/
def listXorSelected (dimension : ℕ) (selector : List Bool) (rows : List (List Bool)) : List Bool :=
  (rows.foldl (fun state row =>
    (state.1.tail, if state.1.headD false then state.2.zipWith Bool.xor row else state.2))
    (selector, List.replicate dimension false)).2

/-- On finite masks, the selector fold is exactly the sum of the selected rows. -/
theorem listXorSelected_eq_ofFn_sum {n k : ℕ} (selector : BitString k)
    (masks : Fin k → BitString n) :
    listXorSelected n (List.ofFn selector) (List.ofFn (fun i => List.ofFn (masks i))) =
      List.ofFn (∑ i, if selector i then masks i else 0) := by
  let advance (state : List Bool × List Bool) (row : List Bool) :=
    (state.1.tail, if state.1.headD false then state.2.zipWith Bool.xor row else state.2)
  have hfold (count : ℕ) (selector : BitString count) (masks : Fin count → BitString n)
      (value : BitString n) :
      (List.ofFn (fun i => List.ofFn (masks i))).foldl advance
          (List.ofFn selector, List.ofFn value) =
        ([], List.ofFn (value + ∑ i, if selector i then masks i else 0)) := by
    induction count generalizing value with
    | zero => simp
    | succ count ih =>
      cases h : selector 0 <;>
        simpa [List.ofFn_succ, advance, h, ← ofFn_add, Fin.sum_univ_succ, add_assoc] using
          ih (fun i => selector i.succ) (fun i => masks i.succ)
            (value + if selector 0 then masks 0 else 0)
  have hzero : List.ofFn (0 : BitString n) = List.replicate n false := by
    change List.ofFn (fun _ : Fin n => false) = _
    simp
  simpa [listXorSelected, advance, hzero] using
    congrArg Prod.snd (hfold k selector masks 0)

/-- Selecting the characteristic word of a finite subset computes its mask sum. -/
theorem listXorSelected_eq_ofFn_sum_subset {n k : ℕ} (indices : Finset (Fin k))
    (masks : Fin k → BitString n) :
    listXorSelected n (List.ofFn (fun i => decide (i ∈ indices)))
        (List.ofFn (fun i => List.ofFn (masks i))) = List.ofFn (∑ i ∈ indices, masks i) := by
  simpa using listXorSelected_eq_ofFn_sum (fun i => decide (i ∈ indices)) masks

end Cslib.BitString
