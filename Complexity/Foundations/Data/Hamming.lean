/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib `InformationTheory/Hamming.lean`)

public import Cslib.Init
public import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Hamming distance one

Two functions are at Hamming distance one when they differ at exactly one coordinate
(`hammingDist_eq_one_iff`); changing one coordinate of a function to a new value moves it to
distance one (`hammingDist_update_of_ne`). The pairs of `A × B` at Hamming distance one are the
edges of the Hamming graph between `A` and `B` (`hammingEdges`); counting them from either side
gives the same number (`card_hammingEdges_comm`, `card_hammingEdges_eq_sum_card_filter`).

## Main definitions

* `hammingEdges`: the pairs of `A × B` at Hamming distance one.
-/

@[expose] public section

open Finset Function

variable {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, DecidableEq (β i)]

/-- Two functions are at Hamming distance one when they differ at exactly one coordinate. -/
theorem hammingDist_eq_one_iff {x y : ∀ i, β i} :
    hammingDist x y = 1 ↔ ∃ i, x i ≠ y i ∧ ∀ j, j ≠ i → x j = y j := by
  rw [hammingDist, card_eq_one]
  constructor
  · rintro ⟨i, hi⟩
    have hmem (j : ι) : x j ≠ y j ↔ j = i := by simpa using Finset.ext_iff.1 hi j
    exact ⟨i, (hmem i).2 rfl, fun j hj => not_not.1 fun h => hj ((hmem j).1 h)⟩
  · rintro ⟨i, hi, h⟩
    refine ⟨i, Finset.ext fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      simpa using hi
    · simpa [hj] using h j hj

/-- Changing one coordinate to a new value moves to Hamming distance one. -/
theorem hammingDist_update_of_ne [DecidableEq ι] {x : ∀ i, β i} {i : ι} {v : β i}
    (h : x i ≠ v) : hammingDist x (update x i v) = 1 :=
  hammingDist_eq_one_iff.2 ⟨i, by simpa using h, fun j hj => (update_of_ne hj _ _).symm⟩

/-- The pairs of `A × B` at Hamming distance one: the edges of the Hamming graph between `A` and
`B`. -/
def hammingEdges (A B : Finset (∀ i, β i)) : Finset ((∀ i, β i) × ∀ i, β i) :=
  (A ×ˢ B).filter fun e => hammingDist e.1 e.2 = 1

variable {A B : Finset (∀ i, β i)}

@[simp] theorem mem_hammingEdges {e : (∀ i, β i) × ∀ i, β i} :
    e ∈ hammingEdges A B ↔ e.1 ∈ A ∧ e.2 ∈ B ∧ hammingDist e.1 e.2 = 1 := by
  simp [hammingEdges, and_assoc]

theorem card_hammingEdges_comm (A B : Finset (∀ i, β i)) :
    #(hammingEdges A B) = #(hammingEdges B A) :=
  card_bij (fun e _ => e.swap) (fun e he => by simp_all [hammingDist_comm])
    (fun _ _ _ _ h => Prod.swap_injective h)
    fun e he => ⟨e.swap, by simp_all [hammingDist_comm]⟩

/-- Splitting `B` splits the edges. -/
theorem card_hammingEdges_filter_add_card_hammingEdges_filter_not (p : (∀ i, β i) → Prop)
    [DecidablePred p] :
    #(hammingEdges A (B.filter p)) + #(hammingEdges A (B.filter fun b => ¬p b)) =
      #(hammingEdges A B) := by
  have h (q : (∀ i, β i) → Prop) [DecidablePred q] :
      hammingEdges A (B.filter q) = (hammingEdges A B).filter fun e => q e.2 := by
    ext e
    simp only [mem_hammingEdges, mem_filter]
    tauto
  rw [h, h, card_filter_add_card_filter_not]

/-- The number of edges is the sum over `A` of the numbers of neighbors in `B`. -/
theorem card_hammingEdges_eq_sum_card_filter (A B : Finset (∀ i, β i)) :
    #(hammingEdges A B) = ∑ a ∈ A, #{b ∈ B | hammingDist a b = 1} := by
  simp only [hammingEdges, card_filter, sum_product]
