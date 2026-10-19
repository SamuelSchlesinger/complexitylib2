/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.List
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.PiLex
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Counting words

Counting the words `List.ofFn v`, for `v : Fin n → Bool`, that pass a test: the counting arguments
of parity and counting classes, which count accepted certificates. A word of length `m + n` is a
prefix of length `m` followed by a word of length `n`
(`Cslib.BitString.card_filter_ofFn_add`); a word of length `n + 1` is a first bit followed by a
word of length `n` (`Cslib.BitString.card_filter_ofFn_succ`); a word of `T` rows of `B` bits
whose rows pass independent tests is counted by a product
(`Cslib.BitString.card_filter_listRows_all`). Exactly one word has no bit `true`, and exactly one
has no bit `false` (`Cslib.BitString.card_filter_not_any`, `Cslib.BitString.card_filter_all`).

The lexicographic order on words of equal length (`Cslib.BitString.wordLt`) is the order of
`Lex (Fin n → Bool)` (`Cslib.BitString.wordLt_ofFn_iff`), so strictly increasing lists of words
represent sets of words.

## Main definitions

* `Cslib.BitString.wordLt`: the lexicographic order on words of equal length.

## Main results

* `Cslib.BitString.card_filter_ofFn_add`, `Cslib.BitString.card_filter_ofFn_succ`: counting
  words by a prefix or by their first bit.
* `Cslib.BitString.card_filter_listRows_all`: counting words by a condition on each row.
* `Cslib.BitString.card_filter_not_any`, `Cslib.BitString.card_filter_all`: the constant words.
* `Cslib.BitString.ofFn_decide_lt`: the unary word of `k` bits `true` among `K`.
* `Cslib.BitString.wordLt_ofFn_iff`: `wordLt` is the lexicographic order.
-/

@[expose] public section

namespace Cslib.BitString

open Finset

/-! ### Counting words -/

/-- **Counting words by their prefixes**: the words of length `m + n` are the words `u ++ w`
with `u` of length `m` and `w` of length `n`. -/
theorem card_filter_ofFn_add (m n : ℕ) (g : List Bool → List Bool → Prop)
    [∀ u w, Decidable (g u w)] :
    (univ.filter fun v : Fin (m + n) → Bool =>
      g ((List.ofFn v).take m) ((List.ofFn v).drop m)).card =
      ∑ u : Fin m → Bool,
        (univ.filter fun w : Fin n → Bool => g (List.ofFn u) (List.ofFn w)).card := by
  classical
  rw [← card_map (Fin.appendEquiv m n).symm.toEmbedding]
  have hmap : (univ.filter fun v : Fin (m + n) → Bool =>
      g ((List.ofFn v).take m) ((List.ofFn v).drop m)).map
        (Fin.appendEquiv m n).symm.toEmbedding =
      univ.filter fun x : (Fin m → Bool) × (Fin n → Bool) => g (List.ofFn x.1) (List.ofFn x.2) := by
    ext x
    simp only [mem_map_equiv, Equiv.symm_symm, mem_filter, mem_univ, true_and]
    change g ((List.ofFn (Fin.append x.1 x.2)).take m)
      ((List.ofFn (Fin.append x.1 x.2)).drop m) ↔ _
    rw [List.ofFn_fin_append, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn]
  rw [hmap, card_filter, Fintype.sum_prod_type]
  simp only [card_filter]

/-- **Counting words by their first bit.** -/
theorem card_filter_ofFn_succ (n : ℕ) (g : List Bool → Prop) [DecidablePred g] :
    (univ.filter fun v : Fin (n + 1) → Bool => g (List.ofFn v)).card =
      (univ.filter fun w : Fin n → Bool => g (true :: List.ofFn w)).card +
        (univ.filter fun w : Fin n → Bool => g (false :: List.ofFn w)).card := by
  classical
  rw [← card_map (Fin.consEquiv fun _ => Bool).symm.toEmbedding]
  have hmap : (univ.filter fun v : Fin (n + 1) → Bool => g (List.ofFn v)).map
      (Fin.consEquiv fun _ => Bool).symm.toEmbedding =
      univ.filter fun x : Bool × (Fin n → Bool) => g (x.1 :: List.ofFn x.2) := by
    ext x
    simp only [mem_map_equiv, Equiv.symm_symm, mem_filter, mem_univ, true_and]
    change g (List.ofFn (Fin.cons x.1 x.2 : Fin (n + 1) → Bool)) ↔ _
    rw [List.ofFn_succ]
    simp
  rw [hmap, card_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [card_filter]

/-- Only the word of `false`s has no bit `true`. -/
theorem card_filter_not_any (n : ℕ) :
    (univ.filter fun w : Fin n → Bool => (!(List.ofFn w).any fun b => b) = true).card = 1 := by
  rw [card_eq_one]
  refine ⟨fun _ => false, ext fun w => ?_⟩
  simp only [mem_filter, mem_univ, true_and, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.any_eq_false, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff,
    mem_singleton, Bool.not_eq_true]
  exact ⟨fun h => funext h, fun h i => by rw [h]⟩

/-- Only the word of `true`s has all bits `true`. -/
theorem card_filter_all (n : ℕ) :
    (univ.filter fun w : Fin n → Bool => ((List.ofFn w).all fun b => b) = true).card = 1 := by
  rw [card_eq_one]
  refine ⟨fun _ => true, ext fun w => ?_⟩
  simp only [mem_filter, mem_univ, true_and, List.all_eq_true, List.mem_ofFn,
    forall_exists_index, forall_apply_eq_imp_iff, mem_singleton]
  exact ⟨fun h => funext h, fun h i => by rw [h]⟩

/-- **Counting words by rows**: the words of `T` rows of `B` bits whose `j`-th row satisfies
`g j` for every `j` are counted by the product of the counts of the rows. -/
theorem card_filter_listRows_all (T B : ℕ) (g : ℕ → List Bool → Bool) :
    (univ.filter fun v : Fin (T * B) → Bool =>
      ((listRows T B (List.ofFn v)).zipIdx.all fun p => g p.2 p.1) = true).card =
      ∏ j : Fin T, (univ.filter fun w : Fin B → Bool => g j (List.ofFn w) = true).card := by
  classical
  have hrows (v : Fin (T * B) → Bool) : listRows T B (List.ofFn v) =
      List.ofFn fun j => List.ofFn (blocksEquiv v j) := by
    rw [listRows_eq_ofFn, ofList_ofFn]
    rfl
  have hall (F : Fin T → List Bool) :
      ((List.ofFn F).zipIdx.all fun p => g p.2 p.1) = true ↔ ∀ j : Fin T, g j (F j) = true := by
    simp only [List.all_eq_true, Prod.forall]
    constructor
    · intro h j
      apply h
      rw [List.mem_zipIdx_iff_getElem?]
      simp
    · intro h w i hw
      rw [List.mem_zipIdx_iff_getElem?, List.getElem?_ofFn] at hw
      simp only at hw
      split at hw
      · rename_i hi
        rw [← Option.some.inj hw]
        exact h ⟨i, hi⟩
      · exact absurd hw (by simp)
  rw [← Fintype.card_piFinset]
  refine card_equiv blocksEquiv fun v => ?_
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, hrows, hall]

/-- The unary word of `k ≤ K` bits `true` followed by `false`s. -/
theorem ofFn_decide_lt {K k : ℕ} (hk : k ≤ K) :
    List.ofFn (fun i : Fin K => decide ((i : ℕ) < k)) =
      List.replicate k true ++ List.replicate (K - k) false := by
  apply List.ext_getElem (by
    simp only [List.length_ofFn, List.length_append, List.length_replicate]
    omega)
  intro i h₁ h₂
  simp only [List.length_ofFn] at h₁
  rw [List.getElem_ofFn]
  by_cases hik : i < k
  · rw [List.getElem_append_left (by simpa using hik)]
    simp [hik]
  · rw [List.getElem_append_right (by simpa using hik)]
    simp [hik]

/-! ### The lexicographic order -/

/-- The lexicographic order on words of equal length: `x` is below `y` at the first position
where they differ. -/
def wordLt (x y : List Bool) : Bool :=
  (List.range x.length).any fun i =>
    ((List.range i).all fun j => x.getD j false == y.getD j false) &&
      (!x.getD i false && y.getD i false)

/-- On bit strings, `wordLt` is the lexicographic order. -/
theorem wordLt_ofFn_iff {n : ℕ} (x y : Fin n → Bool) :
    wordLt (List.ofFn x) (List.ofFn y) = true ↔ toLex x < toLex y := by
  have hget (z : Fin n → Bool) (j : ℕ) (hj : j < n) : (List.ofFn z).getD j false = z ⟨j, hj⟩ := by
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
  change _ ↔ ∃ i, (∀ j, j < i → x j = y j) ∧ x i < y i
  simp only [wordLt, List.any_eq_true, List.mem_range, List.length_ofFn, Bool.and_eq_true,
    List.all_eq_true, beq_iff_eq, Bool.not_eq_true']
  constructor
  · rintro ⟨i, hi, hall, hx, hy⟩
    refine ⟨⟨i, hi⟩, fun j hj => ?_, ?_⟩
    · have := hall j hj
      rwa [hget x j (by omega), hget y j (by omega)] at this
    · rw [hget x i hi] at hx
      rw [hget y i hi] at hy
      rw [hx, hy]
      decide
  · rintro ⟨i, hall, hlt⟩
    refine ⟨i, i.2, fun j hj => ?_, ?_, ?_⟩
    · rw [hget x j (by omega), hget y j (by omega)]
      exact hall ⟨j, by omega⟩ hj
    · rw [hget x i i.2]
      revert hlt
      cases x i <;> cases y i <;> decide
    · rw [hget y i i.2]
      revert hlt
      cases x i <;> cases y i <;> decide

end Cslib.BitString
