/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Order/Fin/Basic.lean`)

public import Complexity.Init
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Basic

/-!
# Equal neighbors in monotone finite arrays

A repeated value in a monotone finite array has an equal predecessor or successor.
The value type needs only a partial order.

## Main results

* `Fin.exists_ne_apply_eq_iff_adjacent`: an adjacent witness suffices for any repeated value.

## References

Adapted from MassProduction/Nonuniform/AdjacentDuplicates.lean in
[S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

/-- In a monotone finite array, every repeated value has an equal neighbor. -/
theorem Fin.exists_ne_apply_eq_iff_adjacent {α : Type*} [PartialOrder α] {count : ℕ}
    (f : Fin count → α) (ordered : Monotone f) (i : Fin count) :
    (∃ j, j ≠ i ∧ f j = f i) ↔
      ((∃ positive : 0 < i.val, f ⟨i.val - 1, by lia⟩ = f i) ∨
        (∃ fits : i.val + 1 < count, f ⟨i.val + 1, fits⟩ = f i)) := by
  constructor
  · rintro ⟨j, different, same⟩
    rcases lt_or_gt_of_ne different with before | after
    · refine Or.inl ⟨by lia, ?_⟩
      exact (ordered.eq_of_ge_of_le same (by change j.val ≤ i.val - 1; lia)
        (by change i.val - 1 ≤ i.val; lia)).trans same
    · have fits : i.val + 1 < count := (Nat.succ_le_of_lt after).trans_lt j.isLt
      exact Or.inr ⟨fits, ordered.eq_of_ge_of_le same.symm
        (by change i.val ≤ i.val + 1; lia) (by exact Nat.succ_le_of_lt after)⟩
  · rintro (⟨positive, same⟩ | ⟨fits, same⟩)
    · refine ⟨⟨i.val - 1, by lia⟩, ?_, same⟩
      intro equal
      have := congrArg Fin.val equal
      dsimp only at this
      lia
    · refine ⟨⟨i.val + 1, fits⟩, ?_, same⟩
      intro equal
      have := congrArg Fin.val equal
      dsimp only at this
      lia
