/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (additions to `Cslib/Computability/Languages/Slice.lean`)

public import Complexity.Init
public import Cslib.Computability.Languages.Slice

/-!
# Slices of Boolean combinations of languages

The slices of the empty and the full language, of complements, unions and intersections.
-/

@[expose] public section

namespace Language

variable {α : Type*} {L M : Language α} {n : ℕ} {x : Fin n → α}

@[simp] theorem slice_zero : (0 : Language α).slice n x = false :=
  Bool.eq_false_iff.2 fun h => notMem_zero _ (slice_eq_true_iff.1 h)

@[simp] theorem slice_top : (⊤ : Language α).slice n x = true := slice_eq_true_iff.2 trivial

@[simp] theorem slice_compl : Lᶜ.slice n x = !L.slice n x := by
  cases h : L.slice n x
  · exact slice_eq_true_iff.2 fun hm => by simp [slice_eq_true_iff.2 hm] at h
  · exact Bool.eq_false_iff.2 fun h' => (slice_eq_true_iff.1 h') (slice_eq_true_iff.1 h)

@[simp] theorem slice_sup : (L ⊔ M).slice n x = (L.slice n x || M.slice n x) := by
  rw [Bool.eq_iff_iff, Bool.or_eq_true, slice_eq_true_iff, slice_eq_true_iff, slice_eq_true_iff]
  exact Iff.rfl

@[simp] theorem slice_inf : (L ⊓ M).slice n x = (L.slice n x && M.slice n x) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, slice_eq_true_iff, slice_eq_true_iff, slice_eq_true_iff]
  exact Iff.rfl

end Language
