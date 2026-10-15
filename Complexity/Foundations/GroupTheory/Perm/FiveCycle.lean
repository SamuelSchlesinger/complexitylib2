/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib `GroupTheory/Perm/Cycle/Type.lean`, next to `IsThreeCycle`)

public import Cslib.Init
public import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Tactic.Group

/-!
# Five-cycles

A five-cycle is a permutation of cycle type `{5}` (`Equiv.Perm.IsFiveCycle`), defined like
Mathlib's `Equiv.Perm.IsThreeCycle`. All five-cycles are conjugate
(`Equiv.Perm.IsFiveCycle.isConj`), and in `Fin 5` every five-cycle is a commutator of two
five-cycles (`Equiv.Perm.IsFiveCycle.exists_commutator`), the fact behind Barrington's theorem.

## Main definitions

* `Equiv.Perm.IsFiveCycle`: the permutations of cycle type `{5}`.

## Main results

* `Equiv.Perm.IsFiveCycle.exists_commutator`: every five-cycle of `Fin 5` is the commutator of two
  five-cycles.
-/

@[expose] public section

namespace Equiv.Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- A five-cycle is a cycle of length 5. -/
def IsFiveCycle (σ : Perm α) : Prop :=
  σ.cycleType = {5}

namespace IsFiveCycle

variable {σ τ : Perm α}

theorem cycleType (h : IsFiveCycle σ) : σ.cycleType = {5} :=
  h

theorem ne_one (h : IsFiveCycle σ) : σ ≠ 1 := by
  rintro rfl
  simpa using h.cycleType

theorem inv (h : IsFiveCycle σ) : IsFiveCycle σ⁻¹ := by
  rwa [IsFiveCycle, cycleType_inv]

@[simp] theorem inv_iff : IsFiveCycle σ⁻¹ ↔ IsFiveCycle σ :=
  ⟨by simpa using inv (σ := σ⁻¹), inv⟩

theorem conj (h : IsFiveCycle σ) (ρ : Perm α) : IsFiveCycle (ρ * σ * ρ⁻¹) := by
  rwa [IsFiveCycle, cycleType_conj]

/-- All five-cycles are conjugate. -/
theorem isConj (hσ : IsFiveCycle σ) (hτ : IsFiveCycle τ) : IsConj σ τ :=
  isConj_iff_cycleType_eq.2 (hσ.trans hτ.symm)

end IsFiveCycle

/-- The cyclic permutation of a list of five distinct elements is a five-cycle. -/
theorem isFiveCycle_formPerm {l : List α} (hl : l.Nodup) (hlen : l.length = 5) :
    IsFiveCycle l.formPerm := by
  rw [IsFiveCycle, (List.isCycle_formPerm hl (by omega)).cycleType,
    List.support_formPerm_of_nodup l hl fun x h => by simp [h] at hlen,
    List.toFinset_card_of_nodup hl, hlen]

/-- Every five-cycle of `Fin 5` is the commutator of two five-cycles. -/
theorem IsFiveCycle.exists_commutator {σ : Perm (Fin 5)} (hσ : IsFiveCycle σ) :
    ∃ α β, IsFiveCycle α ∧ IsFiveCycle β ∧ α * β * α⁻¹ * β⁻¹ = σ := by
  -- `(0 1 2 3 4)` and `(0 2 4 3 1)` have the commutator `(0 3 2 4 1)`.
  have hα := isFiveCycle_formPerm (l := ([0, 1, 2, 3, 4] : List (Fin 5))) (by decide) rfl
  have hβ := isFiveCycle_formPerm (l := ([0, 2, 4, 3, 1] : List (Fin 5))) (by decide) rfl
  have hγ := isFiveCycle_formPerm (l := ([0, 3, 2, 4, 1] : List (Fin 5))) (by decide) rfl
  have hcomm : List.formPerm [0, 1, 2, 3, 4] * List.formPerm [0, 2, 4, 3, 1] *
      (List.formPerm [0, 1, 2, 3, 4])⁻¹ * (List.formPerm [0, 2, 4, 3, 1])⁻¹ =
        (List.formPerm [0, 3, 2, 4, 1] : Perm (Fin 5)) := by
    decide
  obtain ⟨ρ, rfl⟩ := isConj_iff.1 (hγ.isConj hσ)
  exact ⟨_, _, hα.conj ρ, hβ.conj ρ, by rw [← hcomm]; group⟩

end Equiv.Perm
