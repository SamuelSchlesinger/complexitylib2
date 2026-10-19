/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Parity
public import Complexity.Logics.Propositional.CNF

/-!
# Parity constraints in conjunctive normal form

The constraint that the parity of the variables in a finite set `B` is `c` has a formula in
conjunctive normal form with one clause for each assignment to `B` of the other parity, excluding
that assignment (`CNF.parityOnEq`). Its clauses have `#B` literals each, and there are at most
`2 ^ #B` of them (`CNF.length_parityOnEq_le`).

## Main definitions

* `Cslib.Logic.PL.Clause.exclude`: the clause excluding the values of an assignment on a set of
  variables.
* `Cslib.Logic.PL.CNF.parityOnEq`: the parity constraint on a finite set of variables.

## Main results

* `Cslib.Logic.PL.CNF.eval_parityOnEq_eq_true_iff`: `CNF.parityOnEq B c` holds exactly when the
  parity of the variables in `B` is `c`.
* `Cslib.Logic.PL.CNF.length_parityOnEq_le`: it has at most `2 ^ #B` clauses.
-/

@[expose] public section

namespace Cslib.Logic.PL

open Finset

variable {ι : Type*}

/-- The clause excluding the values of `y` on `B`: it holds when the assignment differs from `y` at
some variable in `B`. -/
noncomputable def Clause.exclude (B : Finset ι) (y : ι → Bool) : Clause ι :=
  B.toList.map fun i => (i, !y i)

theorem Clause.eval_exclude_eq_true_iff (B : Finset ι) (y x : ι → Bool) :
    (Clause.exclude B y).eval x = true ↔ ∃ i ∈ B, x i ≠ y i := by
  simp [Clause.exclude, Clause.eval_eq_true_iff, Bool.eq_not_iff]

@[simp] theorem Clause.length_exclude (B : Finset ι) (y : ι → Bool) :
    (Clause.exclude B y).length = #B := by
  simp [Clause.exclude]

/-- The literals of `Clause.exclude B y` are the variables of `B`, with the polarity opposite to
their values in `y`. -/
theorem Clause.mem_exclude {B : Finset ι} {y : ι → Bool} {l : Literal ι} :
    l ∈ Clause.exclude B y ↔ l.1 ∈ B ∧ l.2 = !y l.1 := by
  obtain ⟨i, b⟩ := l
  simp only [Clause.exclude, List.mem_map, mem_toList, Prod.mk.injEq]
  constructor
  · rintro ⟨j, hj, rfl, rfl⟩
    exact ⟨hj, rfl⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨i, hi, rfl, rfl⟩

variable [Fintype ι] [DecidableEq ι]

/-- A formula in conjunctive normal form saying that the parity of the variables in `B` is `c`: a
clause excludes each assignment to `B` of the other parity. -/
noncomputable def CNF.parityOnEq (B : Finset ι) (c : Bool) : CNF ι :=
  ({y : ι → Bool | (∀ i ∉ B, y i = false) ∧ parityOn B y ≠ c} : Finset _).toList.map
    (Clause.exclude B)

theorem CNF.eval_parityOnEq_eq_true_iff (B : Finset ι) (c : Bool) (x : ι → Bool) :
    (CNF.parityOnEq B c).eval x = true ↔ parityOn B x = c := by
  simp only [CNF.parityOnEq, CNF.eval_map_eq_true_iff, mem_toList, mem_filter, mem_univ,
    true_and, Clause.eval_exclude_eq_true_iff, and_imp]
  constructor
  · intro h
    by_contra hne
    -- the assignment of `x` to `B` is excluded
    have hpar : parityOn B (fun i => if i ∈ B then x i else false) = parityOn B x :=
      parityOn_congr fun j hj => by simp [hj]
    obtain ⟨i, hi, hxi⟩ := h (fun i => if i ∈ B then x i else false)
      (fun i hi => by simp [hi]) (hpar ▸ hne)
    simp [hi] at hxi
  · intro hx y _ hy
    by_contra h
    push Not at h
    exact hy ((parityOn_congr h).symm.trans hx)

/-- A clause of `CNF.parityOnEq B c` excludes an assignment to `B`. -/
theorem CNF.exists_eq_exclude_of_mem_parityOnEq {B : Finset ι} {c : Bool} {d : Clause ι}
    (hd : d ∈ CNF.parityOnEq B c) : ∃ y : ι → Bool, d = Clause.exclude B y := by
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hd
  exact ⟨y, rfl⟩

/-- The clauses of `CNF.parityOnEq B c` have `#B` literals. -/
theorem CNF.length_of_mem_parityOnEq {B : Finset ι} {c : Bool} {d : Clause ι}
    (hd : d ∈ CNF.parityOnEq B c) : d.length = #B := by
  obtain ⟨y, rfl⟩ := CNF.exists_eq_exclude_of_mem_parityOnEq hd
  exact Clause.length_exclude B y

/-- `CNF.parityOnEq B c` has at most `2 ^ #B` clauses: one per assignment to `B`. -/
theorem CNF.length_parityOnEq_le (B : Finset ι) (c : Bool) :
    (CNF.parityOnEq B c).length ≤ 2 ^ #B := by
  rw [CNF.parityOnEq, List.length_map, length_toList, ← card_powerset]
  refine card_le_card_of_injOn (fun y => {i ∈ B | y i = true}) (fun y _ => ?_)
    fun y hy y' hy' h => ?_
  · exact mem_powerset.2 (filter_subset _ _)
  · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy hy'
    funext i
    by_cases hi : i ∈ B
    · have h' := congrArg (i ∈ ·) h
      simp only [mem_filter, hi, true_and, eq_iff_iff] at h'
      cases hyi : y i <;> cases hyi' : y' i <;> simp_all
    · rw [hy.1 i hi, hy'.1 i hi]

end Cslib.Logic.PL
