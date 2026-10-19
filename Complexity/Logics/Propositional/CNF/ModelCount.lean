/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF
public import Mathlib.Data.Fintype.Pi

/-!
# Counting satisfying assignments

`CNF.modelCount φ` is the number of satisfying assignments of a formula `φ` in conjunctive normal
form: the assignments of the variables occurring in `φ` (`CNF.vars`) that satisfy it. Variables
not occurring in `φ` are not counted, so the count does not depend on the type of variables, and
injective relabelling preserves it (`CNF.modelCount_relabel`). As a function of the formula this
is the counting problem `#SAT` [Valiant][Valiant1979].

Counts are usually computed through a map `f` from assignments to some finite type: if two
satisfying assignments have the same image exactly when they agree on the variables of `φ`, then
`φ` has as many satisfying assignments as there are images of satisfying assignments
(`CNF.modelCount_eq_card_filter`). A formula has a satisfying assignment exactly when its count
is positive (`CNF.modelCount_pos_iff`), and exactly one when every satisfying assignment agrees
with a given one on the variables of the formula (`CNF.modelCount_eq_one_iff`).

## Main definitions

* `Cslib.Logic.PL.CNF.extendAssignment`: an assignment of the variables of a formula, extended by
  `false` to all variables.
* `Cslib.Logic.PL.CNF.modelCount`: the number of satisfying assignments.

## Main results

* `Cslib.Logic.PL.CNF.modelCount_eq_card_filter`: counting satisfying assignments through a map.
* `Cslib.Logic.PL.CNF.modelCount_relabel`: injective relabelling preserves the count.
* `Cslib.Logic.PL.CNF.modelCount_pos_iff`, `Cslib.Logic.PL.CNF.modelCount_eq_one_iff`.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {V W : Type*} [DecidableEq V]

/-- The assignment of all variables extending an assignment `τ` of the variables of `φ` by
`false`. -/
def CNF.extendAssignment (φ : CNF V) (τ : φ.vars.toFinset → Bool) (v : V) : Bool :=
  if h : v ∈ φ.vars.toFinset then τ ⟨v, h⟩ else false

theorem CNF.extendAssignment_of_mem {φ : CNF V} (τ : φ.vars.toFinset → Bool) {v : V}
    (hv : v ∈ φ.vars) : φ.extendAssignment τ v = τ ⟨v, List.mem_toFinset.2 hv⟩ := by
  simp [CNF.extendAssignment, hv]

/-- **The number of satisfying assignments** of `φ`: the assignments of the variables occurring
in `φ` that satisfy it. -/
def CNF.modelCount (φ : CNF V) : ℕ :=
  (Finset.univ.filter fun τ : φ.vars.toFinset → Bool => φ.eval (φ.extendAssignment τ) = true).card

/-- An assignment of all variables satisfies `φ` exactly when its restriction to the variables of
`φ`, extended by `false`, does. -/
theorem CNF.eval_extendAssignment_restrict (φ : CNF V) (σ : V → Bool) :
    φ.eval (φ.extendAssignment fun v => σ v) = φ.eval σ :=
  CNF.eval_congr fun _ hv => CNF.extendAssignment_of_mem _ hv

/-- **Counting satisfying assignments through a map.** Let `f` send assignments to a finite type
so that two satisfying assignments have the same image exactly when they agree on the variables
of `φ`. Then the satisfying assignments of `φ` are as many as the images of satisfying
assignments, described by `P`. -/
theorem CNF.modelCount_eq_card_filter {ι : Type*} [Fintype ι] {φ : CNF V}
    (f : (V → Bool) → ι) (P : ι → Prop) [DecidablePred P]
    (hf : ∀ σ τ, φ.eval σ = true → φ.eval τ = true → (f σ = f τ ↔ ∀ v ∈ φ.vars, σ v = τ v))
    (hP : ∀ i, P i ↔ ∃ σ, φ.eval σ = true ∧ f σ = i) :
    φ.modelCount = (Finset.univ.filter P).card := by
  refine Finset.card_bij (fun τ _ => f (φ.extendAssignment τ)) (fun τ hτ => ?_)
    (fun τ₁ h₁ τ₂ h₂ h => ?_) fun i hi => ?_
  · rw [Finset.mem_filter] at hτ ⊢
    exact ⟨Finset.mem_univ _, (hP _).2 ⟨_, hτ.2, rfl⟩⟩
  · have h' := (hf _ _ (Finset.mem_filter.1 h₁).2 (Finset.mem_filter.1 h₂).2).1 h
    funext ⟨v, hv⟩
    have hv' := List.mem_toFinset.1 hv
    simpa only [CNF.extendAssignment_of_mem _ hv'] using h' v hv'
  · obtain ⟨σ, hσ, rfl⟩ := (hP i).1 (Finset.mem_filter.1 hi).2
    have he : φ.eval (φ.extendAssignment fun v => σ v) = true := by
      rw [CNF.eval_extendAssignment_restrict, hσ]
    exact ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩,
      (hf _ _ he hσ).2 fun _ hv => CNF.extendAssignment_of_mem _ hv⟩

/-- **Relabelling along an injective map preserves the number of satisfying assignments.** -/
theorem CNF.modelCount_relabel [DecidableEq W] {f : V → W} (hf : Function.Injective f)
    (φ : CNF V) : (φ.relabel f).modelCount = φ.modelCount := by
  refine CNF.modelCount_eq_card_filter (fun σ (v : φ.vars.toFinset) => σ (f v))
    (fun τ => φ.eval (φ.extendAssignment τ) = true) (fun σ τ _ _ => ?_) fun τ => ?_
  · rw [CNF.vars_relabel, List.forall_mem_map, funext_iff, Subtype.forall]
    simp only [List.mem_toFinset]
  · constructor
    · intro hτ
      refine ⟨Function.extend f (φ.extendAssignment τ) fun _ => false, ?_, funext fun v => ?_⟩
      · rwa [CNF.eval_relabel, Function.extend_comp hf]
      · rw [hf.extend_apply, CNF.extendAssignment_of_mem _ (List.mem_toFinset.1 v.2)]
    · rintro ⟨σ, hσ, rfl⟩
      rw [CNF.eval_relabel] at hσ
      rw [← hσ]
      exact CNF.eval_congr fun v hv => CNF.extendAssignment_of_mem _ hv

/-- A formula has a satisfying assignment exactly when its count is positive. -/
theorem CNF.modelCount_pos_iff {φ : CNF V} : 0 < φ.modelCount ↔ φ.Satisfiable := by
  rw [CNF.modelCount, Finset.card_pos, Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨τ, -, hτ⟩
    exact ⟨_, hτ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨fun v => σ v, Finset.mem_univ _, by rw [CNF.eval_extendAssignment_restrict, hσ]⟩

/-- A formula has exactly one satisfying assignment when some assignment satisfies it and every
satisfying assignment agrees with it on the variables of the formula. -/
theorem CNF.modelCount_eq_one_iff {φ : CNF V} :
    φ.modelCount = 1 ↔ ∃ σ : V → Bool, φ.eval σ = true ∧
      ∀ τ : V → Bool, φ.eval τ = true → ∀ v ∈ φ.vars, τ v = σ v := by
  rw [CNF.modelCount, Finset.card_eq_one]
  constructor
  · rintro ⟨τ₀, h⟩
    have hτ₀ : φ.eval (φ.extendAssignment τ₀) = true := by
      have := Finset.mem_singleton_self τ₀
      rw [← h, Finset.mem_filter] at this
      exact this.2
    refine ⟨_, hτ₀, fun τ hτ v hv => ?_⟩
    have hmem : (fun v => τ v : φ.vars.toFinset → Bool) ∈ ({τ₀} : Finset _) := by
      rw [← h, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [CNF.eval_extendAssignment_restrict, hτ]⟩
    rw [Finset.mem_singleton] at hmem
    rw [CNF.extendAssignment_of_mem _ hv, ← hmem]
  · rintro ⟨σ, hσ, h⟩
    refine ⟨fun v => σ v, Finset.eq_singleton_iff_unique_mem.2
      ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [CNF.eval_extendAssignment_restrict, hσ]⟩,
        fun τ hτ => funext fun ⟨v, hv⟩ => ?_⟩⟩
    have hv' := List.mem_toFinset.1 hv
    rw [← CNF.extendAssignment_of_mem τ hv']
    exact h _ (Finset.mem_filter.1 hτ).2 v hv'

end Cslib.Logic.PL
