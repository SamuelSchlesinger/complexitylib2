/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.Tree

/-!
# Sparsification -- searching the branching tree

A depth-first search of the branching tree of a rule (`BranchingRule.searchStep`) keeps a stack of
states and an accumulator. It pops the state on top; at a sparse state (a leaf) it adds the value
of a function `f` of the state to the accumulator, and at any other state it pushes the two
children. Started from a state `s`, after a number of steps less than twice the number of leaves
the stack is back to what it was below `s`, and the accumulator records whether `f` holds at some
leaf (`BranchingRule.exists_iterate_searchStep`). Along the way the stack holds at most `h + 1`
states of the tree of `s`, when its leaf words have length at most `h`.

With `f` a satisfiability test of the leaves, the search decides whether `s` is satisfiable
(`BranchingRule.exists_isLeafWord_sat_iff`).

## Main definitions

* `Cslib.Logic.PL.ClauseSet.Sparsification.BranchingRule.searchStep`: one step of depth-first
  search.

## Main results

* `Cslib.Logic.PL.ClauseSet.Sparsification.BranchingRule.exists_iterate_searchStep`: the search
  visits every leaf, within twice the number of leaves of steps, with a stack of bounded height.
* `Cslib.Logic.PL.ClauseSet.Sparsification.BranchingRule.exists_isLeafWord_sat_iff`: a state is
  satisfiable exactly when one of its leaves is.

## References

* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
* [C. Calabro, R. Impagliazzo, R. Paturi, *A duality between clause width and clause density for
  SAT*][CalabroImpagliazzoPaturi2006]
-/

@[expose] public section

namespace Cslib.Logic.PL.ClauseSet.Sparsification.BranchingRule

open Finset

variable {V : Type*} [DecidableEq V] {θ : ℕ → ℕ} {σ : Type*} (R : BranchingRule θ V σ)

/-- One step of the depth-first search of the branching tree, on a stack of states and an
accumulator: a sparse state on top is popped and `f` of it is added to the accumulator; any other
state on top is replaced by its heart and petal children. -/
noncomputable def searchStep (f : σ → Bool) : List σ × Bool → List σ × Bool
  | ([], acc) => ([], acc)
  | (s :: rest, acc) =>
    open Classical in
    if Sparse θ (R.toClauseSet s) then (rest, acc || f s)
    else (R.next s false :: R.next s true :: rest, acc)

variable {R}

/-- A state is satisfiable exactly when one of its leaves is. -/
theorem exists_isLeafWord_sat_iff (hθ : ∀ j, 1 ≤ θ j) (s : σ) (x : V → Bool) :
    (∃ w, R.IsLeafWord s w ∧ (R.toClauseSet (R.walk s w)).Sat x) ↔ (R.toClauseSet s).Sat x :=
  ⟨fun ⟨_, hw, hx⟩ => hw.isNodeWord.sat_of_sat_walk hx, exists_isLeafWord_sat hθ s⟩

/-- The leaf words of a state that is not sparse are the leaf words of its children, after their
branch. -/
private theorem isLeafWord_cons_iff {s : σ} {b : Bool} {w : List Bool} :
    R.IsLeafWord s (b :: w) ↔ ¬ Sparse θ (R.toClauseSet s) ∧ R.IsLeafWord (R.next s b) w :=
  Iff.rfl

/-- The only leaf word of a sparse state is the empty word. -/
private theorem IsLeafWord.eq_nil {s : σ} (hs : Sparse θ (R.toClauseSet s)) {w : List Bool}
    (hw : R.IsLeafWord s w) : w = [] := by
  cases w with
  | nil => rfl
  | cons b w => exact absurd hs hw.1

open Classical in
/-- **Depth-first search.** Started from a state `s` above a stack `rest`, the search takes `N`
steps, at most twice the number of leaves of `s`, to return to `rest`; then the accumulator
records whether `f` holds at a leaf of `s`. If the leaf words of `s` have length at most `h`, the
stack meanwhile consists of at most `h + 1` states of the tree of `s`, above `rest`. -/
theorem exists_iterate_searchStep (hθ : ∀ j, 1 ≤ θ j) (f : σ → Bool) (s : σ) {h : ℕ}
    (hh : ∀ w, R.IsLeafWord s w → w.length ≤ h) :
    ∃ W : Finset (List Bool), (∀ w ∈ W, R.IsLeafWord s w) ∧ ∃ N, N + 1 ≤ 2 * W.card ∧
      ∀ rest acc, (R.searchStep f)^[N] (s :: rest, acc) =
          (rest, acc || decide (∃ w, R.IsLeafWord s w ∧ f (R.walk s w) = true)) ∧
        ∀ i ≤ N, ∃ stk acc', (R.searchStep f)^[i] (s :: rest, acc) = (stk ++ rest, acc') ∧
          stk.length ≤ h + 1 ∧ ∀ t ∈ stk, ∃ w, R.IsNodeWord s w ∧ R.walk s w = t := by
  classical
  induction hp : potential (R.toClauseSet s) using Nat.strong_induction_on generalizing s h with
  | _ n ih =>
    by_cases hs : Sparse θ (R.toClauseSet s)
    · -- a leaf: one step
      refine ⟨{[]}, fun w hw => by rw [mem_singleton.mp hw]; exact hs, 1, by simp,
        fun rest acc => ⟨?_, fun i hi => ?_⟩⟩
      · simp only [Function.iterate_one, searchStep, hs, ↓reduceIte]
        congr 2
        rw [Bool.eq_iff_iff, decide_eq_true_iff]
        refine ⟨fun hf => ⟨[], hs, hf⟩, fun ⟨w, hw, hf⟩ => ?_⟩
        rwa [hw.eq_nil hs] at hf
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
        · exact ⟨[s], acc, rfl, by simp, fun t ht => ⟨[], trivial, (List.mem_singleton.mp ht).symm⟩⟩
        · refine ⟨[], acc || f s, ?_, by simp, by simp⟩
          simp only [Function.iterate_one, searchStep, hs, ↓reduceIte, List.nil_append]
    · -- an inner node: its two subtrees, one after the other
      have hlt (b : Bool) : potential (R.toClauseSet (R.next s b)) < n :=
        hp ▸ potential_next_lt hθ hs b
      have hh' (b : Bool) : ∀ w, R.IsLeafWord (R.next s b) w → w.length ≤ h - 1 := fun w hw => by
        have := hh (b :: w) ⟨hs, hw⟩
        simp only [List.length_cons] at this
        omega
      obtain ⟨u, hu⟩ := exists_isLeafWord (R := R) hθ s
      have hh1 : 1 ≤ h := by
        cases u with
        | nil => exact absurd hu hs
        | cons b u => have := hh _ hu; simp only [List.length_cons] at this; omega
      obtain ⟨W₀, hW₀, N₀, hN₀, h₀⟩ := ih _ (hlt false) (R.next s false) (hh' false) rfl
      obtain ⟨W₁, hW₁, N₁, hN₁, h₁⟩ := ih _ (hlt true) (R.next s true) (hh' true) rfl
      have hstep (rest : List σ) (acc : Bool) : R.searchStep f (s :: rest, acc) =
          (R.next s false :: R.next s true :: rest, acc) := by
        simp only [searchStep, hs, ↓reduceIte]
      have hdisj : Disjoint (W₀.image (false :: ·)) (W₁.image (true :: ·)) := by
        rw [Finset.disjoint_left]
        intro w hw₀ hw₁
        obtain ⟨u₀, -, rfl⟩ := mem_image.mp hw₀
        obtain ⟨u₁, -, hu₁⟩ := mem_image.mp hw₁
        exact Bool.false_ne_true (List.head_eq_of_cons_eq hu₁).symm
      refine ⟨W₀.image (false :: ·) ∪ W₁.image (true :: ·), fun w hw => ?_, N₁ + (N₀ + 1), ?_,
        fun rest acc => ⟨?_, fun i hi => ?_⟩⟩
      · rcases mem_union.mp hw with hw | hw
        · obtain ⟨u, hu, rfl⟩ := mem_image.mp hw
          exact ⟨hs, hW₀ u hu⟩
        · obtain ⟨u, hu, rfl⟩ := mem_image.mp hw
          exact ⟨hs, hW₁ u hu⟩
      · rw [card_union_of_disjoint hdisj, card_image_of_injective _ List.cons_injective,
          card_image_of_injective _ List.cons_injective]
        omega
      · rw [Function.iterate_add_apply, Function.iterate_succ_apply, hstep, (h₀ _ acc).1,
          (h₁ _ _).1, Bool.or_assoc]
        congr 2
        refine Bool.eq_iff_iff.mpr ?_
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro (⟨w, hw, hf⟩ | ⟨w, hw, hf⟩)
          · exact ⟨false :: w, ⟨hs, hw⟩, hf⟩
          · exact ⟨true :: w, ⟨hs, hw⟩, hf⟩
        · rintro ⟨w, hw, hf⟩
          cases w with
          | nil => exact absurd hw hs
          | cons b w =>
            cases b
            · exact Or.inl ⟨w, hw.2, hf⟩
            · exact Or.inr ⟨w, hw.2, hf⟩
      · -- the stack: the root, then the heart subtree above the petal child, then the petal
        -- subtree
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · exact ⟨[s], acc, rfl, by simp,
            fun t ht => ⟨[], trivial, (List.mem_singleton.mp ht).symm⟩⟩
        by_cases hi₀ : i ≤ N₀ + 1
        · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
          obtain ⟨stk, acc', heq, hlen, hmem⟩ := (h₀ (R.next s true :: rest) acc).2 j (by omega)
          refine ⟨stk ++ [R.next s true], acc', ?_, ?_, fun t ht => ?_⟩
          · rw [Function.iterate_succ_apply, hstep, heq, List.append_assoc, List.singleton_append]
          · simp only [List.length_append, List.length_singleton]
            omega
          · rcases List.mem_append.mp ht with ht | ht
            · obtain ⟨w, hw, rfl⟩ := hmem t ht
              exact ⟨false :: w, ⟨hs, hw⟩, rfl⟩
            · exact ⟨[true], ⟨hs, trivial⟩, (List.mem_singleton.mp ht).symm⟩
        · obtain ⟨j, rfl⟩ : ∃ j, i = j + (N₀ + 1) := ⟨i - (N₀ + 1), by omega⟩
          obtain ⟨stk, acc', heq, hlen, hmem⟩ :=
            (h₁ rest (acc || decide (∃ w, R.IsLeafWord (R.next s false) w ∧
              f (R.walk (R.next s false) w) = true))).2 j (by omega)
          refine ⟨stk, acc', ?_, by omega, fun t ht => ?_⟩
          · rw [Function.iterate_add_apply, Function.iterate_succ_apply, hstep,
              (h₀ _ acc).1, heq]
          · obtain ⟨w, hw, rfl⟩ := hmem t ht
            exact ⟨true :: w, ⟨hs, hw⟩, rfl⟩

end Cslib.Logic.PL.ClauseSet.Sparsification.BranchingRule
