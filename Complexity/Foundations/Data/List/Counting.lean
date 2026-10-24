/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.List.Basic

/-!
# List counts and scan bounds

## Main results

* `List.length_flatMap_le`: blocks of bounded length have bounded total length.
* `List.decide_mem_eq_any`: membership as a scan of the list.
* `List.countP_and_not_add_countP_and`: members satisfying one predicate split by whether
  they satisfy another.
-/

@[expose] public section

/-- Blocks of at most `k` elements each, one for each element of `l`, have at most `|l| k`
elements in total. -/
theorem List.length_flatMap_le {α β : Type*} {l : List α} {f : α → List β} {k : ℕ}
    (h : ∀ a ∈ l, (f a).length ≤ k) : (l.flatMap f).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    have hl := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

/-- Membership in a list as a scan of the list, the form in which polynomial-time membership tests
are certified. -/
theorem List.decide_mem_eq_any {α : Type*} [DecidableEq α] (a : α) (l : List α) :
    decide (a ∈ l) = l.any fun u => decide (u = a) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, List.any_eq_true]
  simp

/-- Partitioning the elements of a list satisfying `p` by whether they satisfy `q`. -/
theorem List.countP_and_not_add_countP_and {α : Type*} (p q : α → Prop) [DecidablePred p]
    [DecidablePred q] (l : List α) :
    l.countP (fun a => ¬ q a ∧ p a) + l.countP (fun a => p a ∧ q a) = l.countP (fun a => p a) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons]
    by_cases hp : p a <;> by_cases hq : q a <;>
      simp only [hp, hq, not_true_eq_false, not_false_eq_true, and_true, and_false,
        decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] <;> omega
