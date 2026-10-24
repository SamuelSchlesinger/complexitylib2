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
# List append boundaries and unary delimiters

## Main results

* `List.zip_tail_append_cons`: split adjacent pairs at a shared boundary element.
* `List.replicate_not_append_cons_inj`, `List.replicate_true_append_false_inj`: a unary block
  followed by its delimiter determines both its length and the remaining suffix.
-/

@[expose] public section

/-- Split consecutive pairs at a boundary element shared by the two list segments. -/
theorem List.zip_tail_append_cons {α : Type*} (before : List α) (middle : α)
    (after : List α) :
    (before ++ middle :: after).zip (before ++ middle :: after).tail =
      (before ++ [middle]).zip (before ++ [middle]).tail ++ (middle :: after).zip after := by
  induction before with
  | nil => simp
  | cons first before ih =>
    cases before with
    | nil => simp
    | cons second before =>
      simpa only [List.cons_append, List.tail_cons, List.zip_cons_cons] using
        congrArg (List.cons (first, second)) ih

/-- A unary block of copies of `!a` followed by the delimiter `a` determines both its length and the
remaining suffix. -/
theorem List.replicate_not_append_cons_inj {a : Bool} {m m' : ℕ} {l l' : List Bool}
    (h : List.replicate m (!a) ++ a :: l = List.replicate m' (!a) ++ a :: l') :
    m = m' ∧ l = l' := by
  induction m generalizing m' <;> cases m' <;> simp_all [List.replicate_succ]

/-- A unary block of `true` bits followed by `false` determines both its length and the remaining
suffix. -/
theorem List.replicate_true_append_false_inj {m m' : ℕ} {l l' : List Bool}
    (h : List.replicate m true ++ false :: l = List.replicate m' true ++ false :: l') :
    m = m' ∧ l = l' :=
  List.replicate_not_append_cons_inj (a := false) h
