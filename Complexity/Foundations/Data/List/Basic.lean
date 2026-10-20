/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD

/-!
# List selection identities

## Main results

* `List.foldr_ite_eq_of_mem`: a chain of equality tests selects the branch of a contained tag.
  Used by deterministic and probabilistic finite-control certificates.
* `List.length_flatMap_le`: blocks of bounded length have bounded total length.
* `List.getD_set_self`, `List.getD_set_ne`, `List.forall_mem_set_of_forall_mem`,
  `List.getD_le_of_forall_le`: lists as register files, updated by `List.set` and read by
  `List.getD`.

## References

Adapts the selection identity from `Computability/Probabilistic/Finite.lean` on the cslib
`crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

/-- A chain of equality tests selects a contained tag, regardless of duplicates or fallback. -/
theorem List.foldr_ite_eq_of_mem {Tag Value : Type*} [DecidableEq Tag]
    (tags : List Tag) (tag : Tag) (branch : Tag → Value) (fallback : Value) (h : tag ∈ tags) :
    tags.foldr (fun candidate rest => if tag = candidate then branch candidate else rest)
      fallback = branch tag := by
  induction tags with
  | nil => simp at h
  | cons candidate tags ih =>
    by_cases heq : tag = candidate
    · simp [heq]
    · simp only [List.foldr_cons, heq, ↓reduceIte]
      exact ih (List.mem_cons.mp h |>.resolve_left heq)

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

/-! ### Lists as register files -/

/-- Reading the updated entry of a list. -/
theorem List.getD_set_self {α : Type*} {l : List α} {i : ℕ} {x d : α} (h : i < l.length) :
    (l.set i x).getD i d = x := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_set_self]

/-- Reading another entry of an updated list. -/
theorem List.getD_set_ne {α : Type*} {l : List α} {i j : ℕ} {x d : α} (h : i ≠ j) :
    (l.set i x).getD j d = l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

/-- A property of all the entries of a list holds of all the entries of an update by a value
having it. -/
theorem List.forall_mem_set_of_forall_mem {α : Type*} {p : α → Prop} {l : List α} {i : ℕ} {x : α}
    (h : ∀ a ∈ l, p a) (hx : p x) : ∀ a ∈ l.set i x, p a := fun a ha => by
  rcases List.mem_or_eq_of_mem_set ha with ha | rfl
  · exact h a ha
  · exact hx

/-- The entries of a list of numbers at most `B`, read with default `0`, are at most `B`. -/
theorem List.getD_le_of_forall_le {l : List ℕ} {B : ℕ} (h : ∀ a ∈ l, a ≤ B) (j : ℕ) :
    l.getD j 0 ≤ B := by
  rw [List.getD_eq_getElem?_getD]
  rcases hj : l[j]? with _ | a
  · exact Nat.zero_le _
  · exact h a (List.mem_of_getElem? hj)
