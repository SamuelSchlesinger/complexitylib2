/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange

/-!
# List selection identities

## Main results

* `List.foldr_ite_eq_of_mem`: a chain of equality tests selects the branch of a contained tag.
  Used by deterministic and probabilistic finite-control certificates.
* `List.countP_range_eq_card_filter`: counting the numbers below `n` that pass a test is counting
  the elements of `Fin n` that pass it.

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

/-- The numbers below `n` that pass a test are as many as the elements of `Fin n` that pass it. -/
theorem List.countP_range_eq_card_filter (n : ℕ) (p : ℕ → Bool) :
    (List.range n).countP p = (Finset.univ.filter fun j : Fin n => p j = true).card := by
  rw [← List.map_coe_finRange_eq_range, List.countP_map, Fin.univ_def,
    List.countP_eq_length_filter]
  simp [Finset.filter, Finset.card, Function.comp_def]
