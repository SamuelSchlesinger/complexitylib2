/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.List.Basic

/-!
# List selection identities

## Main results

* `List.foldr_ite_eq_of_mem`: a chain of equality tests selects the branch of a contained tag.
  Used by deterministic and probabilistic finite-control certificates.

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
