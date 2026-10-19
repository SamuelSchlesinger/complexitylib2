/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.SensitivitySeparation.Internal.RecursiveDefinitions
public import Complexity.Computability.QueryComplexity.SensitivitySeparation.Internal.Basic
import Mathlib.Tactic

/-!
# Superquadratic sensitivity separation: recursive flips

This file analyses the effect of a single raw bit flip on a row clause. Flipping the coordinate
`((j, c), a)` changes only the child at `(j, c)`. Hence it can change the clause of row `i` only if
`j = i` and it changes the target value of that child, or if `j` is an out-neighbour of `i`,
`c = label i j` and it changes the gate value of that child. These facts underlie all sensitivity
recurrences.

## Main results

* `recursiveChild_flip_same`: flipping `((j, c), a)` flips coordinate `a` of the child at `(j, c)`.
* `recursiveChild_flip_other`: flipping `((j, c), a)` leaves every other child unchanged.
* `rowClause_flip_eq`: a flip that changes none of the conditions of a row clause leaves the clause
  unchanged.
* `rowClause_flip_change`: a flip that changes a row clause changes its target condition in its own
  row or a gate condition on a labeled outgoing edge.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/RecursiveFlips.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

/-- Flipping the raw coordinate `((j, c), a)` flips coordinate `a` of the child at `(j, c)`. -/
theorem recursiveChild_flip_same {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) (a : I) :
    recursiveChild (flip x {((j, c), a)}) j c = flip (recursiveChild x j c) {a} :=
  flip_prod_same x (j, c) a

/-- Flipping the raw coordinate `((j, c), a)` does not change the child at any position
`(j', c') ≠ (j, c)`. -/
theorem recursiveChild_flip_other {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j j' : Fin k) (c c' : Fin r) (a : I)
    (h : (j', c') ≠ (j, c)) :
    recursiveChild (flip x {((j, c), a)}) j' c' = recursiveChild x j' c' :=
  flip_prod_other x a h

/-- If `x` and `y` give the same target values on all children of row `i` and the same gate values
on the children `(j, label i j)` for all out-neighbours `j` of `i`, then the clause of row `i` takes
the same value at `x` and `y`. -/
theorem rowClause_eq_of_conditions {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x y : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (ht : ∀ c, F (Fin.last h) (recursiveChild x i c) =
      F (Fin.last h) (recursiveChild y i c))
    (hg : ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) =
      F (gateIndex q) (recursiveChild y j (label i j))) :
    rowClause T label F q x i = rowClause T label F q y i := by
  apply Bool.eq_iff_iff.mpr
  rw [rowClause_eq_true_iff, rowClause_eq_true_iff]
  constructor
  · rintro ⟨hxt, hxg⟩
    exact ⟨fun c => (ht c).symm.trans (hxt c),
      fun j hij => (hg j hij).symm.trans (hxg j hij)⟩
  · rintro ⟨hyt, hyg⟩
    exact ⟨fun c => (ht c).trans (hyt c),
      fun j hij => (hg j hij).trans (hyg j hij)⟩

/-- Flipping `((j, c), a)` does not change the clause of row `i`, provided it does not change the
target value of the child at `(j, c)` when `j = i`, nor its gate value when `T.Adj i j` and
`c = label i j`. -/
theorem rowClause_flip_eq {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k) (c : Fin r) (a : I)
    (ht : j = i → F (Fin.last h) (flip (recursiveChild x j c) {a}) =
      F (Fin.last h) (recursiveChild x j c))
    (hg : T.Adj i j → c = label i j →
      F (gateIndex q) (flip (recursiveChild x j c) {a}) =
        F (gateIndex q) (recursiveChild x j c)) :
    rowClause T label F q (flip x {((j, c), a)}) i = rowClause T label F q x i := by
  apply rowClause_eq_of_conditions
  · intro c'
    by_cases heq : (i, c') = (j, c)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rw [recursiveChild_flip_same]
      exact ht rfl
    · rw [recursiveChild_flip_other x j i c c' a heq]
  · intro j' hij'
    by_cases heq : (j', label i j') = (j, c)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rw [recursiveChild_flip_same]
      exact hg hij' rfl
    · rw [recursiveChild_flip_other x j j' c (label i j') a heq]

/-- If flipping `((j, c), a)` changes the clause of row `i`, then either `j = i` and the flip
changes the target value of the child at `(j, c)`, or `T.Adj i j`, `c = label i j` and the flip
changes the gate value of that child. -/
theorem rowClause_flip_change {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k) (c : Fin r) (a : I)
    (hc : rowClause T label F q (flip x {((j, c), a)}) i ≠ rowClause T label F q x i) :
    (j = i ∧ F (Fin.last h) (flip (recursiveChild x j c) {a}) ≠
      F (Fin.last h) (recursiveChild x j c)) ∨
    (T.Adj i j ∧ c = label i j ∧
      F (gateIndex q) (flip (recursiveChild x j c) {a}) ≠
        F (gateIndex q) (recursiveChild x j c)) := by
  by_contra hn
  apply hc
  apply rowClause_flip_eq
  · intro hji
    by_contra hne
    exact hn (Or.inl ⟨hji, hne⟩)
  · intro hij hcl
    by_contra hne
    exact hn (Or.inr ⟨hij, hcl, hne⟩)

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
