/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`)

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.SymmDiff

/-!
# Reindexing a product by a symmetric difference

In a generalized Boolean algebra `b ↦ a ∆ b` is an involution, so over a finite generalized
Boolean algebra the product of `f (a ∆ b)` over all `b` is the product of `f b` over all `b`
(`Fintype.prod_symmDiff`, `Fintype.sum_symmDiff`). The main instance is the Boolean algebra of the
subsets of a finite type, where this reindexes sums over sets of coordinates by `S ↦ T ∆ S`.

## Main results

* `Fintype.prod_symmDiff`, `Fintype.sum_symmDiff`: reindexing a product or a sum by a symmetric
  difference.
-/

@[expose] public section

namespace Fintype

variable {α M : Type*} [Fintype α] [GeneralizedBooleanAlgebra α] [CommMonoid M]

/-- Reindexing a product over a finite generalized Boolean algebra by the involution
`b ↦ a ∆ b`. -/
@[to_additive /-- Reindexing a sum over a finite generalized Boolean algebra by the involution
`b ↦ a ∆ b`. -/]
theorem prod_symmDiff (a : α) (f : α → M) : ∏ b, f (symmDiff a b) = ∏ b, f b :=
  Equiv.prod_comp (Function.Involutive.toPerm _ (symmDiff_right_involutive a)) f

end Fintype
