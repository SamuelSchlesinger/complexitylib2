/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Nat/Init.lean`)

public import Complexity.Init

/-!
# A discrete intermediate value theorem

A sequence of natural numbers that grows by at most one per step takes every value between its
value at the start and any of its later values (`Nat.exists_eq_of_forall_le_add_one`). Compare
`SimpleGraph.Walk.mem_support_hasse_of_ge_of_le`, the same fact for walks in the Hasse diagram of
a linear order.

## Main results

* `Nat.exists_eq_of_forall_le_add_one`: the discrete intermediate value theorem.
-/

@[expose] public section

namespace Nat

/-- **A discrete intermediate value theorem.** A sequence of natural numbers that grows by at
most one per step up to time `T` takes, by time `T`, every value between `a 0` and `a T`. -/
theorem exists_eq_of_forall_le_add_one {a : ℕ → ℕ} {k T : ℕ} (h0 : a 0 ≤ k) (hT : k ≤ a T)
    (hstep : ∀ t < T, a (t + 1) ≤ a t + 1) : ∃ t ≤ T, a t = k := by
  induction T with
  | zero => exact ⟨0, Nat.le_refl 0, Nat.le_antisymm h0 hT⟩
  | succ T ih =>
    by_cases h : k ≤ a T
    · obtain ⟨t, ht, hat⟩ := ih h fun t ht => hstep t (by omega)
      exact ⟨t, by omega, hat⟩
    · exact ⟨T + 1, Nat.le_refl _, by have := hstep T (by omega); omega⟩

end Nat
