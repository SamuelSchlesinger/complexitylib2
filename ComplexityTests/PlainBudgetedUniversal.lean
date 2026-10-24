/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Computability.Complexity.Classes.Hierarchy.SpaceUniversal

/-! The budgeted universal machine uses independent plain resource bounds without class imports. -/
namespace ComplexityTests.PlainBudgetedUniversal
open Turing.MultiTapeTM Turing.MultiTapeTM.Universal

-- Zero budget rejects every step, even for an unbounded runtime clock.
example (d : Desc) (x : List ℕ) (t : ℕ) : budgetedUniversal (d, x, t, 0) = ([], false) := by
  have h (i : ℕ) : (budgetStep d x 0)^[i] (init d, []) = (init d, []) := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih, budgetStep]
      split_ifs with hb
      · rw [eCfg_apply, length_encPair] at hb
        omega
      · rfl
  simp only [budgetedUniversal, h]
  rfl

-- A zero clock performs no computation, independently of the available workspace.
example (d : Desc) (x : List ℕ) (b : ℕ) : budgetedUniversal (d, x, 0, b) = ([], false) := rfl

example (d : Desc) (x : List ℕ) (b t : ℕ) :
    ((budgetStep d x b)^[t] (init d, [])).2.length ≤ 2 :=
  length_budgetStep_iterate_le d x b t

example : ComputableInO budgetedUniversal eInS eOut
    (fun i => (i.2.2.1 + 1) * ((eInS i).length + 1) ^ 2 * (budgetSpace i + 1) ^ 3)
    budgetSpace := computableInO_budgetedUniversal

end ComplexityTests.PlainBudgetedUniversal
