/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists

/-!
# Tests for the polynomial-time calculus

Christian Reitwiessner's `CslibTests/MultiTapePolyTime.lean` (branch `crei/tidy-universal`
@7f7c0696), and the change that branch makes to `CslibTests/MultiTapeComplexity.lean`.
-/

namespace ComplexityTests.MultiTapePolyTime

open Turing.MultiTapeTM

-- `fun_prop` assembles polynomial-time computability from the closure properties.
example : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => (p.2, p.1 + 1 + 1))
    (encPair encNat encNat) (encPair encNat encNat) := by
  fun_prop

example {c : ℕ → Bool} (hc : ComputableTidilyInPolyTime c encNat encBool) :
    ComputableTidilyInPolyTime (fun n => if c n then n + 1 else n) encNat encNat := by
  fun_prop

private def finish (move : SignType) (symbol : Bool) : Turing.MultiTapeTM 0 Bool Unit :=
  ofTr () fun _ _ _ => ⟨move, Fin.elim0, some symbol, none⟩

private def bit : Bool ↪ List Bool := ⟨fun b => [b], by intro a b h; simpa using h⟩

-- A deterministic machine that has halted after `t` steps satisfies the time bound `t`.
example (symbol : Bool) :
    ComputableInTimeAndSpace (fun _ : Bool => symbol) bit bit
      (fun b => if b then 1 else 2) (fun _ => 0) := by
  refine ⟨0, Unit, inferInstance, finish 0 symbol, fun b ↦ ?_⟩
  have h : ((finish 0 symbol).runFrom ((finish 0 symbol).initCfg (bit b)) 1).Halted ∧
      ((finish 0 symbol).runFrom ((finish 0 symbol).initCfg (bit b)) 1).output = bit symbol := by
    rw [runFrom, Function.iterate_one, step_of_state rfl]
    simp [finish, Turing.Cfg.Halted]; rfl
  exact ⟨⟨1, h⟩, (runsInTime_iff_halted.mpr h.1).mono (by cases b <;> decide), by simp⟩


/-- `length_le_length_encList` holds in every universe. -/
example {α : Type 1} (enc : α ↪ List Bool) (l : List α) :
    l.length ≤ (Turing.MultiTapeTM.encList enc l).length :=
  Turing.MultiTapeTM.length_le_length_encList enc l

end ComplexityTests.MultiTapePolyTime
