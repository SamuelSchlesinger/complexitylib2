/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: submitted #1138 @b1635b2e

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Complexity.Computability.Machines.Turing.MultiTape.Space

/-!
# Machines computing in zero space

The additions of cslib PR #1138 to `Cslib.Computability.Machines.Turing.MultiTape.Deterministic`:
a function computable in zero space is computable by a machine without work tapes.

## Main results

* `Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_no_work_tapes`.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- A function computable in zero space is computable by a machine without work tapes, within the
same bounds, since every work tape costs at least one cell (`MultiTapeNTM.RunsInSpace.le`). The
domain must be nonempty: otherwise the machine is never run and its number of tapes is arbitrary.
-/
theorem ComputableInTimeAndSpace.exists_no_work_tapes {α β : Type*} [Nonempty α]
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β} {t : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t (fun _ => 0)) :
    ∃ (State : Type) (_ : Finite State) (tm : MultiTapeTM 0 Bool State),
      ComputesFunInTimeAndSpace tm encIn encOut f t (fun _ => 0) := by
  obtain ⟨k, State, hfin, tm, htm⟩ := h
  obtain rfl : k = 0 := Nat.le_zero.mp (htm (Classical.arbitrary α)).2.2.le
  exact ⟨State, hfin, tm, htm⟩

end Turing.MultiTapeTM
