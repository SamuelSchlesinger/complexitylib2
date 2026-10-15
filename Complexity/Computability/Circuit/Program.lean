/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Computability/Circuit/Program.lean`)

public import Cslib.Computability.Circuit.Program

/-!
# Lines read earlier wires

In the widened lines of a program (`Program.lines`), every gate wire that a line reads comes
before the line's own gate (`Program.lt_of_lines_wires_eq_gate`), so facts about wires can be
proved by induction along the program order (`Program.wire_induction`).
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {n g : ℕ}

/-- The gate wires read by a line come before its gate. -/
theorem Program.lt_of_lines_wires_eq_gate (p : Program σ n g) (k : Fin g)
    (s : Fin (σ.Arity (p.lines k).op)) (j : Fin g) (h : (p.lines k).wires s = .gate j) :
    j < k := by
  induction p with
  | empty => exact k.elim0
  | @gate g p line ih =>
    -- Both kinds of gate widen a line whose gate wires are earlier, by `Wire.castSucc`.
    have widen (line' : Line σ n g) (bound : Fin (g + 1))
        (hbound : ∀ s j, line'.wires s = .gate j → j.castSucc < bound) :
        ∀ s j, (line'.mapWires Wire.Renaming.castSucc).wires s = .gate j → j < bound := by
      intro s j h
      change Wire.Renaming.castSucc (line'.wires s) = _ at h
      rw [Wire.Renaming.castSucc_apply] at h
      cases hw : line'.wires s with
      | input => rw [hw] at h; cases h
      | gate j' =>
        rw [hw] at h
        cases h
        exact hbound s j' hw
    revert s j
    induction k using Fin.lastCases with
    | last =>
      rw [Program.lines_gate_last]
      exact widen line _ fun _ j _ => Fin.castSucc_lt_last j
    | cast k =>
      rw [Program.lines_gate_castSucc]
      exact widen _ _ fun s j hw => Fin.castSucc_lt_castSucc_iff.2 (ih k s j hw)

/-- Induction along the program order: a property of wires that holds for the inputs, and for a
gate whenever it holds for the wires the gate reads, holds for every wire. -/
theorem Program.wire_induction (p : Program σ n g) {P : Wire n g → Prop}
    (input : ∀ i, P (.input i)) (gate : ∀ k, (∀ s, P ((p.lines k).wires s)) → P (.gate k))
    (w : Wire n g) : P w := by
  have hgate : ∀ m, ∀ k : Fin g, (k : ℕ) = m → P (.gate k) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro k hk
      refine gate k fun s => ?_
      cases hw : (p.lines k).wires s with
      | input i => exact input i
      | gate j => exact ih j (hk ▸ p.lt_of_lines_wires_eq_gate k s j hw) j rfl
  cases w with
  | input i => exact input i
  | gate k => exact hgate k k rfl

end Cslib.Circuits
