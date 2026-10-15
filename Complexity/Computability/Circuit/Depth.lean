/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Circuit/Depth.lean`)

public import Cslib.Computability.Circuit.Depth

/-!
# Depths along program lines

Every wire read by a gate is shallower than the gate (`Program.wireDepths_lines_lt`), which is what
makes induction on depth go through for programs.

## Main results

* `Cslib.Circuits.Program.wireDepths_lines_lt`: the wires a gate reads are shallower than it.
* `Cslib.Circuits.Program.depths_pos`: gates have positive depth.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {n g : ℕ}

/-- A gate is deeper than every wire it reads. -/
theorem Line.wireDepth_lt_depth (line : Line σ n g) (depths : Wire n g → ℕ)
    (a : Fin (σ.Arity line.op)) : depths (line.wires a) < line.depth depths := by
  have h := (line.depth_le_add_one_iff depths (d := line.depth depths - 1)).1
    (by have := line.depth_pos depths; omega) a
  have := line.depth_pos depths
  omega

/-- The wires read by a gate of a program are shallower than the gate. -/
theorem Program.wireDepths_lines_lt (p : Program σ n g) (k : Fin g)
    (a : Fin (σ.Arity (p.lines k).op)) : p.wireDepths ((p.lines k).wires a) < p.depths k := by
  induction p with
  | empty => exact k.elim0
  | @gate g p line ih =>
    revert a
    induction k using Fin.lastCases with
    | last =>
      rw [Program.lines_gate_last, Program.depths_gate_last]
      intro a
      change (p.gate line).wireDepths (Wire.Renaming.castSucc (line.wires a)) < _
      rw [Wire.Renaming.castSucc_apply, Program.wireDepths_gate_castSucc]
      exact line.wireDepth_lt_depth _ a
    | cast k =>
      rw [Program.lines_gate_castSucc, Program.depths_gate_castSucc]
      intro a
      change (p.gate line).wireDepths (Wire.Renaming.castSucc ((p.lines k).wires a)) < _
      rw [Wire.Renaming.castSucc_apply, Program.wireDepths_gate_castSucc]
      exact ih k a

/-- Every gate of a program has positive depth. -/
theorem Program.depths_pos (p : Program σ n g) (k : Fin g) : 0 < p.depths k := by
  induction p with
  | empty => exact k.elim0
  | @gate g p line ih =>
    induction k using Fin.lastCases with
    | last => rw [Program.depths_gate_last]; exact line.depth_pos _
    | cast k => rw [Program.depths_gate_castSucc]; exact ih k

end Cslib.Circuits
