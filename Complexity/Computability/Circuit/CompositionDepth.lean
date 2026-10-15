/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Circuit/Composition.lean`)

public import Cslib.Computability.Circuit.Composition
public import Complexity.Computability.Circuit.Depth

/-!
# Depth of composed circuits

Continuing a program does not change the depths of its wires (`Program.wireDepths_append_castAdd`),
and the wires of the continuation are at most as deep as in the continuation alone, plus the depth
of the wires feeding it (`Program.wireDepths_append_appendedWire_le`). So sequential composition
adds depths (`Circuit.depth_comp_le`) and parallel composition takes their maximum
(`Circuit.depth_append_le`).

## Main results

* `Cslib.Circuits.Circuit.depth_comp_le`: `depth (d.comp c) ≤ depth d + depth c`.
* `Cslib.Circuits.Circuit.depth_append_le`: `depth (c.append d) ≤ max (depth c) (depth d)`.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {n k m p g₁ g₂ : ℕ}

namespace Program

variable (P : Program σ n g₁) (feed : Fin k → Wire n g₁)

/-- Continuing a program does not change the depths of its wires. -/
theorem wireDepths_append_castAdd (q : Program σ k g₂) (w : Wire n g₁) :
    (P.append feed q).wireDepths (w.castAdd g₂) = P.wireDepths w := by
  induction q with
  | empty => cases w <;> rfl
  | gate q line ih =>
    cases w with
    | input i => rfl
    | gate j =>
      exact (Program.wireDepths_gate_castSucc _ _ (Wire.gate (j.castAdd _))).trans ih

/-- A wire of the continuation is at most as deep as in the continuation alone, plus the depth of
the wires feeding it. -/
theorem wireDepths_append_appendedWire_le {D : ℕ} (hD : ∀ i, P.wireDepths (feed i) ≤ D)
    (q : Program σ k g₂) (w : Wire k g₂) :
    (P.append feed q).wireDepths (appendedWire feed w) ≤ q.wireDepths w + D := by
  induction q with
  | empty =>
    cases w with
    | input i => exact (wireDepths_append_castAdd P feed .empty (feed i)).trans_le (by
        simpa using hD i)
    | gate j => exact j.elim0
  | gate q line ih =>
    cases w with
    | input i =>
      refine (wireDepths_append_castAdd P feed _ (feed i)).trans_le ?_
      simpa using hD i
    | gate j =>
      refine Fin.lastCases ?_ (fun j => ?_) j
      · change ((P.append feed q).gate (line.mapWires (appendedWire feed))).depths
          (Fin.last _) ≤ (q.gate line).depths (Fin.last _) + D
        rw [Program.depths_gate_last, Program.depths_gate_last]
        have hpos := line.depth_pos q.wireDepths
        refine le_trans ((Line.depth_le_add_one_iff _ _ (d := line.depth q.wireDepths - 1 + D)).2
          fun a => ?_) (by omega)
        have := line.wireDepth_lt_depth q.wireDepths a
        exact (ih (line.wires a)).trans (by omega)
      · change ((P.append feed q).gate (line.mapWires (appendedWire feed))).wireDepths
          (Wire.castSucc (Wire.gate (Fin.natAdd g₁ j))) ≤
          (q.gate line).wireDepths (Wire.castSucc (Wire.gate j)) + D
        rw [Program.wireDepths_gate_castSucc, Program.wireDepths_gate_castSucc]
        exact ih (.gate j)

end Program

namespace Circuit

/-- **Sequential composition adds depths.** -/
theorem depth_comp_le (d : Circuit σ m p) (c : Circuit σ n m) :
    (d.comp c).depth ≤ d.depth + c.depth :=
  (Circuit.depth_le_iff _).2 fun o =>
    (Program.wireDepths_append_appendedWire_le c.program c.outputs
      (fun i => c.outputDepths_le_depth i) d.program (d.outputs o)).trans
      (Nat.add_le_add_right (d.outputDepths_le_depth o) _)

/-- **Parallel composition takes the larger depth.** -/
theorem depth_append_le (c : Circuit σ n m) (d : Circuit σ n p) :
    (c.append d).depth ≤ max c.depth d.depth := by
  refine (Circuit.depth_le_iff _).2 fun o => ?_
  induction o using Fin.addCases with
  | left o =>
    change (c.program.append Wire.input d.program).wireDepths
      (Fin.append (Wire.castAdd d.size ∘ c.outputs)
        (Program.appendedWire Wire.input ∘ d.outputs) (Fin.castAdd p o)) ≤ _
    rw [Fin.append_left, Function.comp_apply, Program.wireDepths_append_castAdd]
    exact (c.outputDepths_le_depth o).trans (le_max_left _ _)
  | right o =>
    change (c.program.append Wire.input d.program).wireDepths
      (Fin.append (Wire.castAdd d.size ∘ c.outputs)
        (Program.appendedWire Wire.input ∘ d.outputs) (Fin.natAdd m o)) ≤ _
    rw [Fin.append_right, Function.comp_apply]
    exact (Program.wireDepths_append_appendedWire_le c.program Wire.input (D := 0)
      (fun i => le_rfl) d.program (d.outputs o)).trans
      ((d.outputDepths_le_depth o).trans (le_max_right _ _))

end Circuit

end Cslib.Circuits
