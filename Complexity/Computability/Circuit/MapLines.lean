/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Depth

/-!
# Transforming circuits line by line

`Program.mapLines f` replaces every line of a program by its image under `f`, a map of lines over
one signature to lines over another that keeps the number of earlier gates, so the program keeps
its shape and its size. If `f` keeps the value of every line, the transformed program computes the
same gate values (`Program.eval_mapLines`), and if `f` never makes a line deeper, no gate becomes
deeper (`Program.depths_mapLines_le`). Translating the operations along a map of signatures
(`Program.mapOp`) is the special case changing only the operations; removing repeated arguments
of idempotent gates is another.

## Main definitions

* `Cslib.Circuits.Program.mapLines`, `Cslib.Circuits.Circuit.mapLines`: the program or circuit with
  every line transformed.

## Main results

* `Cslib.Circuits.Program.eval_mapLines`, `Cslib.Circuits.Circuit.eval_mapLines`: transforming
  lines that keep their values keeps the function computed.
* `Cslib.Circuits.Program.depths_mapLines_le`, `Cslib.Circuits.Circuit.depth_mapLines_le`:
  transforming lines that get no deeper keeps the depth bounded.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ τ : Signature} {n g m : ℕ} {U : Type*}

/-- The program with every line `line` replaced by `f line`. -/
def Program.mapLines (f : ∀ {g : ℕ}, Line σ n g → Line τ n g) :
    {g : ℕ} → Program σ n g → Program τ n g
  | _, .empty => .empty
  | _, .gate p line => (p.mapLines f).gate (f line)

/-- The circuit with every line `line` of its program replaced by `f line`. -/
def Circuit.mapLines (f : ∀ {g : ℕ}, Line σ n g → Line τ n g) (c : Circuit σ n m) :
    Circuit τ n m :=
  ⟨c.program.mapLines f, c.outputs⟩

variable {f : ∀ {g : ℕ}, Line σ n g → Line τ n g}

/-- Transforming the lines of the empty program gives the empty program. -/
@[simp] theorem Program.mapLines_empty : (Program.empty : Program σ n 0).mapLines f = .empty :=
  rfl

/-- Transforming the lines of a program transforms its last line and the lines before it. -/
@[simp] theorem Program.mapLines_gate (p : Program σ n g) (line : Line σ n g) :
    (p.gate line).mapLines f = (p.mapLines f).gate (f line) :=
  rfl

/-- The program of the transformed circuit is the transformed program. -/
@[simp] theorem Circuit.mapLines_program (c : Circuit σ n m) :
    (c.mapLines f).program = c.program.mapLines f :=
  rfl

/-- Transforming the lines keeps the outputs. -/
@[simp] theorem Circuit.mapLines_outputs (c : Circuit σ n m) :
    (c.mapLines f).outputs = c.outputs :=
  rfl

/-- Transforming the lines keeps the size. -/
@[simp] theorem Circuit.size_mapLines (c : Circuit σ n m) : (c.mapLines f).size = c.size :=
  rfl

section eval

variable {I : Interpretation σ U} {J : Interpretation τ U}

/-- Transforming lines that keep their values keeps the value of every gate. -/
theorem Program.eval_mapLines
    (hf : ∀ {g : ℕ} (line : Line σ n g) (x : Fin n → U) (gates : Fin g → U),
      (f line).eval J x gates = line.eval I x gates)
    (p : Program σ n g) (x : Fin n → U) : (p.mapLines f).eval J x = p.eval I x := by
  induction p with
  | empty => funext k; exact k.elim0
  | gate p line ih =>
    funext k
    induction k using Fin.lastCases with
    | last => rw [mapLines_gate, eval_gate_last, eval_gate_last, ih, hf]
    | cast k => rw [mapLines_gate, eval_gate_castSucc, eval_gate_castSucc, ih]

/-- **Transforming lines that keep their values keeps the function computed.** -/
theorem Circuit.eval_mapLines
    (hf : ∀ {g : ℕ} (line : Line σ n g) (x : Fin n → U) (gates : Fin g → U),
      (f line).eval J x gates = line.eval I x gates)
    (c : Circuit σ n m) : (c.mapLines f).eval J = c.eval I :=
  funext fun x => congrArg (fun gates => Wire.elim x gates ∘ c.outputs)
    (c.program.eval_mapLines hf x)

end eval

section depth

variable (hf : ∀ {g : ℕ} (line : Line σ n g) (depths : Wire n g → ℕ),
  (f line).depth depths ≤ line.depth depths)
include hf

/-- Transforming lines that get no deeper makes no gate deeper. -/
theorem Program.depths_mapLines_le (p : Program σ n g) (k : Fin g) :
    (p.mapLines f).depths k ≤ p.depths k := by
  induction p with
  | empty => exact k.elim0
  | @gate g p line ih =>
    have hw (w : Wire n g) : (p.mapLines f).wireDepths w ≤ p.wireDepths w := by
      cases w with
      | input i => exact le_rfl
      | gate j => exact ih j
    induction k using Fin.lastCases with
    | last =>
      rw [mapLines_gate, depths_gate_last, depths_gate_last]
      refine le_trans ?_ (hf line p.wireDepths)
      simpa using (f line).depthWith_mono (cost := 1) (cost' := 1) (fun _ => le_rfl) hw
    | cast k => simpa using ih k

/-- Transforming lines that get no deeper makes no wire deeper. -/
theorem Program.wireDepths_mapLines_le (p : Program σ n g) (w : Wire n g) :
    (p.mapLines f).wireDepths w ≤ p.wireDepths w := by
  cases w with
  | input i => exact le_rfl
  | gate j => exact p.depths_mapLines_le hf j

/-- **Transforming lines that get no deeper keeps the depth bounded.** -/
theorem Circuit.depth_mapLines_le (c : Circuit σ n m) : (c.mapLines f).depth ≤ c.depth :=
  (Circuit.depth_le_iff _).2 fun j =>
    (c.program.wireDepths_mapLines_le hf (c.outputs j)).trans (c.outputDepths_le_depth j)

end depth

end Cslib.Circuits
