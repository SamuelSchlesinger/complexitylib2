/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Depth

/-!
# Translating circuits between signatures

An arity-preserving map `f` from the operations of `σ` to those of `τ` translates programs and
circuits over `σ` into programs and circuits over `τ` gate by gate (`Circuit.mapOp`). The size and
the depth stay the same (`Circuit.size_mapOp`, `Circuit.depth_mapOp`), and when the interpretation
of `f op` is that of `op` the translated circuit computes the same function
(`Circuit.eval_mapOp`). This embeds circuits over a basis into circuits over a larger basis.

## Main definitions

* `Cslib.Circuits.Circuit.mapOp`: the translation of a circuit along a map of operations.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ τ : Signature} {n g m : ℕ} {U : Type*}
  (f : σ.Op → τ.Op) (hf : ∀ op, τ.Arity (f op) = σ.Arity op)

/-- The line performing `f op` on the wires of `line`. -/
def Line.mapOp (line : Line σ n g) : Line τ n g :=
  ⟨f line.op, fun a => line.wires (Fin.cast (hf line.op) a)⟩

/-- The program performing `f op` in place of each operation `op`. -/
def Program.mapOp : {g : ℕ} → Program σ n g → Program τ n g
  | _, .empty => .empty
  | _, .gate p line => .gate (p.mapOp) (line.mapOp f hf)

/-- The circuit performing `f op` in place of each operation `op`. -/
def Circuit.mapOp (c : Circuit σ n m) : Circuit τ n m :=
  ⟨c.program.mapOp f hf, c.outputs⟩

variable {f hf}

@[simp] theorem Circuit.size_mapOp (c : Circuit σ n m) : (c.mapOp f hf).size = c.size :=
  rfl

/-- The translated program has the same gate depths. -/
theorem Program.depths_mapOp (p : Program σ n g) : (p.mapOp f hf).depths = p.depths := by
  induction p with
  | empty => funext k; exact k.elim0
  | gate p line ih =>
    funext k
    induction k using Fin.lastCases with
    | last =>
      rw [Program.mapOp, Program.depths_gate_last, Program.depths_gate_last]
      have hw : (p.mapOp f hf).wireDepths = p.wireDepths := by
        funext w
        cases w with
        | input i => rfl
        | gate j => exact congrFun ih j
      rw [hw]
      refine le_antisymm ?_ ?_
      · exact (Line.depth_le_add_one_iff _ _ (d := line.depth p.wireDepths - 1)).2 fun a => by
          have := (Line.depth_le_add_one_iff line p.wireDepths
            (d := line.depth p.wireDepths - 1)).1
            (by have := line.depth_pos p.wireDepths; omega) (Fin.cast (hf line.op) a)
          exact this
        |>.trans (by have := line.depth_pos p.wireDepths; omega)
      · refine ((Line.depth_le_add_one_iff _ _ (d := (line.mapOp f hf).depth p.wireDepths - 1)).2
          fun a => ?_).trans (by have := (line.mapOp f hf).depth_pos p.wireDepths; omega)
        have := (Line.depth_le_add_one_iff (line.mapOp f hf) p.wireDepths
          (d := (line.mapOp f hf).depth p.wireDepths - 1)).1
          (by have := (line.mapOp f hf).depth_pos p.wireDepths; omega)
          (Fin.cast (hf line.op).symm a)
        simpa [Line.mapOp] using this
    | cast k =>
      rw [Program.mapOp, Program.depths_gate_castSucc, Program.depths_gate_castSucc]
      exact congrFun ih k

@[simp] theorem Circuit.depth_mapOp (c : Circuit σ n m) : (c.mapOp f hf).depth = c.depth := by
  simp only [Circuit.depth, Circuit.outputDepths, Circuit.mapOp]
  congr 1
  funext d j
  congr 2
  simp only [Program.wireDepths, Program.depths_mapOp]

variable {I : Interpretation σ U} {J : Interpretation τ U}

/-- The translated program computes the same gate values, if the interpretations agree. -/
theorem Program.eval_mapOp (hIJ : ∀ op (x : Fin (σ.Arity op) → U),
      J (f op) (fun a => x (Fin.cast (hf op) a)) = I op x) (p : Program σ n g) (x : Fin n → U) :
    (p.mapOp f hf).eval J x = p.eval I x := by
  induction p with
  | empty => funext k; exact k.elim0
  | gate p line ih =>
    funext k
    induction k using Fin.lastCases with
    | last =>
      rw [Program.mapOp, Program.eval_gate_last, Program.eval_gate_last, ih]
      exact hIJ line.op (Wire.elim x (p.eval I x) ∘ line.wires)
    | cast k =>
      rw [Program.mapOp, Program.eval_gate_castSucc, Program.eval_gate_castSucc, ih]

/-- **The translated circuit computes the same function**, if the interpretations agree. -/
theorem Circuit.eval_mapOp (hIJ : ∀ op (x : Fin (σ.Arity op) → U),
      J (f op) (fun a => x (Fin.cast (hf op) a)) = I op x) (c : Circuit σ n m) (x : Fin n → U) :
    (c.mapOp f hf).eval J x = c.eval I x := by
  funext o
  simp only [Circuit.eval, Circuit.mapOp, Function.comp_apply, Program.trace]
  rw [Program.eval_mapOp hIJ]

end Cslib.Circuits
