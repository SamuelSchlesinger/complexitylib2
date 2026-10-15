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

A map of signatures `φ : σ.Hom τ` sends each operation of `σ` to an operation of `τ` of the same
arity. It translates programs and circuits over `σ` into programs and circuits over `τ` gate by gate
(`Circuit.mapOp`), keeping the size and the depth (`Circuit.size_mapOp`, `Circuit.depth_mapOp`),
and when the interpretation of `φ op` is that of `op` the translated circuit computes the same
function (`Circuit.eval_mapOp`). This embeds circuits over a basis into circuits over a larger
basis; it is the simulation of cslib's `Program.simulate` in which every gate costs one gate and
keeps its depth.

## Main definitions

* `Cslib.Circuits.Signature.Hom`: an arity-preserving map of operations.
* `Cslib.Circuits.Signature.Hom.Preserves`: a map of operations keeps their meaning.
* `Cslib.Circuits.Circuit.mapOp`: the translation of a circuit along a map of signatures.

## Main results

* `Cslib.Circuits.Circuit.eval_mapOp`, `Cslib.Circuits.Circuit.Computes.mapOp`: the translation
  computes the same function under agreeing interpretations.
* `Cslib.Circuits.Circuit.size_mapOp`, `Cslib.Circuits.Circuit.depth_mapOp`: size and depth are
  kept.
-/

@[expose] public section

namespace Cslib.Circuits

/-- A map of signatures: an arity-preserving map of operations. -/
structure Signature.Hom (σ τ : Signature) where
  /-- The image of each operation. -/
  toFun : σ.Op → τ.Op
  /-- Operations keep their arity. -/
  arity_eq : ∀ op, τ.Arity (toFun op) = σ.Arity op

variable {σ τ : Signature} {n g m : ℕ} {U : Type*}

/-- The identity map of a signature. -/
def Signature.Hom.id (σ : Signature) : σ.Hom σ :=
  ⟨_root_.id, fun _ => rfl⟩

/-- `φ` keeps the meaning of every operation: `op` means under `I` what `φ op` means under `J`. -/
def Signature.Hom.Preserves (φ : σ.Hom τ) (I : Interpretation σ U) (J : Interpretation τ U) :
    Prop :=
  ∀ op (x : Fin (σ.Arity op) → U), J (φ.toFun op) (fun a => x (Fin.cast (φ.arity_eq op) a)) = I op x

theorem Signature.Hom.preserves_id (I : Interpretation σ U) : (Hom.id σ).Preserves I I :=
  fun _ _ => rfl

variable (φ : σ.Hom τ)

/-- The line performing `φ op` on the wires of `line`. -/
def Line.mapOp (line : Line σ n g) : Line τ n g :=
  ⟨φ.toFun line.op, fun a => line.wires (Fin.cast (φ.arity_eq line.op) a)⟩

/-- The program performing `φ op` in place of each operation `op`. -/
def Program.mapOp : {g : ℕ} → Program σ n g → Program τ n g
  | _, .empty => .empty
  | _, .gate p line => .gate (p.mapOp) (line.mapOp φ)

/-- The circuit performing `φ op` in place of each operation `op`. -/
def Circuit.mapOp (c : Circuit σ n m) : Circuit τ n m :=
  ⟨c.program.mapOp φ, c.outputs⟩

variable {φ}

@[simp] theorem Circuit.size_mapOp (c : Circuit σ n m) : (c.mapOp φ).size = c.size :=
  rfl

/-- A translated line has the same depth. -/
theorem Line.depth_mapOp (line : Line σ n g) (depths : Wire n g → ℕ) :
    (line.mapOp φ).depth depths = line.depth depths :=
  le_antisymm
    ((Line.depth_le_add_one_iff _ _).2 fun _ => (line.depth_le_add_one_iff depths).1 le_rfl _)
    ((Line.depth_le_add_one_iff _ _).2 fun a => by
      simpa [Line.mapOp] using ((line.mapOp φ).depth_le_add_one_iff depths).1 le_rfl
        (Fin.cast (φ.arity_eq line.op).symm a))

/-- The translated program has the same gate depths. -/
theorem Program.depths_mapOp (p : Program σ n g) : (p.mapOp φ).depths = p.depths := by
  induction p with
  | empty => funext k; exact k.elim0
  | gate p line ih =>
    funext k
    induction k using Fin.lastCases with
    | last =>
      simp only [Program.mapOp, Program.depths_gate_last, Program.wireDepths, ih, Line.depth_mapOp]
    | cast k => simp only [Program.mapOp, Program.depths_gate_castSucc, ih]

@[simp] theorem Circuit.depth_mapOp (c : Circuit σ n m) : (c.mapOp φ).depth = c.depth := by
  simp only [Circuit.depth, Circuit.outputDepths, Circuit.mapOp, Program.wireDepths,
    Program.depths_mapOp]

variable {I : Interpretation σ U} {J : Interpretation τ U}

/-- The translated program computes the same gate values, if the interpretations agree. -/
theorem Program.eval_mapOp (hIJ : φ.Preserves I J) (p : Program σ n g) (x : Fin n → U) :
    (p.mapOp φ).eval J x = p.eval I x := by
  induction p with
  | empty => funext k; exact k.elim0
  | gate p line ih =>
    funext k
    induction k using Fin.lastCases with
    | last =>
      rw [Program.mapOp, Program.eval_gate_last, Program.eval_gate_last, ih]
      exact hIJ line.op (Wire.elim x (p.eval I x) ∘ line.wires)
    | cast k => rw [Program.mapOp, Program.eval_gate_castSucc, Program.eval_gate_castSucc, ih]

/-- **The translated circuit computes the same function**, if the interpretations agree. -/
theorem Circuit.eval_mapOp (hIJ : φ.Preserves I J) (c : Circuit σ n m) (x : Fin n → U) :
    (c.mapOp φ).eval J x = c.eval I x := by
  funext o
  simp only [Circuit.eval, Circuit.mapOp, Function.comp_apply, Program.trace]
  rw [Program.eval_mapOp hIJ]

theorem Circuit.Computes.mapOp (hIJ : φ.Preserves I J) {c : Circuit σ n m}
    {f : (Fin n → U) → Fin m → U} (hc : c.Computes I f) : (c.mapOp φ).Computes J f :=
  fun x => (Circuit.eval_mapOp hIJ c x).trans (hc x)

end Cslib.Circuits
