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
arity. It is a map of the operation symbols, unlike cslib's `Homomorphism`, which maps the carriers
of two interpretations of one signature. It translates programs and circuits over `σ` into
programs and circuits over `τ` gate by gate (`Circuit.mapOp`), keeping the size and the depth
(`Circuit.size_mapOp`, `Circuit.depth_mapOp`), and when `φ` keeps the meaning of every operation
(`Signature.Hom.Preserves`) the translated circuit computes the same function
(`Circuit.eval_mapOp`). This embeds circuits over a basis into circuits over a larger basis; it is
analogous to cslib's `Program.simulate` with a budget of one gate for every operation.

## Main definitions

* `Cslib.Circuits.Signature.Hom`: an arity-preserving map of operations, with `Hom.id` and
  `Hom.comp`.
* `Cslib.Circuits.Signature.Hom.Preserves`: a map of operations keeps their meaning.
* `Cslib.Circuits.Line.mapOp`, `Cslib.Circuits.Program.mapOp`, `Cslib.Circuits.Circuit.mapOp`: the
  translation along a map of signatures.

## Main results

* `Cslib.Circuits.Circuit.eval_mapOp`, `Cslib.Circuits.Circuit.Computes.mapOp`: the translation
  computes the same function along a meaning-preserving map.
* `Cslib.Circuits.Circuit.size_mapOp`, `Cslib.Circuits.Circuit.depth_mapOp`: size and depth are
  kept.
* `Cslib.Circuits.Circuit.mapOp_id`, `Cslib.Circuits.Circuit.mapOp_comp`: translation is
  functorial.
-/

@[expose] public section

namespace Cslib.Circuits

/-- A map of signatures: an arity-preserving map of operations. -/
@[ext]
structure Signature.Hom (σ τ : Signature) where
  /-- The image of each operation. -/
  toFun : σ.Op → τ.Op
  /-- Operations keep their arity. -/
  arity_eq : ∀ op, τ.Arity (toFun op) = σ.Arity op

variable {σ τ υ : Signature} {n g m : ℕ} {U : Type*}

namespace Signature.Hom

/-- Maps of signatures are applied like functions. -/
instance : FunLike (σ.Hom τ) σ.Op τ.Op where
  coe φ := φ.toFun
  coe_injective _ _ h := Signature.Hom.ext h

@[simp] theorem toFun_eq_coe (φ : σ.Hom τ) : φ.toFun = ⇑φ :=
  rfl

/-- The identity map of a signature. -/
protected def id (σ : Signature) : σ.Hom σ :=
  ⟨_root_.id, fun _ => rfl⟩

/-- The composition of maps of signatures. -/
def comp (ψ : τ.Hom υ) (φ : σ.Hom τ) : σ.Hom υ :=
  ⟨ψ ∘ φ, fun op => (ψ.arity_eq (φ op)).trans (φ.arity_eq op)⟩

@[simp] theorem id_apply (op : σ.Op) : Hom.id σ op = op :=
  rfl

@[simp] theorem comp_apply (ψ : τ.Hom υ) (φ : σ.Hom τ) (op : σ.Op) : ψ.comp φ op = ψ (φ op) :=
  rfl

@[simp] theorem id_comp (φ : σ.Hom τ) : (Hom.id τ).comp φ = φ :=
  rfl

@[simp] theorem comp_id (φ : σ.Hom τ) : φ.comp (Hom.id σ) = φ :=
  rfl

theorem comp_assoc {ω : Signature} (χ : υ.Hom ω) (ψ : τ.Hom υ) (φ : σ.Hom τ) :
    (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) :=
  rfl

/-- `φ` keeps the meaning of every operation: `op` means under `I` what `φ op` means under `J`. -/
class Preserves (φ : σ.Hom τ) (I : Interpretation σ U) (J : Interpretation τ U) : Prop where
  /-- The operation `φ op` means under `J` what `op` means under `I`. -/
  interpret_eq : ∀ op (x : Fin (σ.Arity op) → U),
    J (φ op) (fun a => x (Fin.cast (φ.arity_eq op) a)) = I op x

instance preserves_id (I : Interpretation σ U) : (Hom.id σ).Preserves I I :=
  ⟨fun _ _ => rfl⟩

theorem Preserves.comp {I : Interpretation σ U} {J : Interpretation τ U}
    {K : Interpretation υ U} {ψ : τ.Hom υ} {φ : σ.Hom τ} (hψ : ψ.Preserves J K)
    (hφ : φ.Preserves I J) : (ψ.comp φ).Preserves I K :=
  ⟨fun op x => (hψ.interpret_eq (φ op) _).trans (hφ.interpret_eq op x)⟩

end Signature.Hom

variable (φ : σ.Hom τ)

/-- The line performing `φ op` on the wires of `line`. -/
def Line.mapOp (line : Line σ n g) : Line τ n g :=
  ⟨φ line.op, fun a => line.wires (Fin.cast (φ.arity_eq line.op) a)⟩

/-- The program performing `φ op` in place of each operation `op`. -/
def Program.mapOp : {g : ℕ} → Program σ n g → Program τ n g
  | _, .empty => .empty
  | _, .gate p line => .gate (p.mapOp) (line.mapOp φ)

/-- The circuit performing `φ op` in place of each operation `op`. -/
def Circuit.mapOp (c : Circuit σ n m) : Circuit τ n m :=
  ⟨c.program.mapOp φ, c.outputs⟩

variable {φ}

@[simp] theorem Line.mapOp_op (line : Line σ n g) : (line.mapOp φ).op = φ line.op :=
  rfl

@[simp] theorem Line.mapOp_wires (line : Line σ n g) (a : Fin (τ.Arity (φ line.op))) :
    (line.mapOp φ).wires a = line.wires (Fin.cast (φ.arity_eq line.op) a) :=
  rfl

@[simp] theorem Program.mapOp_empty : (Program.empty : Program σ n 0).mapOp φ = .empty :=
  rfl

@[simp] theorem Program.mapOp_gate (p : Program σ n g) (line : Line σ n g) :
    (p.gate line).mapOp φ = (p.mapOp φ).gate (line.mapOp φ) :=
  rfl

@[simp] theorem Circuit.mapOp_program (c : Circuit σ n m) :
    (c.mapOp φ).program = c.program.mapOp φ :=
  rfl

@[simp] theorem Circuit.mapOp_outputs (c : Circuit σ n m) : (c.mapOp φ).outputs = c.outputs :=
  rfl

@[simp] theorem Line.mapOp_id (line : Line σ n g) : line.mapOp (Signature.Hom.id σ) = line :=
  rfl

theorem Line.mapOp_comp (ψ : τ.Hom υ) (line : Line σ n g) :
    line.mapOp (ψ.comp φ) = (line.mapOp φ).mapOp ψ :=
  rfl

@[simp] theorem Program.mapOp_id (p : Program σ n g) : p.mapOp (Signature.Hom.id σ) = p := by
  induction p with
  | empty => rfl
  | gate p line ih => rw [mapOp_gate, ih, Line.mapOp_id]

theorem Program.mapOp_comp (ψ : τ.Hom υ) (p : Program σ n g) :
    p.mapOp (ψ.comp φ) = (p.mapOp φ).mapOp ψ := by
  induction p with
  | empty => rfl
  | gate p line ih => rw [mapOp_gate, ih, Line.mapOp_comp, mapOp_gate, mapOp_gate]

@[simp] theorem Circuit.mapOp_id (c : Circuit σ n m) : c.mapOp (Signature.Hom.id σ) = c := by
  simp [Circuit.mapOp]

theorem Circuit.mapOp_comp (ψ : τ.Hom υ) (c : Circuit σ n m) :
    c.mapOp (ψ.comp φ) = (c.mapOp φ).mapOp ψ := by
  simp only [Circuit.mapOp, Program.mapOp_comp]

@[simp] theorem Circuit.size_mapOp (c : Circuit σ n m) : (c.mapOp φ).size = c.size :=
  rfl

/-- A translated line has the same depth. -/
theorem Line.depth_mapOp (line : Line σ n g) (depths : Wire n g → ℕ) :
    (line.mapOp φ).depth depths = line.depth depths :=
  le_antisymm
    ((Line.depth_le_add_one_iff _ _).2 fun _ => (line.depth_le_add_one_iff depths).1 le_rfl _)
    ((Line.depth_le_add_one_iff _ _).2 fun a => by
      simpa using ((line.mapOp φ).depth_le_add_one_iff depths).1 le_rfl
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

/-- The translated program computes the same gate values along a meaning-preserving map. -/
theorem Program.eval_mapOp [hφ : φ.Preserves I J] (p : Program σ n g) (x : Fin n → U) :
    (p.mapOp φ).eval J x = p.eval I x := by
  induction p with
  | empty => funext k; exact k.elim0
  | gate p line ih =>
    funext k
    induction k using Fin.lastCases with
    | last =>
      rw [Program.mapOp, Program.eval_gate_last, Program.eval_gate_last, ih]
      exact hφ.interpret_eq line.op (Wire.elim x (p.eval I x) ∘ line.wires)
    | cast k => rw [Program.mapOp, Program.eval_gate_castSucc, Program.eval_gate_castSucc, ih]

/-- **The translated circuit computes the same function** along a meaning-preserving map. -/
theorem Circuit.eval_mapOp [φ.Preserves I J] (c : Circuit σ n m) (x : Fin n → U) :
    (c.mapOp φ).eval J x = c.eval I x := by
  funext o
  simp only [Circuit.eval, Circuit.mapOp, Function.comp_apply, Program.trace]
  rw [Program.eval_mapOp (I := I)]

/-- A circuit translated along a meaning-preserving map computes what the circuit computes. -/
theorem Circuit.Computes.mapOp [φ.Preserves I J] {c : Circuit σ n m}
    {f : (Fin n → U) → Fin m → U} (hc : c.Computes I f) : (c.mapOp φ).Computes J f :=
  fun x => (Circuit.eval_mapOp c x).trans (hc x)

end Cslib.Circuits
