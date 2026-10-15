/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Circuit/Depth.lean`)

public import Cslib.Computability.Circuit.Depth

/-!
# Depths along program lines, and depths with costs

Every wire read by a gate is shallower than the gate (`Program.wireDepths_lines_lt`), which is what
makes induction on depth go through for programs.

The depth with costs (`Circuit.depthWith cost`) charges `cost op` for a gate of operation `op`
instead of one, so it is the largest total cost of the gates on a path to an output. Unit costs
give `Circuit.depth` (`Circuit.depthWith_one`). With free negations it is the largest number of
AND and OR gates on a path in a circuit over the unbounded fan-in basis, the depth of AC⁰ circuits
with negations at the inputs.

## Main definitions

* `Cslib.Circuits.Line.depthWith`, `Cslib.Circuits.Program.depthsWith`,
  `Cslib.Circuits.Program.wireDepthsWith`, `Cslib.Circuits.Circuit.depthWith`: depths with costs.

## Main results

* `Cslib.Circuits.Program.depths_eq_depth_lines`: the depth of a gate is the depth of its line.
* `Cslib.Circuits.Program.wireDepths_lines_lt`: the wires a gate reads are shallower than it.
* `Cslib.Circuits.Program.depths_pos`: gates have positive depth.
* `Cslib.Circuits.Program.wireDepthsWith_lines_add_le`: with costs, the wires a gate reads are
  shallower than it by at least its cost.
* `Cslib.Circuits.Circuit.depthWith_one`: unit costs give the depth.
* `Cslib.Circuits.Circuit.depthWith_le_iff`, `Cslib.Circuits.Circuit.depthWith_mono`: bounds, and
  monotonicity in the costs.
* `Cslib.Circuits.Circuit.depthWith_le_depth`: costs of at most one never increase the depth.
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

/-- The depth of a gate of a program is the depth of its line, over the depths of the wires. -/
theorem Program.depths_eq_depth_lines (p : Program σ n g) (k : Fin g) :
    p.depths k = (p.lines k).depth p.wireDepths := by
  induction p with
  | empty => exact k.elim0
  | @gate g p line ih =>
    have h : (fun w => (p.gate line).wireDepths (Wire.Renaming.castSucc w)) = p.wireDepths :=
      funext fun w => by rw [Wire.Renaming.castSucc_apply, Program.wireDepths_gate_castSucc]
    induction k using Fin.lastCases with
    | last =>
      rw [Program.lines_gate_last, Program.depths_gate_last]
      exact congrArg line.depth h.symm
    | cast k =>
      rw [Program.lines_gate_castSucc, Program.depths_gate_castSucc, ih]
      exact congrArg (p.lines k).depth h.symm

/-- The wires read by a gate of a program are shallower than the gate. -/
theorem Program.wireDepths_lines_lt (p : Program σ n g) (k : Fin g)
    (a : Fin (σ.Arity (p.lines k).op)) : p.wireDepths ((p.lines k).wires a) < p.depths k :=
  p.depths_eq_depth_lines k ▸ (p.lines k).wireDepth_lt_depth _ a

/-- Every gate of a program has positive depth. -/
theorem Program.depths_pos (p : Program σ n g) (k : Fin g) : 0 < p.depths k :=
  p.depths_eq_depth_lines k ▸ (p.lines k).depth_pos _

/-! ### Depth with costs

The depth of a wire when each operation `op` costs `cost op` instead of one: the largest total
cost of the gates on a path to the wire. With negations costing nothing, it is the largest number
of AND and OR gates on a path, the depth of AC⁰ circuits with negations at the inputs. -/

private theorem foldl_max_le_iff {m : ℕ} (f : Fin m → ℕ) (initial bound : ℕ) :
    Fin.foldl m (fun acc i => max acc (f i)) initial ≤ bound ↔
      initial ≤ bound ∧ ∀ i, f i ≤ bound := by
  induction m generalizing initial with
  | zero => simp
  | succ m ih =>
    rw [Fin.foldl_succ, ih]
    simp [Fin.forall_fin_succ, and_assoc]

private theorem le_foldl_max {m : ℕ} (f : Fin m → ℕ) (initial : ℕ) (j : Fin m) :
    f j ≤ Fin.foldl m (fun acc i => max acc (f i)) initial :=
  ((foldl_max_le_iff f initial _).1 le_rfl).2 j

/-- The depth of a line when its operation costs `cost op`. -/
def Line.depthWith (cost : σ.Op → ℕ) (line : Line σ n g) (wireDepths : Wire n g → ℕ) : ℕ :=
  Fin.foldl (σ.Arity line.op) (fun depth k => max depth (wireDepths (line.wires k))) 0 +
    cost line.op

/-- A line is at least as deep as its cost. -/
theorem Line.cost_le_depthWith (cost : σ.Op → ℕ) (line : Line σ n g) (depths : Wire n g → ℕ) :
    cost line.op ≤ line.depthWith cost depths :=
  Nat.le_add_left _ _

/-- A line is at least as deep as every wire it reads plus its cost. -/
theorem Line.wireDepth_add_le_depthWith (cost : σ.Op → ℕ) (line : Line σ n g)
    (depths : Wire n g → ℕ) (a : Fin (σ.Arity line.op)) :
    depths (line.wires a) + cost line.op ≤ line.depthWith cost depths := by
  unfold Line.depthWith
  have : depths (line.wires a) ≤
      Fin.foldl (σ.Arity line.op) (fun depth k => max depth (depths (line.wires k))) 0 :=
    le_foldl_max (fun k => depths (line.wires k)) 0 a
  omega

private theorem foldl_max_mono {m : ℕ} {f f' : Fin m → ℕ} (h : ∀ i, f i ≤ f' i) :
    Fin.foldl m (fun acc i => max acc (f i)) 0 ≤ Fin.foldl m (fun acc i => max acc (f' i)) 0 :=
  (foldl_max_le_iff f 0 _).2 ⟨Nat.zero_le _, fun i => (h i).trans (le_foldl_max f' 0 i)⟩

/-- With unit costs, `Line.depthWith` is `Line.depth`. -/
@[simp] theorem Line.depthWith_one (line : Line σ n g) (depths : Wire n g → ℕ) :
    line.depthWith 1 depths = line.depth depths := by
  simp only [Line.depthWith, Line.depth, Pi.one_apply]
  omega

/-- Raising the depths of the wires by at most `D` raises the depth of a line by at most `D`. -/
theorem Line.depthWith_le_add (cost : σ.Op → ℕ) (line : Line σ n g) {depths depths' : Wire n g → ℕ}
    {D : ℕ} (h : ∀ a, depths (line.wires a) ≤ depths' (line.wires a) + D) :
    line.depthWith cost depths ≤ line.depthWith cost depths' + D := by
  have : Fin.foldl (σ.Arity line.op) (fun depth k => max depth (depths (line.wires k))) 0 ≤
      Fin.foldl (σ.Arity line.op) (fun depth k => max depth (depths' (line.wires k))) 0 + D :=
    (foldl_max_le_iff _ 0 _).2 ⟨Nat.zero_le _, fun a =>
      (h a).trans (Nat.add_le_add_right (le_foldl_max (fun k => depths' (line.wires k)) 0 a) _)⟩
  unfold Line.depthWith
  omega

/-- A line reading only wires of depth zero has the depth of its cost. -/
theorem Line.depthWith_eq_cost (cost : σ.Op → ℕ) (line : Line σ n g) {depths : Wire n g → ℕ}
    (h : ∀ a, depths (line.wires a) = 0) : line.depthWith cost depths = cost line.op := by
  have : Fin.foldl (σ.Arity line.op) (fun depth k => max depth (depths (line.wires k))) 0 ≤ 0 :=
    (foldl_max_le_iff _ 0 0).2 ⟨le_rfl, fun a => (h a).le⟩
  unfold Line.depthWith
  omega

/-- `Line.depthWith` is monotone in the costs and in the depths of the wires. -/
theorem Line.depthWith_mono {cost cost' : σ.Op → ℕ} (hcost : ∀ op, cost op ≤ cost' op)
    {depths depths' : Wire n g → ℕ} (hdepths : ∀ w, depths w ≤ depths' w) (line : Line σ n g) :
    line.depthWith cost depths ≤ line.depthWith cost' depths' :=
  Nat.add_le_add (foldl_max_mono fun _ => hdepths _) (hcost _)

/-- The depth of every gate of a program when each operation `op` costs `cost op`. -/
def Program.depthsWith (cost : σ.Op → ℕ) {g : ℕ} : Program σ n g → Fin g → ℕ
  | .empty => Fin.elim0
  | .gate p line =>
    Fin.lastCases (line.depthWith cost (Wire.elim (fun _ => 0) (p.depthsWith cost)))
      (p.depthsWith cost)

/-- The depth of every wire of a program when each operation `op` costs `cost op`. -/
def Program.wireDepthsWith (cost : σ.Op → ℕ) (p : Program σ n g) : Wire n g → ℕ :=
  Wire.elim (fun _ => 0) (p.depthsWith cost)

@[simp] theorem Program.wireDepthsWith_input (cost : σ.Op → ℕ) (p : Program σ n g) (i : Fin n) :
    p.wireDepthsWith cost (.input i) = 0 := rfl

@[simp] theorem Program.wireDepthsWith_gateWire (cost : σ.Op → ℕ) (p : Program σ n g) (k : Fin g) :
    p.wireDepthsWith cost (.gate k) = p.depthsWith cost k := rfl

@[simp] theorem Program.depthsWith_gate_last (cost : σ.Op → ℕ) (p : Program σ n g)
    (line : Line σ n g) :
    (p.gate line).depthsWith cost (Fin.last g) = line.depthWith cost (p.wireDepthsWith cost) := by
  simp [Program.depthsWith, Program.wireDepthsWith]

@[simp] theorem Program.depthsWith_gate_castSucc (cost : σ.Op → ℕ) (p : Program σ n g)
    (line : Line σ n g) (j : Fin g) :
    (p.gate line).depthsWith cost j.castSucc = p.depthsWith cost j := by
  simp [Program.depthsWith]

@[simp] theorem Program.wireDepthsWith_gate_castSucc (cost : σ.Op → ℕ) (p : Program σ n g)
    (line : Line σ n g) (w : Wire n g) :
    (p.gate line).wireDepthsWith cost w.castSucc = p.wireDepthsWith cost w := by
  cases w <;> simp

/-- The depth of a gate is the depth of its line over the depths of the wires. -/
theorem Program.depthsWith_eq_depthWith_lines (cost : σ.Op → ℕ) (p : Program σ n g) (k : Fin g) :
    p.depthsWith cost k = (p.lines k).depthWith cost (p.wireDepthsWith cost) := by
  induction p with
  | empty => exact k.elim0
  | @gate g p line ih =>
    have h : (fun w => (p.gate line).wireDepthsWith cost (Wire.Renaming.castSucc w)) =
        p.wireDepthsWith cost :=
      funext fun w => by
        rw [Wire.Renaming.castSucc_apply, Program.wireDepthsWith_gate_castSucc]
    induction k using Fin.lastCases with
    | last =>
      rw [Program.lines_gate_last, Program.depthsWith_gate_last]
      exact congrArg (line.depthWith cost) h.symm
    | cast k =>
      rw [Program.lines_gate_castSucc, Program.depthsWith_gate_castSucc, ih]
      exact congrArg ((p.lines k).depthWith cost) h.symm

/-- A gate is at least as deep as its cost. -/
theorem Program.cost_le_depthsWith (cost : σ.Op → ℕ) (p : Program σ n g) (k : Fin g) :
    cost (p.lines k).op ≤ p.depthsWith cost k :=
  p.depthsWith_eq_depthWith_lines cost k ▸ (p.lines k).cost_le_depthWith cost _

/-- With unit costs, `Program.depthsWith` is `Program.depths`. -/
@[simp] theorem Program.depthsWith_one (p : Program σ n g) :
    p.depthsWith 1 = p.depths := by
  induction p with
  | empty => exact funext fun k => k.elim0
  | @gate g p line ih =>
    have hw : p.wireDepthsWith 1 = p.wireDepths := by
      funext w; cases w <;> simp [ih, Program.wireDepths]
    funext k
    induction k using Fin.lastCases with
    | last => simp [hw]
    | cast k => simp [ih]

/-- With unit costs, `Program.wireDepthsWith` is `Program.wireDepths`. -/
@[simp] theorem Program.wireDepthsWith_one (p : Program σ n g) :
    p.wireDepthsWith 1 = p.wireDepths := by
  simp [Program.wireDepthsWith, Program.wireDepths]

/-- `Program.depthsWith` is monotone in the costs. -/
theorem Program.depthsWith_mono {cost cost' : σ.Op → ℕ} (hcost : ∀ op, cost op ≤ cost' op)
    (p : Program σ n g) (k : Fin g) : p.depthsWith cost k ≤ p.depthsWith cost' k := by
  induction p with
  | empty => exact k.elim0
  | @gate g p line ih =>
    have hw : ∀ w, p.wireDepthsWith cost w ≤ p.wireDepthsWith cost' w := fun w => by
      cases w <;> simp [ih]
    induction k using Fin.lastCases with
    | last => simpa using line.depthWith_mono hcost hw
    | cast k => simpa using ih k

/-- `Program.wireDepthsWith` is monotone in the costs. -/
theorem Program.wireDepthsWith_mono {cost cost' : σ.Op → ℕ} (hcost : ∀ op, cost op ≤ cost' op)
    (p : Program σ n g) (w : Wire n g) : p.wireDepthsWith cost w ≤ p.wireDepthsWith cost' w := by
  cases w <;> simp [p.depthsWith_mono hcost]

/-- The wires read by a gate are shallower than the gate by at least its cost. -/
theorem Program.wireDepthsWith_lines_add_le (cost : σ.Op → ℕ) (p : Program σ n g) (k : Fin g)
    (a : Fin (σ.Arity (p.lines k).op)) :
    p.wireDepthsWith cost ((p.lines k).wires a) + cost (p.lines k).op ≤ p.depthsWith cost k :=
  p.depthsWith_eq_depthWith_lines cost k ▸ (p.lines k).wireDepth_add_le_depthWith cost _ a

/-- The largest depth of an output when each operation `op` costs `cost op`. -/
def Circuit.depthWith (cost : σ.Op → ℕ) {m : ℕ} (c : Circuit σ n m) : ℕ :=
  Fin.foldl m (fun depth k => max depth (c.program.wireDepthsWith cost (c.outputs k))) 0

/-- A circuit has depth at most `D` with costs exactly when all its outputs do. -/
theorem Circuit.depthWith_le_iff (cost : σ.Op → ℕ) {m : ℕ} (c : Circuit σ n m) {D : ℕ} :
    c.depthWith cost ≤ D ↔ ∀ j, c.program.wireDepthsWith cost (c.outputs j) ≤ D := by
  simpa [Circuit.depthWith] using foldl_max_le_iff _ 0 D

theorem Circuit.wireDepthsWith_outputs_le_depthWith (cost : σ.Op → ℕ) {m : ℕ}
    (c : Circuit σ n m) (j : Fin m) :
    c.program.wireDepthsWith cost (c.outputs j) ≤ c.depthWith cost :=
  le_foldl_max (fun k => c.program.wireDepthsWith cost (c.outputs k)) 0 j

/-- With unit costs, `Circuit.depthWith` is `Circuit.depth`. -/
@[simp] theorem Circuit.depthWith_one {m : ℕ} (c : Circuit σ n m) :
    c.depthWith 1 = c.depth := by
  simp [Circuit.depthWith, Circuit.depth, Circuit.outputDepths]

/-- `Circuit.depthWith` is monotone in the costs. -/
theorem Circuit.depthWith_mono {cost cost' : σ.Op → ℕ} (hcost : ∀ op, cost op ≤ cost' op)
    {m : ℕ} (c : Circuit σ n m) : c.depthWith cost ≤ c.depthWith cost' :=
  foldl_max_mono fun _ => c.program.wireDepthsWith_mono hcost _

@[simp] theorem Circuit.depthWith_wiring (cost : σ.Op → ℕ) {m : ℕ} (select : Fin m → Fin n) :
    (Circuit.wiring σ select).depthWith cost = 0 :=
  Nat.eq_zero_of_le_zero <| (Circuit.depthWith_le_iff cost _).2 fun _ => le_rfl

@[simp] theorem Circuit.depthWith_zero_outputs (cost : σ.Op → ℕ) (c : Circuit σ n 0) :
    c.depthWith cost = 0 :=
  rfl

/-- Costs of at most one never increase the depth. -/
theorem Circuit.depthWith_le_depth {cost : σ.Op → ℕ} (hcost : ∀ op, cost op ≤ 1) {m : ℕ}
    (c : Circuit σ n m) : c.depthWith cost ≤ c.depth :=
  c.depthWith_one ▸ c.depthWith_mono hcost

end Cslib.Circuits
