/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Computability/Circuit/Simulation.lean`)

public import Complexity.Computability.Circuit.Pi
public import Cslib.Computability.Circuit.Simulation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The cost of a program, gate by gate

The cost of a program is the sum of the costs of its lines (`Program.cost_eq_sum`), so a bound on
the cost of every operation bounds the cost of the program by the number of gates
(`Program.cost_le_mul`). Costs add up along the composition of circuits
(`Circuit.cost_program_comp`, `Circuit.cost_program_append`, `Circuit.cost_program_pi`).
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {n g : ℕ}

/-- The cost of a program is the sum of the costs of its lines. -/
theorem Program.cost_eq_sum (p : Program σ n g) (cost : σ.Op → ℕ) :
    p.cost cost = ∑ k, cost (p.lines k).op := by
  induction p with
  | empty => simp
  | gate p line ih =>
    rw [Program.cost_gate, ih, Fin.sum_univ_castSucc]
    simp [Program.lines_gate_last, Program.lines_gate_castSucc]

/-- If every operation costs at most `b`, a program with `g` gates costs at most `b * g`. -/
theorem Program.cost_le_mul (p : Program σ n g) {cost : σ.Op → ℕ} {b : ℕ}
    (h : ∀ op, cost op ≤ b) : p.cost cost ≤ b * g :=
  (p.cost_mono h).trans_eq (p.cost_const b)

/-- Continuing a program adds the costs. -/
@[simp] theorem Program.cost_append {k g₂ : ℕ} (p : Program σ n g) (feed : Fin k → Wire n g)
    (q : Program σ k g₂) (cost : σ.Op → ℕ) :
    (p.append feed q).cost cost = p.cost cost + q.cost cost := by
  induction q with
  | empty => rfl
  | gate q line ih => rw [Program.append, Program.cost_gate, Program.cost_gate, ih,
      Line.mapWires_op, Nat.add_assoc]

namespace Circuit

/-! The costs of circuits built from smaller ones. They are not `simp` lemmas: `simp` would first
rewrite the number of gates, an implicit argument of `Program.cost`, by `Circuit.size_comp` and the
like, after which they no longer match. They apply with `rw` and `simp only`. -/

variable {m p : ℕ}

theorem cost_program_wiring (select : Fin m → Fin n) (cost : σ.Op → ℕ) :
    (Circuit.wiring σ select).program.cost cost = 0 :=
  rfl

theorem cost_program_oneGate (op : σ.Op) (args : Fin (σ.Arity op) → Fin n)
    (cost : σ.Op → ℕ) : (oneGate op args).program.cost cost = cost op :=
  Nat.zero_add _

/-- Sequential composition adds the costs. -/
theorem cost_program_comp (d : Circuit σ m p) (c : Circuit σ n m) (cost : σ.Op → ℕ) :
    (d.comp c).program.cost cost = c.program.cost cost + d.program.cost cost :=
  Program.cost_append _ _ _ cost

/-- Parallel composition adds the costs. -/
theorem cost_program_append (c : Circuit σ n m) (d : Circuit σ n p) (cost : σ.Op → ℕ) :
    (c.append d).program.cost cost = c.program.cost cost + d.program.cost cost :=
  Program.cost_append _ _ _ cost

/-- The cost of `pi cs` is the sum of the costs. -/
theorem cost_program_pi (cs : Fin m → Circuit σ n 1) (cost : σ.Op → ℕ) :
    (pi cs).program.cost cost = ∑ j, (cs j).program.cost cost := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pi, cost_program_append, ih, Fin.sum_univ_castSucc]

end Circuit

end Cslib.Circuits
