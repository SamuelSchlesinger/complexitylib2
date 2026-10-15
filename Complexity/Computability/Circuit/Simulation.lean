/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Computability/Circuit/Simulation.lean`)

public import Cslib.Computability.Circuit.Simulation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The cost of a program, gate by gate

The cost of a program is the sum of the costs of its lines (`Program.cost_eq_sum`), so a bound on
the cost of every operation bounds the cost of the program by the number of gates
(`Program.cost_le_mul`).
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

end Cslib.Circuits
