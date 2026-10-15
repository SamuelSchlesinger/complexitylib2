/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Formula
public import Complexity.Computability.Circuit.Pi

/-!
# Formulas as circuits

A formula is a circuit whose gates each feed one other gate. `Formula.toCircuit` lays out the
operation nodes of a formula as gates, an input leaf becoming a wire: the circuit computes the same
function (`Formula.eval_toCircuit`), has one gate per operation node (`Formula.size_toCircuit`), and
is no deeper (`Formula.depth_toCircuit_le`). So lower bounds on circuit size are lower bounds on
formula size.

## Main definitions

* `Cslib.Circuits.Formula.toCircuit`: a formula as a single-output circuit.

## Main results

* `Cslib.Circuits.Formula.computes_toCircuit`: the circuit computes what the formula computes.
* `Cslib.Circuits.Formula.size_toCircuit`, `Cslib.Circuits.Formula.depth_toCircuit_le`: it has the
  size of the formula and at most its depth.
-/

@[expose] public section

namespace Cslib.Circuits.Formula

variable {σ : Signature} {n : ℕ} {U : Type*}

/-- A formula as a circuit: an input leaf is a wire, and an operation node is a gate on the
circuits of its arguments, side by side. -/
def toCircuit : Formula σ n → Circuit σ n 1
  | input i => Circuit.wiring σ fun _ => i
  | gate op args => (Circuit.oneGate op id).comp (Circuit.pi fun a => (args a).toCircuit)

@[simp] theorem eval_toCircuit (I : Interpretation σ U) (F : Formula σ n) (x : Fin n → U)
    (j : Fin 1) : F.toCircuit.eval I x j = F.eval I x := by
  induction F generalizing j with
  | input i => rfl
  | gate op args ih =>
    rw [toCircuit, Circuit.eval_comp, Circuit.eval_oneGate, Circuit.eval_pi, eval_gate]
    exact congrArg (I op) (funext fun a => ih a 0)

theorem computes_toCircuit {I : Interpretation σ U} {F : Formula σ n} {f : (Fin n → U) → U}
    (hF : F.Computes I f) : F.toCircuit.Computes I (Circuits.single f) := fun x => by
  funext j
  rw [eval_toCircuit, computes_iff.1 hF]
  rfl

@[simp] theorem size_toCircuit (F : Formula σ n) : F.toCircuit.size = F.size := by
  induction F with
  | input i => rfl
  | gate op args ih =>
    rw [toCircuit, Circuit.size_comp, Circuit.size_pi, Circuit.size_oneGate, size_gate]
    simp only [ih]

theorem depth_toCircuit_le (F : Formula σ n) : F.toCircuit.depth ≤ F.depth := by
  induction F with
  | input i => simp [toCircuit]
  | gate op args ih =>
    rw [toCircuit, depth_gate, add_comm]
    exact (Circuit.depth_comp_le _ _).trans (Nat.add_le_add (Circuit.depth_oneGate_le _ _)
      (Circuit.depth_pi_le _ fun a => (ih a).trans (Finset.le_sup (f := fun a => (args a).depth)
        (Finset.mem_univ a))))

end Cslib.Circuits.Formula
