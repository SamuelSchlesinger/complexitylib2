/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Pointwise
import Complexity.Computability.Circuit.Boolean.Synthesis
import Mathlib.Tactic.FinCases

/-! Truth tables of small De Morgan circuits under the pointwise lift, on two and three inputs,
with zero inputs and with an empty set of points; the costs of projections and the one-gate lower
bound on two and three inputs. -/

namespace ComplexityTests.CircuitHamming.Pointwise

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

/-! ### The lift and evaluation at a point -/

/-- Conjunction of two functions, lifted pointwise. -/
example (f g : Bool → Bool) :
    interpretation.pointwise Bool .and ![f, g] = fun b => f b && g b :=
  rfl

/-- Evaluation at `true` sends the lifted negation of `id` to `false`. -/
example : (interpretation.evalAt true).map (interpretation.pointwise Bool .not ![id]) = false :=
  rfl

/-! ### Two inputs -/

/-- NAND on two inputs: a conjunction followed by a negation. -/
private def nand : Circuit signature 2 1 :=
  ⟨.gate (.gate .empty ⟨.and, fun a => .input a⟩) ⟨.not, fun _ => .gate 0⟩, fun _ => .gate 1⟩

/-- The lifted output of `nand` at the projections is the truth table of NAND. -/
example : nand.eval (interpretation.pointwise (BitString 2)) (fun j x => x j) 0 =
    fun x => !(x 0 && x 1) := by
  rw [Circuit.eval_pointwise_proj]
  rfl

/-- The same truth table, checked value by value. -/
example : nand.eval (interpretation.pointwise (BitString 2)) (fun j x => x j) 0 ![true, true] =
    false ∧
    nand.eval (interpretation.pointwise (BitString 2)) (fun j x => x j) 0 ![true, false] =
      true := by
  decide

/-- Wires carry truth tables: the first gate carries the conjunction. -/
example : nand.program.trace (interpretation.pointwise (BitString 2)) (fun j x => x j)
    (.gate ⟨0, by decide⟩) = fun x => x 0 && x 1 := by
  rw [Program.trace_pointwise_proj]
  rfl

/-- Inputs need not be projections: lifted to the points of `Bool` with inputs `id` and `not`,
the conjunction gate is constantly `false`. -/
example (b : Bool) :
    nand.program.trace (interpretation.pointwise Bool) ![id, not] (.gate ⟨0, by decide⟩) b =
      false := by
  rw [Program.trace_pointwise_apply]
  cases b <;> rfl

/-- The conjunction is available in `nand`. -/
example : (fun x : BitString 2 => x 0 && x 1) ∈ available interpretation nand.program := by
  rw [available_eq_range_trace_pointwise]
  exact ⟨.gate ⟨0, by decide⟩, rfl⟩

/-- `nand` computes NAND, read off its lifted evaluation. -/
example : nand.Computes interpretation (single fun x => !(x 0 && x 1)) := by
  rw [Circuit.computes_iff_eval_pointwise_proj]
  rfl

/-- `nand` does not compute the conjunction: the truth tables differ. -/
example : ¬nand.Computes interpretation (single fun x => x 0 && x 1) := by
  rw [Circuit.computes_iff_eval_pointwise_proj]
  intro h
  have := congrFun (congrFun h 0) ![true, true]
  exact absurd this (by decide)

/-! ### Three inputs -/

/-- A chain of two conjunctions on three inputs. -/
private def and3 : Circuit signature 3 1 :=
  ⟨.gate (.gate .empty ⟨.and, ![.input 0, .input 1]⟩) ⟨.and, ![.gate 0, .input 2]⟩,
    fun _ => .gate 1⟩

example : and3.eval (interpretation.pointwise (BitString 3)) (fun j x => x j) 0 =
    fun x => x 0 && x 1 && x 2 := by
  rw [Circuit.eval_pointwise_proj]
  rfl

example : and3.Computes interpretation (single fun x => x 0 && x 1 && x 2) := by
  rw [Circuit.computes_iff_eval_pointwise_proj]
  rfl

/-! ### Boundary cases -/

/-- The constant `true` on zero inputs. -/
private def trueConst : Circuit signature 0 1 :=
  ⟨.gate .empty ⟨.const true, Fin.elim0⟩, fun _ => .gate 0⟩

/-- With zero inputs there are no projections; the truth table is a single value. -/
example : trueConst.eval (interpretation.pointwise (BitString 0)) Fin.elim0 0 = fun _ => true :=
  Circuit.eval_pointwise_proj trueConst interpretation 0 ▸ rfl

example : trueConst.Computes interpretation (single fun _ => true) :=
  (Circuit.computes_iff_eval_pointwise_proj _ _ _).2 rfl

/-- Over an empty set of points every lifted value is the empty function. -/
example (a : Fin 2 → Empty → Bool) :
    nand.eval (interpretation.pointwise Empty) a 0 = Empty.elim :=
  funext fun e => e.elim

/-! ### Projections and the first gate -/

example : complexity interpretation (single fun x : BitString 2 => x 1) = 0 :=
  complexity_single_proj 1

example : complexity interpretation (single fun x : BitString 3 => x 2) = 0 :=
  complexity_single_proj 2

/-- The conjunction of two inputs costs exactly one gate. -/
example : complexity interpretation (single fun x : BitString 2 => x 0 && x 1) = 1 := by
  refine le_antisymm ?_ (one_le_complexity_single fun i h => ?_)
  · have h := complexity_and_le (fun x : BitString 2 => x 0) fun x => x 1
    rw [complexity_single_proj, complexity_single_proj] at h
    exact h
  · fin_cases i
    · exact absurd (congrFun h ![true, false]) (by decide)
    · exact absurd (congrFun h ![false, true]) (by decide)

/-- The conjunction of three inputs needs at least one gate. -/
example : 1 ≤ complexity interpretation (single fun x : BitString 3 => x 0 && x 1 && x 2) :=
  one_le_complexity_single fun i h => by
    fin_cases i
    · exact absurd (congrFun h ![true, false, false]) (by decide)
    · exact absurd (congrFun h ![false, true, false]) (by decide)
    · exact absurd (congrFun h ![false, false, true]) (by decide)

/-! ### Axioms -/

/--
info: 'Cslib.Circuits.Program.trace_pointwise_proj' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Program.trace_pointwise_proj

/--
info: 'Cslib.Circuits.available_eq_range_trace_pointwise' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms available_eq_range_trace_pointwise

/--
info: 'Cslib.Circuits.Circuit.eval_pointwise_proj' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Circuit.eval_pointwise_proj

/--
info: 'Cslib.Circuits.Circuit.computes_iff_eval_pointwise_proj' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Circuit.computes_iff_eval_pointwise_proj

/--
info: 'Cslib.Circuits.complexity_single_proj' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms complexity_single_proj

/--
info: 'Cslib.Circuits.one_le_complexity_single' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms one_le_complexity_single

end ComplexityTests.CircuitHamming.Pointwise
