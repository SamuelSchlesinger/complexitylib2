/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.WeightedThreshold
import Complexity.Computability.Circuit.Boolean.Threshold.Parity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
Weighted threshold clients: repeated coefficients, nullary gates, native circuit translation,
and the exact boundary for output determinacy.
-/

open Cslib Cslib.Circuits

namespace WeightedThresholdTests

open Boolean.WeightedThreshold

-- Nullary gates use the empty sum; equality is accepted.
example (x : Fin 0 → Bool) : interpretation ⟨0, Fin.elim0, 0⟩ x = true := by
  norm_num [interpretation]

example (x : Fin 0 → Bool) : interpretation ⟨0, Fin.elim0, 1⟩ x = false := by
  norm_num [interpretation]

example (x : Fin 1 → Bool) : interpretation ⟨1, fun _ => 0, 0⟩ x = true := by
  norm_num [interpretation]

-- A negative coefficient implements negation without adding a separate operation.
example (x : Fin 1 → Bool) : interpretation ⟨1, fun _ => -1, 0⟩ x = !x 0 := by
  cases hx : x 0 <;> norm_num [interpretation, hx]

private def cancelLine : Line signature 1 0 :=
  ⟨⟨2, ![3, -3], 0⟩, fun _ => .input 0⟩

private def cancelled : Program signature 1 1 :=
  Program.empty.gate cancelLine

-- Opposite coefficients on repeated occurrences of one wire cancel before counting inputs.
example : lineWeight cancelLine (.input 0) = 0 := by
  dsimp only [lineWeight, cancelLine]
  norm_num [Fin.sum_univ_two]

private theorem cancelled_inputWeight (gate input : Fin 1) :
    inputWeight cancelled gate input = 0 := by
  fin_cases gate; fin_cases input
  change lineWeight ((Program.empty.gate cancelLine).lines (Fin.last 0)) (.input 0) = 0
  rw [Program.lines_gate_last]
  dsimp only [lineWeight, Line.mapWires, cancelLine]
  norm_num [Fin.sum_univ_two]

example : inputGates cancelled = ∅ := by
  ext gate
  simp [cancelled_inputWeight]

example (x : Fin 1 → Bool) : cancelled.eval interpretation x 0 = true := by
  change (Program.empty.gate cancelLine).eval interpretation x (Fin.last 0) = true
  rw [Program.eval_gate_last]
  dsimp only [Line.eval, interpretation, cancelLine, Function.comp_apply, Wire.elim]
  norm_num [Fin.sum_univ_two]

-- Equal coefficients on repeated wires add, rather than being deduplicated.
private def repeated : Line signature 1 0 :=
  ⟨⟨2, ![1, 2], 3⟩, fun _ => .input 0⟩

example : lineWeight repeated (.input 0) = 3 := by
  dsimp only [lineWeight, repeated]
  norm_num [Fin.sum_univ_two]

example (x : Fin 1 → Bool) : repeated.eval interpretation x Fin.elim0 = x 0 := by
  cases hx : x 0 <;>
    dsimp only [repeated, Line.eval, interpretation, Function.comp_apply, Wire.elim] <;>
    norm_num [Fin.sum_univ_two, hx]

private def readInput : Program signature 2 1 :=
  Program.empty.gate ⟨⟨1, fun _ => 1, 1⟩, fun _ => .input 0⟩

private def negatePrior : Program signature 2 2 :=
  readInput.gate ⟨⟨1, fun _ => -1, 0⟩, fun _ => .gate 0⟩

-- This gate is semantically constant, but its direct input coefficient is nonzero.
-- Cancellation with an earlier gate's value does not erase direct input reading.
private def mixed : Program signature 2 3 :=
  negatePrior.gate ⟨⟨2, ![1, -1], 0⟩, ![.input 0, .gate 0]⟩

example : inputGates mixed = {0, 2} := by
  ext gate
  simp only [mem_inputGates]
  fin_cases gate
  · change (∃ i, lineWeight (⟨⟨1, fun _ => 1, 1⟩, fun _ => .input 0⟩ :
        Line signature 2 3) (.input i) ≠ 0) ↔ _
    dsimp only [lineWeight]
    norm_num [Fin.exists_fin_succ]
  · change (∃ i, lineWeight (⟨⟨1, fun _ => -1, 0⟩, fun _ => .gate 0⟩ :
        Line signature 2 3) (.input i) ≠ 0) ↔ _
    dsimp only [lineWeight]
    norm_num
  · change (∃ i, lineWeight ((⟨⟨2, ![1, -1], 0⟩, ![.input 0, .gate 0]⟩ :
        Line signature 2 2).mapWires Wire.Renaming.castSucc) (.input i) ≠ 0) ↔ _
    dsimp only [lineWeight, Line.mapWires]
    norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.exists_fin_succ]

example (x : Fin 2 → Bool) : mixed.eval interpretation x 2 = true := by
  have hread : negatePrior.eval interpretation x 0 = x 0 := by
    change readInput.eval interpretation x (Fin.last 0) = x 0
    rw [readInput, Program.eval_gate_last]
    cases hx : x 0 <;>
      dsimp only [Line.eval, interpretation, Function.comp_apply, Wire.elim] <;>
      norm_num [hx]
  change (negatePrior.gate _).eval interpretation x (Fin.last 2) = true
  rw [Program.eval_gate_last]
  dsimp only [Line.eval, interpretation, Function.comp_apply]
  simp [Fin.sum_univ_two, hread]

example : gateWeight mixed 1 1 = 0 := gateWeight_eq_zero_of_le mixed 1 1 le_rfl
example : gateWeight mixed 1 2 = 0 := gateWeight_eq_zero_of_le mixed 1 2 (by decide)

-- Selected gate outputs may share a gate and omit other gates.
private def gateOutputs : Circuit signature 2 2 :=
  ⟨mixed, fun _ => .gate 1⟩

example {x y : Fin 2 → Bool} (h : transcript mixed x = transcript mixed y) :
    gateOutputs.eval interpretation x = gateOutputs.eval interpretation y :=
  circuit_eval_eq_of_transcript_eq gateOutputs (fun _ => ⟨(1 : Fin 3), rfl⟩) h

-- A free original-input output is a genuine counterexample without the gate-output premise.
example : ∃ x y : Fin 1 → Bool,
    transcript (Circuit.id signature 1).program x =
      transcript (Circuit.id signature 1).program y ∧
    (Circuit.id signature 1).eval interpretation x ≠
      (Circuit.id signature 1).eval interpretation y := by
  refine ⟨fun _ => false, fun _ => true, ?_, ?_⟩
  · funext gate
    exact gate.val.elim0
  · intro h
    exact Bool.false_ne_true (congrFun h 0)

-- Existing threshold circuits translate through CSLib's mapOp; gate count is unchanged.
example (n : ℕ) :
    ((Boolean.Threshold.parityCircuit n).mapOp ofThreshold).size =
      (Boolean.Threshold.parityCircuit n).size :=
  Circuit.size_mapOp _

example (n : ℕ) (x : Fin n → Bool) :
    ((Boolean.Threshold.parityCircuit n).mapOp ofThreshold).eval interpretation x =
      (Boolean.Threshold.parityCircuit n).eval Boolean.Threshold.interpretation x :=
  Circuit.eval_mapOp _ _

end WeightedThresholdTests
