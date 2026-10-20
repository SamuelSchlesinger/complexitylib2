/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.WeightedThreshold.CapacityCircuit
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases

/-! Native weighted-program clients for the scalar-block capacity bound. -/

open Cslib Cslib.Circuits Cslib.Circuits.Boolean.WeightedThreshold

-- Gate-only and nullary operations do not add capacity cost, even when their outputs vary.
private def readInput : Program signature 1 1 :=
  Program.empty.gate ⟨⟨1, fun _ => 1, 1⟩, fun _ => .input 0⟩

private def negatePrior : Program signature 1 2 :=
  readInput.gate ⟨⟨1, fun _ => -1, 0⟩, fun _ => .gate 0⟩

private def withUnused : Program signature 1 3 :=
  negatePrior.gate ⟨⟨0, Fin.elim0, 0⟩, Fin.elim0⟩

private theorem negatePrior_eval (x : Fin 1 → Bool) :
    negatePrior.eval interpretation x 1 = !x 0 := by
  have hread : negatePrior.eval interpretation x 0 = x 0 := by
    change readInput.eval interpretation x (Fin.last 0) = x 0
    rw [readInput, Program.eval_gate_last]
    cases hx : x 0 <;> simp [Line.eval, interpretation, hx]
  change (readInput.gate _).eval interpretation x (Fin.last 1) = !x 0
  rw [Program.eval_gate_last]
  change decide ((0 : ℝ) ≤ ∑ _ : Fin 1, (-1 : ℝ) *
    (negatePrior.eval interpretation x 0).toNat) = !x 0
  rw [hread]
  cases x 0 <;> simp

private theorem withUnused_inputGates : inputGates withUnused = {0} := by
  ext gate
  simp only [mem_inputGates]
  fin_cases gate
  · change (∃ i, lineWeight (⟨⟨1, fun _ => 1, 1⟩, fun _ => .input 0⟩ :
      Line signature 1 3) (.input i) ≠ 0) ↔ _
    simp [lineWeight]
  · change (∃ i, lineWeight (⟨⟨1, fun _ => -1, 0⟩, fun _ => .gate 0⟩ :
      Line signature 1 3) (.input i) ≠ 0) ↔ _
    simp [lineWeight]
  · change (∃ i, lineWeight ((⟨⟨0, Fin.elim0, 0⟩, Fin.elim0⟩ :
      Line signature 1 2).mapWires Wire.Renaming.castSucc) (.input i) ≠ 0) ↔ _
    have hz (i : Fin 1) : lineWeight
        ((⟨⟨0, Fin.elim0, 0⟩, Fin.elim0⟩ : Line signature 1 2).mapWires
          Wire.Renaming.castSucc) (.input i) = 0 :=
      Finset.sum_eq_zero fun a _ => a.elim0
    simp only [hz, ne_eq, not_true_eq_false, exists_false, Finset.mem_singleton]
    decide

example (readout : (Fin 3 → Bool) → Bool) :
    (blockDecomposition withUnused readout).cost = 4 := by
  simp [cost_blockDecomposition, withUnused_inputGates]

example (readout : (Fin 3 → Bool) → Bool) :
    (blockDecomposition withUnused readout).kind 0 = .oneDim 1 ∧
      (blockDecomposition withUnused readout).kind 1 = .oneDim 0 ∧
      (blockDecomposition withUnused readout).kind 2 = .oneDim 0 := by
  simp [blockDecomposition, withUnused_inputGates]

example (x : Fin 1 → Bool) :
    (blockDecomposition withUnused (fun z => z 1)).history 2 x 1 = !x 0 := by
  change (negatePrior.gate _).eval interpretation x (Fin.castSucc 1) = !x 0
  rw [Program.eval_gate_castSucc]
  exact negatePrior_eval x

example (x : Fin 1 → Bool) :
    (blockDecomposition withUnused (fun z => z 1)).history 2 x 2 = false ∧
      (blockDecomposition withUnused (fun z => z 1)).history 3 x 2 = true := by
  constructor
  · rfl
  · change (negatePrior.gate _).eval interpretation x (Fin.last 2) = true
    rw [Program.eval_gate_last]
    simp [Line.eval, interpretation]

private def negateCircuit : Circuit signature 1 1 := ⟨withUnused, fun _ => .gate 1⟩

private theorem negateCircuit_eval (x : Fin 1 → Bool) :
    negateCircuit.eval interpretation x 0 = !x 0 := by
  change (negatePrior.gate _).eval interpretation x (Fin.castSucc 1) = !x 0
  rw [Program.eval_gate_castSucc]
  exact negatePrior_eval x

example : negateCircuit.eval interpretation (fun _ => false) 0 = true ∧
    negateCircuit.eval interpretation (fun _ => true) 0 = false := by
  simp [negateCircuit_eval]

-- Neither color contains a 2-by-2 rectangle on a one-coordinate domain.
private theorem oneBit_rectangleFree (f : (Fin 1 → Bool) → Bool) (b : Bool) :
    Frontier.RectangleFree {x | f x = b} 2 := by
  apply Frontier.rectangleFree_iff.mpr
  intro X A B _
  by_cases h : (0 : Fin 1) ∈ X
  · right
    have hX : X = Set.univ := by ext i; fin_cases i; simp [h]
    subst X
    have : B.ncard ≤ 1 := by simpa using Set.ncard_le_ncard (Set.subset_univ B)
    omega
  · left
    have hX : X = ∅ := by ext i; fin_cases i; simp [h]
    subst X
    have : A.ncard ≤ 1 := by simpa using Set.ncard_le_ncard (Set.subset_univ A)
    omega

example : 2 ^ 1 < 4 * 2 ^ 2 * 4 ^ (inputGates negateCircuit.program).card :=
  circuit_two_pow_lt_mul_four_pow_inputGates negateCircuit ⟨(1 : Fin 3), rfl⟩ negateCircuit_eval
    (oneBit_rectangleFree _)

-- Repeated occurrences cancel before classifying the gate as input-reading.
private def cancelled : Program signature 1 1 :=
  Program.empty.gate ⟨⟨2, ![3, -3], 0⟩, fun _ => .input 0⟩

example (readout : (Fin 1 → Bool) → Bool) :
    (blockDecomposition cancelled readout).cost = 1 := by
  have hzero (gate input : Fin 1) : inputWeight cancelled gate input = 0 := by
    fin_cases gate; fin_cases input
    change lineWeight ((Program.empty.gate _).lines (Fin.last 0)) (.input 0) = 0
    rw [Program.lines_gate_last]
    dsimp only [lineWeight, Line.mapWires]
    norm_num [Fin.sum_univ_two]
  simp [cost_blockDecomposition, inputGates, hzero]

-- An arbitrary nullary threshold has cost one, whether its value is true or false.
example (n : ℕ) (threshold : ℝ) (readout : (Fin 1 → Bool) → Bool) :
    (blockDecomposition (Program.empty.gate
      (⟨⟨0, Fin.elim0, threshold⟩, Fin.elim0⟩ : Line signature n 0)) readout).cost = 1 := by
  rw [cost_blockDecomposition]
  have hzero (gate : Fin 1) (input : Fin n) : inputWeight
      (Program.empty.gate ⟨⟨0, Fin.elim0, threshold⟩, Fin.elim0⟩) gate input = 0 := by
    fin_cases gate
    change lineWeight ((Program.empty.gate _).lines (Fin.last 0)) (.input input) = 0
    rw [Program.lines_gate_last]
    exact Finset.sum_eq_zero fun a _ => a.elim0
  simp [inputGates, hzero]

-- Arbitrary effective gate-only programs have unit cost, including the zero-input case.
example {n g : ℕ} (p : Program signature n g) (readout : (Fin g → Bool) → Bool)
    (h : ∀ gate input, inputWeight p gate input = 0) :
    (blockDecomposition p readout).cost = 1 := by
  simp [cost_blockDecomposition, inputGates, h]

example {g : ℕ} (p : Program signature 0 g) (readout : (Fin g → Bool) → Bool) :
    (blockDecomposition p readout).cost = 1 := by
  simp [cost_blockDecomposition, inputGates]

example (n : ℕ) (readout : (Fin 0 → Bool) → Bool) :
    (blockDecomposition (Program.empty : Program signature n 0) readout).cost = 1 := by
  simp [cost_blockDecomposition, inputGates]

example {g : ℕ} (p : Program signature 0 g) (readout : (Fin g → Bool) → Bool) :
    2 ^ 0 < 4 * 2 ^ 2 * 4 ^ (inputGates p).card := by
  apply two_pow_lt_mul_four_pow_inputGates p readout (fun _ => rfl)
  intro b
  apply Frontier.rectangleFree_iff.mpr
  intro X A B _
  left
  have : A.ncard ≤ 1 := by simpa using Set.ncard_le_ncard (Set.subset_univ A)
  omega

-- Raw-input circuit outputs cannot be represented as a readout of an empty gate vector.
example : ¬ ∃ gate, (Circuit.id signature 1).outputs 0 = .gate gate := by
  rintro ⟨gate, _⟩
  exact gate.elim0

example : ¬ ∃ readout : (Fin 0 → Bool) → Bool, ∀ x : Fin 1 → Bool,
    readout (Program.empty.eval interpretation x) = x 0 := by
  rintro ⟨readout, h⟩
  have hf := h (fun _ => false)
  have ht := h (fun _ => true)
  exact Bool.false_ne_true (hf.symm.trans ht)

-- Piece bounds and direction-run capacity bounds on native programs and circuits.
example {β : Type*} {Φ : ℝ → β} (h : PiecesAtMost Φ 4) : ChangesAtMost Φ 3 :=
  h.changesAtMost

example (x : Fin 1 → Bool) (gate : Fin 3) :
    evalFrom withUnused ∅ (fun _ => false)
      (fun g => ∑ i, inputWeight withUnused g i * (x i).toNat) gate =
      withUnused.eval interpretation x gate :=
  evalFrom_eq_eval withUnused gate (by simp) (fun _ _ _ => rfl)

open scoped Classical in
example (slope : Fin 3 → ℝ) :
    PiecesAtMost (fun t => evalFrom withUnused ∅ (fun _ => false) (fun g => slope g * t))
      (2 ^ (Finset.univ.filter fun g : Fin 3 => g ∉ (∅ : Finset (Fin 3)) ∧ slope g ≠ 0).card) :=
  piecesAtMost_evalFrom withUnused ∅ (fun _ => false) slope

private theorem withUnused_along_one (gate : Fin 3) :
    ∃ c : ℝ, inputWeight withUnused gate = c • (fun _ : Fin 1 => (1 : ℝ)) :=
  ⟨inputWeight withUnused gate 0, by funext i; fin_cases i; simp⟩

private def withUnusedSingleRun : DirectionRuns withUnused 1 :=
  singleRun withUnused (fun _ => 1) withUnused_along_one

example : ∑ i ∈ Finset.range 3, (gateRuns withUnused).size i = 1 := by
  rw [(gateRuns withUnused).sum_size, withUnused_inputGates]
  rfl

example : 1 < 2 * 1 + 2 + 2 * (inputGates negateCircuit.program).card :=
  circuit_lt_two_mul_add_two_mul_inputGates negateCircuit ⟨(1 : Fin 3), rfl⟩ le_rfl
    negateCircuit_eval (oneBit_rectangleFree _)

example : 2 ^ 1 < 16 * 2 ^ 2 * 2 ^ (inputGates negateCircuit.program).card :=
  circuit_two_pow_lt_of_direction negateCircuit ⟨(1 : Fin 3), rfl⟩ (fun _ => 1)
    withUnused_along_one negateCircuit_eval (oneBit_rectangleFree _)

example : 1 < 2 * 1 + 4 + (inputGates negateCircuit.program).card :=
  circuit_lt_of_direction negateCircuit ⟨(1 : Fin 3), rfl⟩ (fun _ => 1)
    withUnused_along_one le_rfl negateCircuit_eval (oneBit_rectangleFree _)

example : 2 ^ 1 < 4 * 2 ^ 2 * 4 ^ 1 * 2 ^ (inputGates negateCircuit.program).card :=
  circuit_two_pow_lt_of_runs negateCircuit ⟨(1 : Fin 3), rfl⟩ withUnusedSingleRun
    negateCircuit_eval (oneBit_rectangleFree _)

example : 1 < 2 * 1 + 2 + 2 * 1 + (inputGates negateCircuit.program).card :=
  circuit_lt_of_runs negateCircuit ⟨(1 : Fin 3), rfl⟩ withUnusedSingleRun le_rfl
    negateCircuit_eval (oneBit_rectangleFree _)

example : 2 ^ 1 < 4 * 2 ^ 2 * max 1 (4 * 0) :=
  two_pow_lt_of_multilevel (f := fun _ : Fin 1 → Bool => false) (K := 2)
    (fun _ => 0) (fun _ => false) (ChangesAtMost.const false) (fun _ => rfl)
    (oneBit_rectangleFree _)

/--
info: 'Cslib.PiecesAtMost.changesAtMost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PiecesAtMost.changesAtMost

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.piecesAtMost_evalFrom' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.piecesAtMost_evalFrom

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_of_direction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_of_direction

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_of_runs' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_of_runs

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.lt_of_runs' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.lt_of_runs

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_of_multilevel' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_of_multilevel

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.two_pow_sub_lt_of_multilevel' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.two_pow_sub_lt_of_multilevel
