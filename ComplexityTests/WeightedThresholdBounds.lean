/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Activation
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Components
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.ScalarActivity
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases

/-! Tests and axiom guards for mixed-activation, cut, component, and block-excess bounds. -/

open Cslib Cslib.Circuits Cslib.Circuits.Boolean.WeightedThreshold

-- A one-input threshold program and circuit computing negation.
private def readInput : Program signature 1 1 :=
  Program.empty.gate ⟨⟨1, fun _ => 1, 1⟩, fun _ => .input 0⟩

private def negatePrior : Program signature 1 2 :=
  readInput.gate ⟨⟨1, fun _ => -1, 0⟩, fun _ => .gate 0⟩

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

private def negateCircuit : Circuit signature 1 1 := ⟨negatePrior, fun _ => .gate 1⟩

private theorem negateCircuit_eval (x : Fin 1 → Bool) :
    negateCircuit.eval interpretation x 0 = !x 0 :=
  negatePrior_eval x

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

-- Weighted threshold circuits translate into `activationSignature` via `mapOp`.
example (x : Fin 1 → Bool) :
    (negateCircuit.mapOp ofWeightedThreshold).eval activationInterpretation x =
      negateCircuit.eval interpretation x :=
  Circuit.eval_mapOp _ _

-- C4: Mixed-activation program and circuit bounds.
private def constActivationCircuit : Circuit activationSignature 1 1 :=
  ⟨Program.empty.gate ⟨⟨1, fun _ => 1, fun _ => false⟩, fun _ => .input 0⟩, fun _ => .gate 0⟩

private theorem constActivationCircuit_eval (x : Fin 1 → Bool) :
    constActivationCircuit.eval activationInterpretation x 0 = false := by
  change (Program.empty.gate _).eval activationInterpretation x (Fin.last 0) = false
  rw [Program.eval_gate_last]
  rfl

private theorem constActivation_changes (j : Fin constActivationCircuit.size) :
    ChangesAtMost (constActivationCircuit.program.lines j).op.activate 0 := by
  fin_cases j
  change ChangesAtMost (fun _ : ℝ => false) 0
  exact ChangesAtMost.const false

example :
    2 ^ 1 < 4 * 2 ^ 2 *
      ∏ _ ∈ activationInputGates constActivationCircuit.program, max 1 (4 * 0) :=
  circuit_two_pow_lt_of_activations constActivationCircuit ⟨(0 : Fin 1), rfl⟩
    (fun _ => 0) (fun j _ => constActivation_changes j)
    constActivationCircuit_eval (oneBit_rectangleFree _)

-- Cut and balanced-cut bounds on `negateCircuit`.
example (U : Finset (Fin 1)) :
    U.card < (Finset.univ.filter fun j =>
      (inputSupport negateCircuit.program j ∩ U).Nonempty).card + 1 ∨
    Uᶜ.card < (Finset.univ.filter fun j =>
      (inputSupport negateCircuit.program j ∩ Uᶜ).Nonempty).card + 1 :=
  circuit_lt_of_split negateCircuit ⟨(1 : Fin 2), rfl⟩ negateCircuit_eval
    (oneBit_rectangleFree _) U (k := 1) le_rfl

example : 1 ≤ 2 * ((inputGates negateCircuit.program).card + 1) :=
  circuit_le_two_mul_add negateCircuit ⟨(1 : Fin 2), rfl⟩ negateCircuit_eval
    (oneBit_rectangleFree _) (k := 1) le_rfl

-- C5: Fan-in-two component bound on `negateCircuit`.
private theorem negateCircuit_support_le_two (j : Fin negateCircuit.size) :
    (inputSupport negateCircuit.program j).card ≤ 2 :=
  le_trans (Finset.card_le_univ _) (by decide)

example : 1 < (inputGates negateCircuit.program).card + 2 * 1 :=
  circuit_lt_of_inputSupport_card_le_two negateCircuit ⟨(1 : Fin 2), rfl⟩
    negateCircuit_eval (oneBit_rectangleFree _) negateCircuit_support_le_two (L := 1) le_rfl

-- C6: Block-excess bound on `negateCircuit` with a single singleton block `{0}` and `F = ∅`.
example : 1 < (∅ : Finset (Fin 1)).card + (inputGates negateCircuit.program).card + 1 + 2 * 1 := by
  refine circuit_lt_of_blocks negateCircuit ⟨(1 : Fin 2), rfl⟩ negateCircuit_eval
    (oneBit_rectangleFree _) ∅ {({0} : Finset (Fin 1))} ?_ ?_ ?_ ?_ 1 ?_ (k := 1) le_rfl
  · simp [Set.PairwiseDisjoint]
  · intro i _
    fin_cases i
    exact ⟨{0}, Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩
  · intro b hb
    simp [Finset.mem_singleton.mp hb]
  · intro j
    right
    refine ⟨{0}, Finset.mem_singleton_self _, ?_⟩
    intro i _
    fin_cases i
    exact Finset.mem_singleton_self _
  · intro b hb
    rw [Finset.mem_singleton.mp hb, Finset.card_singleton]
    omega

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.cost_activationBlockDecomposition' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.cost_activationBlockDecomposition

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_of_activations' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_of_activations

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.circuit_two_pow_lt_of_activations' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.circuit_two_pow_lt_of_activations

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.exists_median' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.exists_median

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.exists_rectangle_of_cut' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.exists_rectangle_of_cut

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.exists_rectangle_of_split' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.exists_rectangle_of_split

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.lt_of_split' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.lt_of_split

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.circuit_lt_of_split' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.circuit_lt_of_split

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.le_two_mul_add' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.le_two_mul_add

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.circuit_le_two_mul_add' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.circuit_le_two_mul_add

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.card_componentInputs_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.card_componentInputs_le

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.exists_split_of_inputSupport_card_le_two' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.exists_split_of_inputSupport_card_le_two

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.lt_of_inputSupport_card_le_two' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.lt_of_inputSupport_card_le_two

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.circuit_lt_of_inputSupport_card_le_two' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.circuit_lt_of_inputSupport_card_le_two

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.lt_of_blocks' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.lt_of_blocks

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.circuit_lt_of_blocks' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.circuit_lt_of_blocks

/-! ### Scalar query-activity run capacity and Cover enumerative coding -/

private theorem negatePrior_along (j : Fin 2) :
    ∃ c : ℝ, inputWeight negatePrior j = c • (fun _ : Fin 1 => (1 : ℝ)) :=
  ⟨inputWeight negatePrior j 0, funext fun i => by fin_cases i; simp⟩

example :
    PiecesAtMost (scalarTranscript negatePrior (fun _ => 1))
      (attainableTranscripts negatePrior).card :=
  piecesAtMost_scalarTranscript negatePrior (fun _ => 1) negatePrior_along

example :
    ChangesAtMost (scalarReadout negatePrior (fun _ => 1) (fun z => z 1))
      ((attainableTranscripts negatePrior).card - 1) :=
  changesAtMost_scalarReadout negatePrior (fun _ => 1) negatePrior_along (fun z => z 1)

example :
    2 ^ 1 < 16 * 2 ^ 2 *
      ∑ j ∈ Finset.range (inputActivity negateCircuit.program + 1),
        (inputGates negateCircuit.program).card.choose j :=
  circuit_two_pow_lt_mul_sum_choose_of_direction negateCircuit ⟨(1 : Fin 2), rfl⟩
    (fun _ => 1) negatePrior_along negateCircuit_eval (oneBit_rectangleFree _)

example :
    2 ^ 1 < 16 * 2 ^ 2 *
      ∑ j ∈ Finset.range (gateActivity negateCircuit.program + 1),
        negateCircuit.size.choose j :=
  circuit_two_pow_lt_mul_sum_choose_gateActivity_of_direction negateCircuit ⟨(1 : Fin 2), rfl⟩
    (fun _ => 1) negatePrior_along negateCircuit_eval (oneBit_rectangleFree _)

example (z : Fin 3 → Bool) :
    coverDecode 3 3 (coverRank 3 z) = z :=
  coverDecode_coverRank z (by simpa using BitString.weight_le z)

example (t : ℕ) (ht : t < ballSize 3 2) :
    coverRank 2 (coverDecode 3 2 t) = t ∧ BitString.weight (coverDecode 3 2 t) ≤ 2 :=
  ⟨coverRank_coverDecode ht, weight_coverDecode_le 3 2 t⟩

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.eval_eq_of_scalarScore_between' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eval_eq_of_scalarScore_between

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.transcript_eq_of_scalarScore_between' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms transcript_eq_of_scalarScore_between

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.piecesAtMost_scalarTranscript' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms piecesAtMost_scalarTranscript

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.piecesAtMost_scalarReadout' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms piecesAtMost_scalarReadout

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.changesAtMost_scalarReadout' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms changesAtMost_scalarReadout

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.length_le_card_attainableTranscripts_of_isChain' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms length_le_card_attainableTranscripts_of_isChain

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.length_le_sum_choose_of_isChain' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms length_le_sum_choose_of_isChain

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.length_le_sum_choose_gateActivity_of_isChain' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms length_le_sum_choose_gateActivity_of_isChain

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_mul_max_card_attainableTranscripts_of_direction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms two_pow_lt_mul_max_card_attainableTranscripts_of_direction

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_mul_card_attainableTranscripts_of_direction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms two_pow_lt_mul_card_attainableTranscripts_of_direction

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_mul_sum_choose_of_direction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms two_pow_lt_mul_sum_choose_of_direction

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_mul_sum_choose_gateActivity_of_direction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms two_pow_lt_mul_sum_choose_gateActivity_of_direction

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.circuit_two_pow_lt_mul_sum_choose_of_direction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms circuit_two_pow_lt_mul_sum_choose_of_direction

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.circuit_two_pow_lt_mul_sum_choose_gateActivity_of_direction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms circuit_two_pow_lt_mul_sum_choose_gateActivity_of_direction

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.coverRank_lt_ballSize' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms coverRank_lt_ballSize

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.weight_coverDecode_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms weight_coverDecode_le

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.coverRank_coverDecode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms coverRank_coverDecode

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.coverDecode_coverRank' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms coverDecode_coverRank
