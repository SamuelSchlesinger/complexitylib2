/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Activation
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Components
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.PendingBias
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases

/-! Tests and axiom guards for mixed-activation, cut, component, block-excess, and pending-bias
bounds. -/

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

-- Concrete pending-bias simulation and state-space bounds on `negatePrior`.
private theorem negatePrior_gateWeight_one_zero : gateWeight negatePrior 1 0 = -1 := by
  change lineWeight (negatePrior.lines (Fin.last 1)) (.gate 0) = -1
  rw [negatePrior, Program.lines_gate_last]
  change (∑ a : Fin 1 with (Wire.gate 0 : Wire 1 2) = Wire.gate 0, (-1 : ℝ)) = -1
  simp

private theorem negatePrior_inputWeight_one (a : Fin 1) : inputWeight negatePrior 1 a = 0 := by
  fin_cases a
  change lineWeight (negatePrior.lines (Fin.last 1)) (.input 0) = 0
  rw [negatePrior, Program.lines_gate_last]
  simp [lineWeight, Wire.Renaming.castSucc]

example (x : Fin 1 → Bool) :
    negatePrior.eval interpretation x 1 =
      decide (gateThreshold negatePrior 1 ≤
        (∑ a : Fin 1, inputWeight negatePrior 1 a * (x a).toNat) +
          pendingBiasTrace negatePrior x 1 ⟨0, by decide⟩) :=
  eval_eq_decide_pendingBiasTrace negatePrior x 1

example : (pendingBiasStates negatePrior 1).card ≤ 2 ^ 1 :=
  card_pendingBiasStates_le_two_pow negatePrior 1

example : (pendingBiasStates negatePrior 1).card ≤ 1 + 1 := by
  refine card_pendingBiasStates_le_add_one_of_row_const negatePrior 1 (fun _ => -1) ?_
  intro i j
  fin_cases i
  fin_cases j
  exact negatePrior_gateWeight_one_zero

example :
    (pendingBiasStates negatePrior 1).card ≤
      (1 + 1 * 1) ^ (Finset.univ : Finset (Fin 1)).card := by
  refine card_pendingBiasStates_le_pow_intWeight negatePrior 1 1 Finset.univ
    (fun _ _ h => funext fun i => h i (Finset.mem_univ i)) (fun _ _ => -1) ?_ (fun _ _ _ => le_rfl)
  intro i _ j
  fin_cases i
  fin_cases j
  simpa using negatePrior_gateWeight_one_zero

example : (Finset.univ.image (intSummary (fun (_ : Fin 1) (_ : Fin 1) => (-1 : ℤ)))).card ≤
    (1 + Fintype.card (Fin 1) * 1) ^ 1 :=
  card_intSummary_le_pow (fun (_ : Fin 1) (_ : Fin 1) => (-1 : ℤ)) (fun _ _ => le_rfl)

example :
    (Finset.univ.image (fun (x : Fin 1 → Bool) (_ : Unit) => !x 0)).card ≤
      (Finset.univ.image (fun x : Fin 1 → Bool => x 0)).card := by
  refine card_rows_le_card_summaries (X := Fin 1 → Bool) (Y := Unit) (α := Bool)
    negatePrior (fun x _ => x) (fun z => z 1) (fun x _ => !x 0)
    (fun x : Fin 1 → Bool => x 0) (fun x _ => negatePrior_eval x) ?_
  intro x₁ x₂ _ h
  have hx : x₁ = x₂ := funext fun i => by fin_cases i; exact h
  rw [hx]

example :
    (Finset.univ.image (fun (x : Fin 1 → Bool) (_ : Unit) => !x 0)).card ≤
      (pendingBiasStates negatePrior 1).card := by
  refine card_rows_le_card_pendingBiasStates_of_phased (X := Fin 1 → Bool) (Y := Unit)
    negatePrior (fun x _ => x) (fun z => z 1)
    (fun x _ => !x 0) 1 () (fun x _ => negatePrior_eval x) (fun _ _ _ _ => rfl) ?_ ?_
  · intro i x₁ x₂ _
    fin_cases i
    change inputSummary negatePrior x₁ 1 = inputSummary negatePrior x₂ 1
    simp [inputSummary, negatePrior_inputWeight_one]
  · intro z₁ z₂ h
    exact h ⟨0, by decide⟩

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.pendingBiasTrace_eq_pendingBias' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.pendingBiasTrace_eq_pendingBias

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.eval_eq_decide_pendingBiasTrace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.eval_eq_decide_pendingBiasTrace

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.card_pendingBiasStates_le_prod_intWeight' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.card_pendingBiasStates_le_prod_intWeight

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.card_pendingBiasStates_le_pow_intWeight' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.card_pendingBiasStates_le_pow_intWeight

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.card_pendingBiasStates_le_add_one_of_row_const' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms card_pendingBiasStates_le_add_one_of_row_const

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.eval_eq_of_inputSummary_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eval_eq_of_inputSummary_eq

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.card_rows_le_card_summaries' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms card_rows_le_card_summaries

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.two_pow_le_card_summaries_of_hadamardCode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms two_pow_le_card_summaries_of_hadamardCode

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.two_pow_le_pow_intSummary_of_hadamardCode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms two_pow_le_pow_intSummary_of_hadamardCode

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.card_rows_le_card_pendingBiasStates_of_phased' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms card_rows_le_card_pendingBiasStates_of_phased

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.two_pow_le_card_pendingBiasStates_of_phased_hadamardCode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms two_pow_le_card_pendingBiasStates_of_phased_hadamardCode

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
