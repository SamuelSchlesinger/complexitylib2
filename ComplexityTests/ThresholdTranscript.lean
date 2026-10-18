/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.WeightedThreshold.TranscriptTree
import Complexity.Computability.DecisionTree.Observations
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
Transcript-tree clients: noninjective observations, zero input coordinates, cancelled repeated
wires, unattainable activation patterns, and a comparison tree computing a nonconstant circuit.
-/

open Cslib Cslib.Circuits Finset
open Cslib.Circuits.Boolean.WeightedThreshold

namespace ThresholdTranscriptTests

-- Four inputs but only two observation vectors; the unused coordinate is not charged.
example : ∃ t : DecisionTree Unit Bool,
    (∀ x : Bool × Bool, t.eval (fun _ => x.1) = x.1) ∧ t.depth ≤ 1 ∧ t.leafCount ≤ 2 := by
  classical
  obtain ⟨t, ht, hd, hl⟩ := DecisionTree.exists_of_observations (univ : Finset (Bool × Bool))
    univ_nonempty (fun x (_ : Unit) => x.1) (fun (_ : Unit) x => x.1) Prod.fst
    (fun _ _ _ _ h => congrFun h ()) (by
      intro S _ _ hne
      obtain ⟨x, hx, y, hy, hxy⟩ := hne
      refine ⟨(), (), fun _ _ => rfl, ?_⟩
      intro b
      by_cases hxb : x.1 = b
      · exact ⟨x, mem_filter.mpr ⟨hx, hxb⟩⟩
      · have hyb : y.1 = b := by
          have hxy' : x.1 ≠ y.1 := fun h => hxy (funext fun _ => h)
          cases hxi : x.1 <;> cases hyi : y.1 <;> cases b <;> simp_all
        exact ⟨y, mem_filter.mpr ⟨hy, hyb⟩⟩)
  refine ⟨t, fun x => ht x (mem_univ _), hd, hl.trans ?_⟩
  exact (card_le_card (subset_univ _)).trans_eq (by decide)

-- A zero-bit cube still has one input, so a nullary gate gives one leaf at depth zero.
private def nullary : Program signature 0 1 :=
  Program.empty.gate ⟨⟨0, Fin.elim0, 0⟩, Fin.elim0⟩

example : ∃ t : DecisionTree (SeparableComparison (Fin 0 → Bool) (Fin 0 → Bool)) Bool,
    (∀ x y, t.eval (fun q => q.eval x y) = true) ∧ t.depth = 0 ∧ t.leafCount = 1 := by
  classical
  have hg : inputGates nullary = ∅ := by ext i; simp
  obtain ⟨t, ht, hd, hl⟩ := exists_gate_readout_tree nullary
    (finSumFinEquiv : Fin 0 ⊕ Fin 0 ≃ Fin 0).symm (fun z => z 0)
  refine ⟨t, ?_, Nat.eq_zero_of_le_zero (by simpa only [hg, card_empty] using hd),
    Nat.le_antisymm (hl.trans (card_image_le.trans (by decide))) t.leafCount_pos⟩
  intro x y
  rw [ht]
  change (Program.empty.gate _).eval interpretation _ (Fin.last 0) = true
  rw [Program.eval_gate_last]
  norm_num [Line.eval, interpretation]

private def cancelled : Program signature 1 1 :=
  Program.empty.gate ⟨⟨2, ![1, -1], 0⟩, fun _ => .input 0⟩

-- Repeated-wire cancellation gives a depth-zero tree despite two syntactic argument slots.
example : ∃ t : DecisionTree (SeparableComparison (Fin 1 → Bool) (Fin 0 → Bool)) Bool,
    (∀ x y, t.eval (fun q => q.eval x y) = true) ∧ t.depth = 0 := by
  classical
  have hg : inputGates cancelled = ∅ := by
    ext gate
    simp only [mem_inputGates, Finset.notMem_empty, iff_false, not_exists]
    intro i
    fin_cases gate; fin_cases i
    change ¬lineWeight (⟨⟨2, ![1, -1], 0⟩, fun _ => .input 0⟩ : Line signature 1 1)
      (.input 0) ≠ 0
    dsimp only [lineWeight]
    norm_num [Fin.sum_univ_two]
  obtain ⟨t, ht, hd, _⟩ := exists_gate_readout_tree cancelled
    (finSumFinEquiv : Fin 1 ⊕ Fin 0 ≃ Fin 1).symm (fun z => z 0)
  refine ⟨t, ?_, Nat.eq_zero_of_le_zero (by simpa only [hg, card_empty] using hd)⟩
  intro x y
  rw [ht]
  change (Program.empty.gate _).eval interpretation _ (Fin.last 0) = true
  rw [Program.eval_gate_last]
  dsimp only [Line.eval, interpretation, Function.comp_apply, Wire.elim]
  simp [Fin.sum_univ_two]

private def readOnce : Program signature 1 1 :=
  Program.empty.gate ⟨⟨1, fun _ => 1, 1⟩, fun _ => .input 0⟩

private def readTwice : Program signature 1 2 :=
  readOnce.gate ⟨⟨1, fun _ => 1, 1⟩, fun _ => .input 0⟩

private theorem readTwice_eval (x : Fin 1 → Bool) :
    readTwice.eval interpretation x = fun _ => x 0 := by
  funext gate
  fin_cases gate
  · change (Program.empty.gate _).eval interpretation x (Fin.last 0) = x 0
    rw [Program.eval_gate_last]
    cases hx : x 0 <;>
      dsimp only [Line.eval, interpretation, Function.comp_apply, Wire.elim] <;> norm_num [hx]
  · change (readOnce.gate _).eval interpretation x (Fin.last 1) = x 0
    rw [Program.eval_gate_last]
    cases hx : x 0 <;>
      dsimp only [Line.eval, interpretation, Function.comp_apply, Wire.elim] <;> norm_num [hx]

-- Two input-reading gates have only the equal-bit transcripts: two leaves suffice, not four.
example : (inputGates readTwice).card = 2 ∧
    ∃ t : DecisionTree (SeparableComparison (Fin 1 → Bool) (Fin 0 → Bool)) Bool,
      (∀ x y, t.eval (fun q => q.eval x y) = x 0) ∧ t.depth ≤ 2 ∧ t.leafCount ≤ 2 := by
  classical
  have hg : inputGates readTwice = univ := by
    ext gate
    simp only [mem_inputGates, mem_univ, iff_true]
    refine ⟨0, ?_⟩
    fin_cases gate <;>
      change lineWeight (⟨⟨1, fun _ => 1, 1⟩, fun _ => .input 0⟩ : Line signature 1 2)
        (.input 0) ≠ 0
    all_goals dsimp only [lineWeight]; norm_num
  obtain ⟨t, ht, hd, hl⟩ := exists_gate_readout_tree readTwice
    (finSumFinEquiv : Fin 1 ⊕ Fin 0 ≃ Fin 1).symm (fun z => z 1)
  refine ⟨by simp [hg], t, ?_, by simpa only [hg, card_univ, Fintype.card_fin] using hd,
    hl.trans ?_⟩
  · intro x y
    rw [ht, readTwice_eval]
    rfl
  · calc
      (univ.image (transcript readTwice)).card ≤
          (univ.image (fun b : Bool => fun _ : inputGates readTwice => b)).card :=
        card_le_card (by
          intro z hz
          obtain ⟨x, _, rfl⟩ := mem_image.mp hz
          exact mem_image.mpr ⟨x 0, mem_univ _, (congrArg
            (fun z : Fin 2 → Bool => fun i : inputGates readTwice => z i)
            (readTwice_eval x)).symm⟩)
      _ ≤ 2 := card_image_le.trans (by decide)

private def andCircuit : Circuit signature 2 1 :=
  ⟨Program.empty.gate ⟨⟨2, fun _ => 1, 2⟩, Wire.input⟩, fun _ => .gate 0⟩

-- The final native-circuit endpoint computes both-sided conjunction, including threshold ties.
example : ∃ t : DecisionTree (SeparableComparison (Fin 1 → Bool) (Fin 1 → Bool)) (Fin 1 → Bool),
    ∀ x y, t.eval (fun q => q.eval x y) 0 = (x 0 && y 0) := by
  obtain ⟨t, ht, _, _⟩ := exists_circuit_tree andCircuit
    (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm
    (fun _ => ⟨(0 : Fin 1), rfl⟩)
  refine ⟨t, fun x y => ?_⟩
  rw [ht]
  change (Program.empty.gate _).eval interpretation (inputOfSplit _ x y) (Fin.last 0) = _
  rw [Program.eval_gate_last]
  cases hx : x 0 <;> cases hy : y 0 <;>
    dsimp only [Line.eval, interpretation, Function.comp_apply, Wire.elim] <;>
    norm_num [Fin.sum_univ_two, inputOfSplit, finSumFinEquiv, Fin.addCases, hx, hy]

end ThresholdTranscriptTests
