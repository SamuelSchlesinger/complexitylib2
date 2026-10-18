/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Activity

/-! Exact Hamming-ball counts and gate-activity bounds, including empty gate sets. -/

open Cslib Cslib.Circuits Cslib.BitString Finset

namespace ThresholdActivity

-- Independent finite counts at zero, partial, and oversized radii.
example : #{x : Fin 3 → Bool | weight x ≤ 0} = 1 := by decide
example : #{x : Fin 3 → Bool | weight x ≤ 1} = 4 := by decide
example : #{x : Fin 3 → Bool | weight x ≤ 5} = 8 := by decide

example {ι : Type*} [Fintype ι] [DecidableEq ι] :
    #{x : ι → Bool | weight x ≤ 0} = 1 := by
  rw [card_filter_weight_le]
  simp

example (e : ℕ) : #{x : Fin 0 → Bool | weight x ≤ e} = 1 := by
  simp [weight]

-- The image bound permits repeated words, empty families, and oversized radii.
example : ((univ : Finset (Fin 3)).image (fun _ => fun _ : Fin 2 => false)).card ≤
    ∑ j ∈ range 1, Nat.choose 2 j := by
  apply card_image_le_sum_choose
  intro _ _
  simp [weight]

example (e : ℕ) : ((∅ : Finset Bool).image (fun _ => fun _ : Fin 0 => false)).card ≤
    ∑ j ∈ range (e + 1), Nat.choose 0 j :=
  card_image_le_sum_choose _ _ (fun _ h => False.elim (notMem_empty _ h))

example (f : Bool → Fin 2 → Bool) : (univ.image f).card ≤ ∑ j ∈ range 6, Nat.choose 2 j := by
  apply card_image_le_sum_choose
  intro x _
  exact (weight_le (f x)).trans (by decide)

-- Coordinate restriction needs injectivity: repeating a true bit can increase weight.
example (x : Fin 2 → Bool) : weight (x ∘ Fin.castAdd 1 : Fin 1 → Bool) ≤ weight x :=
  weight_comp_le x (Fin.castAdd_injective 1 1)

example : weight ((fun _ : Fin 1 => true) ∘ (fun _ : Fin 2 => 0)) >
    weight (fun _ : Fin 1 => true) := by decide

open Boolean.WeightedThreshold

private def trueGate : Program signature 0 1 :=
  Program.empty.gate ⟨⟨0, Fin.elim0, 0⟩, Fin.elim0⟩

-- An active gate-only computation has zero input-reading activity.
private theorem trueGate_eval (x : Fin 0 → Bool) :
    trueGate.eval interpretation x 0 = true := by
  change (Program.empty.gate _).eval interpretation x (Fin.last 0) = true
  rw [Program.eval_gate_last]
  norm_num [Line.eval, interpretation]

example : inputActivity trueGate = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa [inputGates] using inputActivity_le_card trueGate

-- Total activity includes the active nullary gate that input-reading activity excludes.
example : gateActivity trueGate = 1 := by
  apply Nat.le_antisymm (gateActivity_le trueGate)
  have h := (gateActivity_le_iff trueGate).mp le_rfl Fin.elim0
  simpa [weight_eq_sum_toNat, trueGate_eval] using h

example (n : ℕ) : gateActivity (Program.empty : Program signature n 0) = 0 :=
  Nat.eq_zero_of_le_zero (gateActivity_le Program.empty)

-- No gates gives exactly one empty transcript and activity zero, at every input length.
example (n : ℕ) : inputActivity (Program.empty : Program signature n 0) = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa [inputGates] using inputActivity_le_card (Program.empty : Program signature n 0)

example (n : ℕ) :
    (attainableTranscripts (Program.empty : Program signature n 0)).card = 1 := by
  classical
  have h : attainableTranscripts (Program.empty : Program signature n 0) =
      {transcript Program.empty (fun _ => false)} := by
    ext z
    simp only [mem_attainableTranscripts, mem_singleton]
    constructor
    · rintro ⟨x, rfl⟩
      exact Subsingleton.elim _ _
    · rintro rfl
      exact ⟨fun _ => false, rfl⟩
  rw [h, card_singleton]

-- Bounds use only direct-input gates, regardless of the number of internal gates.
example {n g : ℕ} (p : Program signature n g) :
    (attainableTranscripts p).card ≤
      ∑ j ∈ range ((inputGates p).card + 1), (inputGates p).card.choose j :=
  card_attainableTranscripts_le_sum_choose_of_le p (inputActivity_le_card p)

-- A bound larger than the available number of coordinates is also accepted.
example {n g : ℕ} (p : Program signature n g) :
    (attainableTranscripts p).card ≤
      ∑ j ∈ range ((inputGates p).card + 4), (inputGates p).card.choose j := by
  apply card_attainableTranscripts_le_sum_choose_of_le
  exact (inputActivity_le_card p).trans (Nat.le_add_right _ 3)

example {n g : ℕ} (p : Program signature n g) :
    inputActivity p ≤ gateActivity p ∧ gateActivity p ≤ g :=
  ⟨inputActivity_le_gateActivity p, gateActivity_le p⟩

end ThresholdActivity
