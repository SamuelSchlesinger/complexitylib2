/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Activity

/-! Exact Hamming-ball counts and input-activity bounds, including empty gate sets. -/

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

open Boolean.WeightedThreshold

private def trueGate : Program signature 0 1 :=
  Program.empty.gate ⟨⟨0, Fin.elim0, 0⟩, Fin.elim0⟩

-- An active gate-only computation has zero input-reading activity.
example (x : Fin 0 → Bool) : trueGate.eval interpretation x 0 = true := by
  change (Program.empty.gate _).eval interpretation x (Fin.last 0) = true
  rw [Program.eval_gate_last]
  norm_num [Line.eval, interpretation]

example : inputActivity trueGate = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa [inputGates] using inputActivity_le_card trueGate

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

end ThresholdActivity
