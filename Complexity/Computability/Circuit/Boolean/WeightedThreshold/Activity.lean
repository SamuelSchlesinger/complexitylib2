/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedThreshold

/-!
# Activity and attainable threshold transcripts

The number of attainable input-reading transcripts is at most the number of bit strings whose
weight is at most the worst-case input-reading activity. This counts only the gates with a
nonzero aggregated coefficient on an original input, not all internal gates.

The resulting exact binomial sum is an upper bound on the number of patterns. Lower bounds for
a computed function also require a representation theorem, such as the comparison-tree compiler.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.attainableTranscripts`: the realized transcripts.
* `Cslib.Circuits.Boolean.WeightedThreshold.inputActivity`: maximum input-reading activity.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.card_attainableTranscripts_le_sum_choose`: the exact
  Hamming-ball bound for attainable patterns.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Theorem 3.2]
  [ThresholdCircuitRepresentations2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset BitString

variable {n g : ℕ}

/-- The restricted activation transcripts realized by Boolean inputs. -/
noncomputable def attainableTranscripts (p : Program signature n g) :
    Finset (inputGates p → Bool) :=
  univ.image (transcript p)

/-- The maximum number of active input-reading gates on one input. -/
noncomputable def inputActivity (p : Program signature n g) : ℕ :=
  univ.sup fun x => weight (transcript p x)

@[simp]
theorem mem_attainableTranscripts (p : Program signature n g) (z : inputGates p → Bool) :
    z ∈ attainableTranscripts p ↔ ∃ x, transcript p x = z := by
  classical
  simp [attainableTranscripts]

/-- An activity bound is exactly a uniform bound on the weight of the restricted transcripts. -/
theorem inputActivity_le_iff (p : Program signature n g) {e : ℕ} :
    inputActivity p ≤ e ↔ ∀ x, weight (transcript p x) ≤ e := by
  simp [inputActivity, Finset.sup_le_iff]

/-- Input-reading activity never exceeds the number of input-reading gates. -/
theorem inputActivity_le_card (p : Program signature n g) :
    inputActivity p ≤ (inputGates p).card := by
  apply (inputActivity_le_iff p).mpr
  intro x
  simpa only [Fintype.card_coe] using weight_le (transcript p x)

/-- Every realized transcript lies in the Hamming ball specified by any uniform activity bound.
The bound also permits a radius larger than the number of input-reading gates. -/
theorem card_attainableTranscripts_le_sum_choose_of_le (p : Program signature n g) {e : ℕ}
    (he : inputActivity p ≤ e) :
    (attainableTranscripts p).card ≤
      ∑ j ∈ range (e + 1), (inputGates p).card.choose j := by
  classical
  calc
    _ ≤ #{z : inputGates p → Bool | weight z ≤ e} := by
      apply card_le_card
      intro z hz
      obtain ⟨x, rfl⟩ := (mem_attainableTranscripts p z).mp hz
      exact mem_filter.mpr ⟨mem_univ _, (inputActivity_le_iff p).mp he x⟩
    _ = _ := by simp only [card_filter_weight_le, Fintype.card_coe]

/-- Attainable patterns are bounded by the exact binomial sum at worst-case activity. -/
theorem card_attainableTranscripts_le_sum_choose (p : Program signature n g) :
    (attainableTranscripts p).card ≤
      ∑ j ∈ range (inputActivity p + 1), (inputGates p).card.choose j :=
  card_attainableTranscripts_le_sum_choose_of_le p le_rfl

end Cslib.Circuits.Boolean.WeightedThreshold
