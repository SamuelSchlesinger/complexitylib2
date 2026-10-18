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

The number of attainable input-reading transcripts is bounded by a Hamming ball at the
worst-case input-reading activity. Projecting the full gate valuations gives a second bound
using the total gate count and maximum activity across all gates. Both bounds use the same
finite-image counting lemma.

The resulting exact binomial sum is an upper bound on the number of patterns. Lower bounds for
a computed function also require a representation theorem, such as the comparison-tree compiler.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.attainableTranscripts`: the realized transcripts.
* `Cslib.Circuits.Boolean.WeightedThreshold.inputActivity`: maximum input-reading activity.
* `Cslib.Circuits.Boolean.WeightedThreshold.gateActivity`: maximum activity across all gates.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.card_attainableTranscripts_le_sum_choose`: the exact
  Hamming-ball bound for attainable patterns.
* `Cslib.Circuits.Boolean.WeightedThreshold.card_attainableTranscripts_le_sum_choose_gateActivity`:
  the bound using activity across all gates.

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

/-- The maximum number of active gates on one input, including gates without direct inputs. -/
noncomputable def gateActivity (p : Program signature n g) : ℕ :=
  univ.sup fun x => weight (p.eval interpretation x)

@[simp]
theorem mem_attainableTranscripts (p : Program signature n g) (z : inputGates p → Bool) :
    z ∈ attainableTranscripts p ↔ ∃ x, transcript p x = z := by
  classical
  simp [attainableTranscripts]

/-- An activity bound is exactly a uniform bound on the weight of the restricted transcripts. -/
theorem inputActivity_le_iff (p : Program signature n g) {e : ℕ} :
    inputActivity p ≤ e ↔ ∀ x, weight (transcript p x) ≤ e := by
  simp [inputActivity, Finset.sup_le_iff]

/-- A bound on total activity is exactly a uniform bound on complete gate valuations. -/
theorem gateActivity_le_iff (p : Program signature n g) {e : ℕ} :
    gateActivity p ≤ e ↔ ∀ x, weight (p.eval interpretation x) ≤ e := by
  simp [gateActivity, Finset.sup_le_iff]

/-- Total gate activity never exceeds the number of gates. -/
theorem gateActivity_le (p : Program signature n g) : gateActivity p ≤ g := by
  apply (gateActivity_le_iff p).mpr
  intro x
  simpa only [Fintype.card_fin] using weight_le (p.eval interpretation x)

/-- Restricting to the input-reading gates cannot increase activity. -/
theorem inputActivity_le_gateActivity (p : Program signature n g) :
    inputActivity p ≤ gateActivity p := by
  apply (inputActivity_le_iff p).mpr
  intro x
  exact (weight_comp_le (p.eval interpretation x)
    (f := fun i : inputGates p => i.val) Subtype.val_injective).trans
      ((gateActivity_le_iff p).mp le_rfl x)

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
  simpa only [attainableTranscripts, Fintype.card_coe] using
    card_image_le_sum_choose univ (transcript p)
    (fun x _ => (inputActivity_le_iff p).mp he x)

/-- Attainable patterns are bounded by the exact binomial sum at worst-case activity. -/
theorem card_attainableTranscripts_le_sum_choose (p : Program signature n g) :
    (attainableTranscripts p).card ≤
      ∑ j ∈ range (inputActivity p + 1), (inputGates p).card.choose j :=
  card_attainableTranscripts_le_sum_choose_of_le p le_rfl

/-- Projecting full gate valuations cannot create additional restricted transcripts, so total
gate activity gives a Hamming-ball bound using the total number of gates. -/
theorem card_attainableTranscripts_le_sum_choose_gateActivity (p : Program signature n g) :
    (attainableTranscripts p).card ≤ ∑ j ∈ range (gateActivity p + 1), g.choose j := by
  classical
  calc
    _ = ((univ.image (p.eval interpretation)).image
        fun z => fun i : inputGates p => z i).card := by
      simp only [attainableTranscripts, image_image]
      rfl
    _ ≤ (univ.image (p.eval interpretation)).card := card_image_le
    _ ≤ _ := by
      simpa only [Fintype.card_fin] using card_image_le_sum_choose univ
        (p.eval interpretation) (fun x _ => (gateActivity_le_iff p).mp le_rfl x)

end Cslib.Circuits.Boolean.WeightedThreshold
