/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Activity
public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.TranscriptTree
public import Complexity.Foundations.BooleanAnalysis.Hadamard
import Complexity.Computability.DecisionTree.InnerProduct

/-!
# Threshold gate activity for inner product

If a weighted threshold program computes inner product modulo two through a readout of its
gate values, its attainable input-reading transcripts have cardinality `A` with `2 ^ m ≤ A ^ 2`.
Bounding those transcripts by a Hamming ball gives the exact size-activity inequality
`2 ^ m ≤ (∑ j ≤ e, q.choose j) ^ 2`. Here `q` and `e` may count only input-reading gates and
their maximum activity, or all gates and their maximum activity. The statements include
zero-dimensional inputs and arbitrary real weights.

The circuit specializations require the designated output to be a gate.

## Main results

* `two_pow_le_card_attainableTranscripts_sq_of_hadamardCode`: the attained-pattern lower bound.
* `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_le_sum_choose_sq_of_hadamardCode`:
  the exact binomial-sum size-activity inequality.
* `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_le_sum_choose_sq_of_circuit_hadamardCode`:
  the same bound for a native single-output circuit.
* `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_le_sum_choose_gateActivity_sq_of_hadamardCode`:
  the exact bound using total gate count and total activity.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Theorem 3.2]
  [ThresholdCircuitRepresentations2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset BitString

variable {n g : ℕ} {ι : Type*} [Fintype ι]

/-- The square of the number of attainable input-reading transcripts is at least the size of
one side's Boolean cube whenever a fixed gate readout computes inner product. -/
theorem two_pow_le_card_attainableTranscripts_sq_of_hadamardCode
    (p : Program signature n g) (split : Fin n ≃ ι ⊕ ι)
    (readout : (Fin g → Bool) → Bool)
    (h : ∀ x y, readout (p.eval interpretation (inputOfSplit split x y)) = hadamardCode x y) :
    2 ^ Fintype.card ι ≤ (attainableTranscripts p).card ^ 2 := by
  obtain ⟨t, ht, _, hl⟩ := exists_gate_readout_tree p split readout
  exact (t.two_pow_le_leafCount_sq_of_hadamardCode fun x y => (ht x y).trans (h x y)).trans
    (Nat.pow_le_pow_left hl 2)

/-- Inner product forces the exact binomial sum at the program's input-reading activity to
have square at least `2 ^ m`, where `m` is the number of coordinates on either side. -/
theorem two_pow_le_sum_choose_sq_of_hadamardCode
    (p : Program signature n g) (split : Fin n ≃ ι ⊕ ι)
    (readout : (Fin g → Bool) → Bool)
    (h : ∀ x y, readout (p.eval interpretation (inputOfSplit split x y)) = hadamardCode x y) :
    2 ^ Fintype.card ι ≤
      (∑ j ∈ range (inputActivity p + 1), (inputGates p).card.choose j) ^ 2 :=
  (two_pow_le_card_attainableTranscripts_sq_of_hadamardCode p split readout h).trans
    (Nat.pow_le_pow_left (card_attainableTranscripts_le_sum_choose p) 2)

/-- A native single-output circuit computing inner product obeys the size-activity inequality
provided its output selects a gate. -/
theorem two_pow_le_sum_choose_sq_of_circuit_hadamardCode
    (c : Circuit signature n 1) (split : Fin n ≃ ι ⊕ ι)
    (houtput : ∃ gate, c.outputs 0 = .gate gate)
    (h : ∀ x y, c.eval interpretation (inputOfSplit split x y) 0 = hadamardCode x y) :
    2 ^ Fintype.card ι ≤
      (∑ j ∈ range (inputActivity c.program + 1), (inputGates c.program).card.choose j) ^ 2 := by
  obtain ⟨gate, hgate⟩ := houtput
  apply two_pow_le_sum_choose_sq_of_hadamardCode c.program split (fun z => z gate)
  intro x y
  simpa only [Circuit.eval, Function.comp_apply, hgate, Program.trace_gateWire,
    Program.gateFunction_apply] using h x y

/-- Inner product forces the binomial sum at total gate activity to have square at least
`2 ^ m`. All gates are counted, including unused gates and gates without direct inputs. -/
theorem two_pow_le_sum_choose_gateActivity_sq_of_hadamardCode
    (p : Program signature n g) (split : Fin n ≃ ι ⊕ ι)
    (readout : (Fin g → Bool) → Bool)
    (h : ∀ x y, readout (p.eval interpretation (inputOfSplit split x y)) = hadamardCode x y) :
    2 ^ Fintype.card ι ≤ (∑ j ∈ range (gateActivity p + 1), g.choose j) ^ 2 :=
  (two_pow_le_card_attainableTranscripts_sq_of_hadamardCode p split readout h).trans
    (Nat.pow_le_pow_left (card_attainableTranscripts_le_sum_choose_gateActivity p) 2)

/-- A native single-output inner-product circuit also obeys the bound using all gates,
provided its output selects a gate. -/
theorem two_pow_le_sum_choose_gateActivity_sq_of_circuit_hadamardCode
    (c : Circuit signature n 1) (split : Fin n ≃ ι ⊕ ι)
    (houtput : ∃ gate, c.outputs 0 = .gate gate)
    (h : ∀ x y, c.eval interpretation (inputOfSplit split x y) 0 = hadamardCode x y) :
    2 ^ Fintype.card ι ≤
      (∑ j ∈ range (gateActivity c.program + 1), c.size.choose j) ^ 2 := by
  obtain ⟨gate, hgate⟩ := houtput
  apply two_pow_le_sum_choose_gateActivity_sq_of_hadamardCode c.program split (fun z => z gate)
  intro x y
  simpa only [Circuit.eval, Function.comp_apply, hgate, Program.trace_gateWire,
    Program.gateFunction_apply] using h x y

end Cslib.Circuits.Boolean.WeightedThreshold
