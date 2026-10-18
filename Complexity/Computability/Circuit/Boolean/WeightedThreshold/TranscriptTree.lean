/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedThreshold
import Complexity.Computability.DecisionTree.Observations
public import Complexity.Computability.DecisionTree.Separable
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max

/-!
# Weighted threshold transcripts as comparison trees

For any split of the original inputs, a native weighted threshold program has a separable
comparison tree computing any fixed readout of its gate values. The tree has depth at most the
number of input-reading gates and at most as many leaves as attained restricted transcripts.
Only nonempty answer branches are constructed. All comparisons retain the convention that
equality at a threshold returns `true`.

This construction is semantic and noncomputable; no efficient compiler is asserted.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.inputOfSplit`: assemble the two sides of an input.
* `Cslib.Circuits.Boolean.WeightedThreshold.gateComparison`: absorb fixed earlier gate values
  into the threshold of a separable comparison.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.exists_transcript_tree`: any output determined by
  the transcript has the claimed tree.
* `Cslib.Circuits.Boolean.WeightedThreshold.exists_gate_readout_tree`: every fixed readout of
  the complete gate valuation is covered.
* `Cslib.Circuits.Boolean.WeightedThreshold.exists_circuit_tree`: designated gate outputs are
  computed simultaneously.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Lemma 3.1]
  [ThresholdCircuitRepresentations2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset

variable {n g : ℕ} {L R β : Type*} [Fintype L] [Fintype R]

/-- Assemble the left and right input coordinates using their partition equivalence. -/
def inputOfSplit (split : Fin n ≃ L ⊕ R) (x : L → Bool) (y : R → Bool) : Fin n → Bool :=
  Sum.elim x y ∘ split

/-- With preceding gate values fixed, the remaining gate equation is a separable comparison
of its direct input contributions. -/
def gateComparison (p : Program signature n g) (split : Fin n ≃ L ⊕ R) (gate : Fin g)
    (previous : Fin g → Bool) : SeparableComparison (L → Bool) (R → Bool) where
  left x := ∑ i, inputWeight p gate (split.symm (.inl i)) * (x i).toNat
  right y := ∑ i, inputWeight p gate (split.symm (.inr i)) * (y i).toNat
  threshold := (p.lines gate).op.threshold -
    ∑ j, gateWeight p gate j * (previous j).toNat

/-- Earlier gate values suffice to evaluate the comparison; current and later values do not
affect it because their coefficients vanish. -/
theorem gateComparison_eval_eq (p : Program signature n g) (split : Fin n ≃ L ⊕ R)
    (gate : Fin g) (previous : Fin g → Bool) (x : L → Bool) (y : R → Bool)
    (hprevious : ∀ j < gate,
      previous j = p.eval interpretation (inputOfSplit split x y) j) :
    (gateComparison p split gate previous).eval x y =
      p.eval interpretation (inputOfSplit split x y) gate := by
  have hsum : (∑ j, gateWeight p gate j * (previous j).toNat) =
      ∑ j, gateWeight p gate j *
        (p.eval interpretation (inputOfSplit split x y) j).toNat := by
    apply sum_congr rfl
    intro j _
    by_cases hj : j < gate
    · rw [hprevious j hj]
    · rw [gateWeight_eq_zero_of_le p gate j (le_of_not_gt hj)]
      simp
  have hinput : (∑ i, inputWeight p gate i * (inputOfSplit split x y i).toNat) =
      (∑ i, inputWeight p gate (split.symm (.inl i)) * (x i).toNat) +
      ∑ i, inputWeight p gate (split.symm (.inr i)) * (y i).toNat := by
    rw [← split.symm.sum_comp (fun i =>
      inputWeight p gate i * ((inputOfSplit split x y i).toNat : ℝ)), Fintype.sum_sum_type]
    simp only [inputOfSplit, Function.comp_apply, Equiv.apply_symm_apply, Sum.elim_inl,
      Sum.elim_inr]
  rw [eval_gate_eq p (inputOfSplit split x y) gate, SeparableComparison.eval,
    Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  dsimp only [gateComparison]
  rw [hinput, hsum, sub_le_iff_le_add]

omit [Fintype L] [Fintype R] in
private theorem exists_varying_comparison (p : Program signature n g)
    (split : Fin n ≃ L ⊕ R) (S : Finset ((L → Bool) × (R → Bool))) (hS : S.Nonempty)
    (hne : ∃ x ∈ S, ∃ y ∈ S,
      transcript p (inputOfSplit split x.1 x.2) ≠
        transcript p (inputOfSplit split y.1 y.2)) :
    ∃ (q : SeparableComparison (L → Bool) (R → Bool)) (i : inputGates p),
      (∀ x ∈ S, q.eval x.1 x.2 = transcript p (inputOfSplit split x.1 x.2) i) ∧
      ∀ b : Bool,
        (S.filter fun x => transcript p (inputOfSplit split x.1 x.2) i = b).Nonempty := by
  classical
  let : Fintype (L ⊕ R) := Fintype.ofEquiv (Fin n) split
  let : Fintype L := Fintype.ofInjective (Sum.inl : L → L ⊕ R) Sum.inl_injective
  let : Fintype R := Fintype.ofInjective (Sum.inr : R → L ⊕ R) Sum.inr_injective
  let observe (x : (L → Bool) × (R → Bool)) := transcript p (inputOfSplit split x.1 x.2)
  let varying : Finset (inputGates p) := univ.filter fun i =>
    ∃ x ∈ S, ∃ y ∈ S, observe x i ≠ observe y i
  have hv : varying.Nonempty := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hne
    obtain ⟨i, hi⟩ := not_forall.mp (fun h => hxy (funext h))
    exact ⟨i, mem_filter.mpr ⟨mem_univ _, x, hx, y, hy, hi⟩⟩
  let i := varying.min' hv
  have hi : i ∈ varying := min'_mem _ _
  obtain ⟨x₀, hx₀⟩ := hS
  have hprevious (x) (hx : x ∈ S) : ∀ j : Fin g, j < i.val →
      p.eval interpretation (inputOfSplit split x₀.1 x₀.2) j =
        p.eval interpretation (inputOfSplit split x.1 x.2) j := by
    apply eval_eq_of_forall_mem_inputGates_lt p i.val
    intro j hj hjlt
    by_contra hne
    have hjv : (⟨j, hj⟩ : inputGates p) ∈ varying :=
      mem_filter.mpr ⟨mem_univ _, x₀, hx₀, x, hx, hne⟩
    exact (not_le_of_gt hjlt) (varying.min'_le _ hjv)
  refine ⟨gateComparison p split i.val (p.eval interpretation
    (inputOfSplit split x₀.1 x₀.2)), i, ?_, ?_⟩
  · intro x hx
    exact gateComparison_eval_eq p split i.val _ x.1 x.2 (hprevious x hx)
  · obtain ⟨x, hx, y, hy, hxy⟩ := (mem_filter.mp hi).2
    intro b
    by_cases hxb : observe x i = b
    · exact ⟨x, mem_filter.mpr ⟨hx, hxb⟩⟩
    · have hyb : observe y i = b := by
        cases hxi : observe x i <;> cases hyi : observe y i <;> cases b <;> simp_all
      exact ⟨y, mem_filter.mpr ⟨hy, hyb⟩⟩

omit [Fintype L] [Fintype R] in
/-- Any output determined by the restricted transcript has a separable comparison tree of
depth at most the input-reading count and with at most one leaf per attainable transcript. -/
theorem exists_transcript_tree (p : Program signature n g) (split : Fin n ≃ L ⊕ R)
    (output : (Fin n → Bool) → β)
    (hout : ∀ x y, transcript p x = transcript p y → output x = output y) :
    ∃ t : DecisionTree (SeparableComparison (L → Bool) (R → Bool)) β,
      (∀ x y, t.eval (fun q => q.eval x y) = output (inputOfSplit split x y)) ∧
      t.depth ≤ (inputGates p).card ∧ t.leafCount ≤ (univ.image (transcript p)).card := by
  classical
  let : Fintype (L ⊕ R) := Fintype.ofEquiv (Fin n) split
  let : Fintype L := Fintype.ofInjective (Sum.inl : L → L ⊕ R) Sum.inl_injective
  let : Fintype R := Fintype.ofInjective (Sum.inr : R → L ⊕ R) Sum.inr_injective
  obtain ⟨t, ht, hd, hl⟩ := DecisionTree.exists_of_observations
    (univ : Finset ((L → Bool) × (R → Bool))) univ_nonempty
    (fun x => transcript p (inputOfSplit split x.1 x.2))
    (fun (q : SeparableComparison (L → Bool) (R → Bool)) x => q.eval x.1 x.2)
    (fun x => output (inputOfSplit split x.1 x.2))
    (fun _ _ _ _ h => hout _ _ h)
    (fun S _ hS hne => exists_varying_comparison p split S hS hne)
  refine ⟨t, fun x y => ht (x, y) (mem_univ _), ?_, hl.trans (card_le_card ?_)⟩
  · simpa only [Fintype.card_coe] using hd
  · intro z hz
    obtain ⟨x, _, rfl⟩ := mem_image.mp hz
    exact mem_image.mpr ⟨inputOfSplit split x.1 x.2, mem_univ _, rfl⟩

omit [Fintype L] [Fintype R] in
/-- A fixed readout of all native gate values satisfies the transcript-tree bounds. -/
theorem exists_gate_readout_tree (p : Program signature n g) (split : Fin n ≃ L ⊕ R)
    (readout : (Fin g → Bool) → β) :
    ∃ t : DecisionTree (SeparableComparison (L → Bool) (R → Bool)) β,
      (∀ x y, t.eval (fun q => q.eval x y) =
        readout (p.eval interpretation (inputOfSplit split x y))) ∧
      t.depth ≤ (inputGates p).card ∧ t.leafCount ≤ (univ.image (transcript p)).card :=
  exists_transcript_tree p split (fun x => readout (p.eval interpretation x))
    (fun _ _ h => congrArg readout (eval_eq_of_transcript_eq p h))

omit [Fintype L] [Fintype R] in
/-- A circuit whose outputs select gates has a comparison tree computing all designated
outputs simultaneously, under the same depth and attainable-transcript leaf bounds. -/
theorem exists_circuit_tree {m : ℕ} (c : Circuit signature n m) (split : Fin n ≃ L ⊕ R)
    (houtputs : ∀ output, ∃ gate, c.outputs output = .gate gate) :
    ∃ t : DecisionTree (SeparableComparison (L → Bool) (R → Bool)) (Fin m → Bool),
      (∀ x y, t.eval (fun q => q.eval x y) = c.eval interpretation (inputOfSplit split x y)) ∧
      t.depth ≤ (inputGates c.program).card ∧
      t.leafCount ≤ (univ.image (transcript c.program)).card :=
  exists_transcript_tree c.program split (c.eval interpretation)
    (fun _ _ h => circuit_eval_eq_of_transcript_eq c houtputs h)

end Cslib.Circuits.Boolean.WeightedThreshold
