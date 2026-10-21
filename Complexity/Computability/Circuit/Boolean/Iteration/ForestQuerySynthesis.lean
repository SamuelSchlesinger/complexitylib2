/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.ForestRecordQueries

/-!
# Synthesizing the transient compressed-forest reachability flag

Given a circuit `c` computing `f : BitString n → BitString n`, a depth circuit `depth`, and
`tables : ForestCircuitTables f L`, this module synthesizes the 1-bit circuit deciding reachability
`∃ t, f^[t] (inputLeft z) = inputRight z` whenever the target `inputRight z` is transient
(`0 < transientDepth f (inputRight z)`).

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.transientForestCost`: gate budget of the transient
  compressed-forest reachability subcircuit.

## Main results

* `Cslib.Circuits.Boolean.Iteration.synthesis_transient_forest_reachability`: synthesizes a 1-bit
  circuit deciding reachability to transient targets within `transientForestCost`.

## References

* Adapted from `lean/Proofs/ForestQuerySynthesis.lean` in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open FunctionalGraph

variable {n : ℕ}

/-- Gate budget for the transient compressed-forest reachability query. -/
def transientForestCost (n s d M E L : ℕ) : ℕ :=
  2 + d + 6 * L * s +
    dictionaryCost n (n + 1 + (n + 1)) M (2 * L + 2) +
    dictionaryCost n (n + (n + 1 + (n + 1)) + (n + 3)) E (2 * L + 1) +
    (2 * L + 1) * (41 * n + 41) + (24 * n + 50)

/-- Synthesize the transient reachability flag from a depth circuit and forest tables. -/
theorem synthesis_transient_forest_reachability
    (c : Circuit signature n n) (L : ℕ) (hL : 0 < L)
    (depth : Circuit signature n (n + 2))
    (hd : ∀ x, word (depth.eval interpretation x) =
      BitVec.ofNat (n + 2) (transientDepth (c.eval interpretation) x))
    (tables : ForestCircuitTables (c.eval interpretation) L) :
    ∃ out : Circuit signature (n + n) 1,
      (∀ z, 0 < transientDepth (c.eval interpretation) (inputRight z) →
        (out.eval interpretation z 0 = true ↔
          ∃ t, (c.eval interpretation)^[t] (inputLeft z) = inputRight z)) ∧
      out.size ≤ transientForestCost n c.size depth.size
        tables.markCount tables.edgeTable.count L := by
  let f := c.eval interpretation
  let K := 2 * L
  let Q := K + 1
  let constants : Set (BooleanFunction (n + n)) := {fun _ => false, fun _ => true}
  have hconst : Synthesis interpretation (inputs (n + n)) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  let s0 := inputs (n + n) ∪ constants
  have hc0 (b : Bool) : (fun _ : BitString (n + n) => b) ∈ s0 := by
    cases b <;> simp [s0, constants]
  have hleft : wires (inputLeft (n := n)) ⊆ s0 := by
    rintro _ ⟨i, rfl⟩
    exact Or.inl ⟨Fin.castAdd n i, rfl⟩
  have hright : wires (inputRight (n := n)) ⊆ s0 := by
    rintro _ ⟨i, rfl⟩
    exact Or.inl ⟨Fin.natAdd n i, rfl⟩
  have hdy := synthesis_depthWord f depth hd s0 inputRight hright (hc0 false)
  have hxOrb := Synthesis.orbit (I := interpretation) (s := s0) c inputLeft
    (fun i => hleft ⟨i, rfl⟩) K
  have hyOrb := Synthesis.orbit (I := interpretation) (s := s0) c inputRight
    (fun i => hright ⟨i, rfl⟩) K
  let s1 := s0 ∪ (wordWires (fun z => depthWord f (inputRight z)) ∪
    (Synthesis.stages (fun j => wires fun z => f^[j] (inputLeft z)) K ∪
     Synthesis.stages (fun j => wires fun z => f^[j] (inputRight z)) K))
  have hc1 (b : Bool) : (fun _ : BitString (n + n) => b) ∈ s1 := Or.inl (hc0 b)
  have hright1 : wires (inputRight (n := n)) ⊆ s1 := fun _ h => Or.inl (hright h)
  have hdy1 (bit : Fin (n + 3)) :
      (fun z => (depthWord f (inputRight z)).getLsbD bit.val) ∈ s1 :=
    Or.inr (Or.inl ⟨bit, rfl⟩)
  have hxTrace (j : Fin Q) : wires (fun z => f^[j.val] (inputLeft z)) ⊆ s1 :=
    fun _ h => Or.inr (Or.inr (Or.inl
      (Synthesis.subset_stages _ (Nat.le_of_lt_succ j.isLt) h)))
  have hyTrace (j : Fin Q) : wires (fun z => f^[j.val] (inputRight z)) ⊆ s1 :=
    fun _ h => Or.inr (Or.inr (Or.inr
      (Synthesis.subset_stages _ (Nat.le_of_lt_succ j.isLt) h)))
  let markQueries : BitString (n + n) → Fin (Q + 1) → BitString n :=
    fun z j => Fin.lastCases (inputRight z) (fun i : Fin Q => f^[i.val] (inputLeft z)) j
  have hmarkQ (j : Fin (Q + 1)) : wires (fun z => markQueries z j) ⊆ s1 := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa [markQueries] using hright1
    · simpa [markQueries] using hxTrace i
  obtain ⟨mFlags, mRecords, hmDict, hmSynth⟩ := synthesis_fixed_dictionary s1
    tables.marks tables.marks_injective
    (fun i => forestLabelWord tables.low tables.high (tables.marks i))
    markQueries hmarkQ
  obtain ⟨eFlags, eRecords, heDict, heSynth⟩ := synthesis_fixed_dictionary s1
    tables.edgeTable.key tables.edgeTable.key_injective
    (fun i => forestAnchorWord f tables.low tables.high (tables.edgeTable.start i))
    (fun z (j : Fin Q) => f^[j.val] (inputRight z)) hyTrace
  have hshortX := synthesis_prefix_hit s1
    (fun z (j : Fin Q) => f^[j.val] (inputLeft z)) inputRight hxTrace hright1
  let s2 := s1 ∪ (((Set.range (fun j z => mFlags z j) ∪ ⋃ j, wires (fun z => mRecords z j)) ∪
    (Set.range (fun j z => eFlags z j) ∪ ⋃ j, wires (fun z => eRecords z j))) ∪
    {fun z => decide (∃ j : Fin Q, f^[j.val] (inputLeft z) = inputRight z)})
  have hc2 (b : Bool) : (fun _ : BitString (n + n) => b) ∈ s2 := Or.inl (hc1 b)
  have hmFlags2 (j : Fin (Q + 1)) : (fun z => mFlags z j) ∈ s2 :=
    Or.inr (Or.inl (Or.inl (Or.inl ⟨j, rfl⟩)))
  have hmRec2 (j : Fin (Q + 1)) : wires (fun z => mRecords z j) ⊆ s2 :=
    fun _ h => Or.inr (Or.inl (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨j, h⟩))))
  have heFlags2 (j : Fin Q) : (fun z => eFlags z j) ∈ s2 :=
    Or.inr (Or.inl (Or.inr (Or.inl ⟨j, rfl⟩)))
  have heRec2 (j : Fin Q) : wires (fun z => eRecords z j) ⊆ s2 :=
    fun _ h => Or.inr (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨j, h⟩))))
  obtain ⟨foundH, markLabels, hmarkSpec, hmarkSynth⟩ := synthesis_selected_mark f L tables
    s2 (hc2 false)
    (fun z (j : Fin Q) => f^[j.val] (inputLeft z))
    (fun z (j : Fin Q) => mFlags z j.castSucc)
    (fun z (j : Fin Q) => mRecords z j.castSucc)
    (fun j => hmFlags2 j.castSucc)
    (fun j => hmRec2 j.castSucc)
    (fun z j => by simpa [markQueries] using hmDict z j.castSucc)
  obtain ⟨foundA, anchorState, anchorLabels, hanchorSpec, hanchorSynth⟩ :=
    synthesis_selected_anchor f L tables
      (fun j => Nat.le_of_lt_succ j.isLt)
      (fun k hk => ⟨⟨k, Nat.lt_succ_of_le hk⟩, rfl⟩)
      s2 (fun _ h => Or.inl (hright1 h))
      (fun bit => Or.inl (hdy1 bit))
      (fun z => mFlags z (Fin.last Q))
      (fun z => mRecords z (Fin.last Q))
      (hmFlags2 (Fin.last Q))
      (hmRec2 (Fin.last Q))
      (fun z => by simpa [markQueries] using hmDict z (Fin.last Q))
      eFlags eRecords heFlags2 heRec2 heDict
  let s3 := s2 ∪ (({foundH} ∪ wires markLabels) ∪
    ({foundA} ∪ wires anchorState ∪ wires anchorLabels))
  have haState3 : wires anchorState ⊆ s3 :=
    fun _ h => Or.inr (Or.inr (Or.inl (Or.inr h)))
  have hmLabels3 : wires markLabels ⊆ s3 :=
    fun _ h => Or.inr (Or.inl (Or.inr h))
  have haLabels3 : wires anchorLabels ⊆ s3 :=
    fun _ h => Or.inr (Or.inr (Or.inr h))
  have haOrb := Synthesis.orbit (I := interpretation) (s := s3) c anchorState
    (fun i => haState3 ⟨i, rfl⟩) K
  have hint := synthesis_interval_containment s3 markLabels anchorLabels hmLabels3 haLabels3
  let intervalBit : BooleanFunction (n + n) := fun z =>
    (!(forestLowWord (markLabels z)).ult (forestLowWord (anchorLabels z))) &&
    (!(forestHighWord (anchorLabels z)).ult (forestLowWord (markLabels z)))
  let s4 := s3 ∪ (Synthesis.stages (fun j => wires fun z => f^[j] (anchorState z)) K ∪
    {intervalBit})
  have haTrace (j : Fin Q) : wires (fun z => f^[j.val] (anchorState z)) ⊆ s4 :=
    fun _ h => Or.inr (Or.inl
      (Synthesis.subset_stages _ (Nat.le_of_lt_succ j.isLt) h))
  have hverify := synthesis_prefix_hit s4
    (fun z (j : Fin Q) => f^[j.val] (anchorState z)) inputRight haTrace
    (fun _ h => Or.inl (Or.inl (Or.inl (hright1 h))))
  let verifyBit : BooleanFunction (n + n) :=
    fun z => decide (∃ j : Fin Q, f^[j.val] (anchorState z) = inputRight z)
  let shortBit : BooleanFunction (n + n) :=
    fun z => decide (∃ j : Fin Q, f^[j.val] (inputLeft z) = inputRight z)
  let s5 := s4 ∪ {verifyBit}
  have hfoundH5 : foundH ∈ s5 := Or.inl (Or.inl (Or.inr (Or.inl (Or.inl rfl))))
  have hfoundA5 : foundA ∈ s5 := Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl rfl)))))
  have hint5 : intervalBit ∈ s5 := Or.inl (Or.inr (Or.inr rfl))
  have hverify5 : verifyBit ∈ s5 := Or.inr rfl
  have hshort5 : shortBit ∈ s5 := Or.inl (Or.inl (Or.inl (Or.inr (Or.inr rfl))))
  have hand1 := (Synthesis.of_mem hfoundH5).and (Synthesis.of_mem hfoundA5)
  have hand2 := hand1.and (Synthesis.of_mem hverify5)
  have hand3 := hand2.and (Synthesis.of_mem hint5)
  have hfinal := (Synthesis.of_mem hshort5).or hand3
  have hchain := hconst.trans
    ((hdy.union (hxOrb.union hyOrb)).trans
      (((hmSynth.union heSynth).union hshortX).trans
        ((hmarkSynth.union hanchorSynth).trans
          ((haOrb.union hint).trans
            (hverify.trans hfinal)))))
  obtain ⟨out, hout, hsize⟩ := hchain.exists_circuit
  refine ⟨out, fun z hyPos => ?_, hsize.trans ?_⟩
  · rw [hout z]
    change (shortBit z || (foundH z && foundA z && verifyBit z && intervalBit z)) = true ↔ _
    let hChosen : BitString n :=
      if h : foundH z = true then
        f^[(Classical.choose ((hmarkSpec z).1 h)).val] (inputLeft z)
      else inputLeft z
    have hHsound : foundH z = true →
        hChosen ∈ forestMarks f tables.H ∧
          ∃ d ≤ 2 * L, f^[d] (inputLeft z) = hChosen := by
      intro hf
      have hspec := Classical.choose_spec ((hmarkSpec z).1 hf)
      set j := Classical.choose ((hmarkSpec z).1 hf)
      have hjeq : hChosen = f^[j.val] (inputLeft z) := dite_eq_left_of_eq_true (eq_true hf)
      exact ⟨hjeq ▸ hspec.1, j.val, Nat.le_of_lt_succ j.isLt, hjeq.symm⟩
    have hHcomplete : (∃ d ≤ 2 * L, f^[d] (inputLeft z) ∈ forestMarks f tables.H) →
        foundH z = true := by
      rintro ⟨d, hd, hmem⟩
      exact (hmarkSpec z).2 ⟨⟨d, Nat.lt_succ_of_le hd⟩, hmem⟩
    have hAsound : foundA z = true → ForestAnchor f tables.H L (inputRight z) (anchorState z) :=
      fun hf => ((hanchorSpec z).1 hf).1
    have hAcomplete : (∃ b, ForestAnchor f tables.H L (inputRight z) b) → foundA z = true :=
      (hanchorSpec z).2
    have hnav := forest_navigation_spec f tables.H L hL tables.cover tables.low tables.high
      tables.interval (inputLeft z) (inputRight z) hChosen (anchorState z) hyPos
      (foundH z) (foundA z) hHsound hHcomplete hAsound hAcomplete
    rw [hnav]
    have hshortIff : shortBit z = true ↔ ∃ i ≤ 2 * L, f^[i] (inputLeft z) = inputRight z := by
      simp only [shortBit, decide_eq_true_eq]
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨j.val, Nat.le_of_lt_succ j.isLt, hj⟩
      · rintro ⟨i, hi, he⟩
        exact ⟨⟨i, Nat.lt_succ_of_le hi⟩, he⟩
    have hverifyIff : verifyBit z = true ↔
        ∃ i ≤ 2 * L, f^[i] (anchorState z) = inputRight z := by
      simp only [verifyBit, decide_eq_true_eq]
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨j.val, Nat.le_of_lt_succ j.isLt, hj⟩
      · rintro ⟨i, hi, he⟩
        exact ⟨⟨i, Nat.lt_succ_of_le hi⟩, he⟩
    have hintIff (hfH : foundH z = true) (hfA : foundA z = true) :
        intervalBit z = true ↔
          (tables.low (anchorState z) ≤ tables.low hChosen ∧
            tables.low hChosen ≤ tables.high (anchorState z)) := by
      have hmEq : markLabels z = forestLabelWord tables.low tables.high hChosen := by
        have hspec := Classical.choose_spec ((hmarkSpec z).1 hfH)
        have hjeq : hChosen = f^[(Classical.choose ((hmarkSpec z).1 hfH)).val] (inputLeft z) :=
          dite_eq_left_of_eq_true (eq_true hfH)
        rw [hjeq]
        exact hspec.2
      have haEq : anchorLabels z = forestLabelWord tables.low tables.high (anchorState z) :=
        ((hanchorSpec z).1 hfA).2
      dsimp only [intervalBit]
      rw [hmEq, haEq]
      exact forest_label_interval tables.low tables.high (anchorState z) hChosen
    rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      hshortIff, hverifyIff]
    constructor
    · rintro (hs | ⟨⟨⟨hfH, hfA⟩, hv⟩, hi⟩)
      · exact Or.inl hs
      · exact Or.inr ⟨hfH, hfA, hv, (hintIff hfH hfA).mp hi⟩
    · rintro (hs | ⟨hfH, hfA, hv, hi⟩)
      · exact Or.inl hs
      · exact Or.inr ⟨⟨⟨hfH, hfA⟩, hv⟩, (hintIff hfH hfA).mpr hi⟩
  · unfold transientForestCost
    dsimp only [Q, K]
    rw [show 2 * L + 1 + 1 = 2 * L + 2 by omega]
    nlinarith

end Cslib.Circuits.Boolean.Iteration
