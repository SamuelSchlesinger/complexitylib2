/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.InputTime
public import Complexity.Computability.Circuit.Boolean.Iteration.NavigationFeatures

/-!
# Circuit synthesis for reachability and first hitting times

This module synthesizes the navigation word `(reaches f x y, hittingTime f x y)` on pair inputs
`z : BitString (n + n)` in two ways:
* `synthesis_navigation_given_flag`: when a circuit `transientReach` already decides reachability on
  transient targets (`0 < transientDepth f y`), we combine two depth circuits, two cycle-label
  circuits, a streaming modular difference (`synthesis_subMod`), and word arithmetic to output
  `navigationBits f (inputLeft z) (inputRight z)` without evaluating a variable-time iterate;
* `synthesis_navigation`: when no external transient-reachability circuit is supplied, we evaluate
  `f^[transientDepth f x - transientDepth f y] x` by binary powering (`synthesis_binary_powering`)
  to decide transient reachability directly.

## Main results

* `Cslib.Circuits.Boolean.Iteration.synthesis_navigation_given_flag`: synthesizes `navigationBits`
  using an external transient-reachability circuit.
* `Cslib.Circuits.Boolean.Iteration.synthesis_navigation`: synthesizes `navigationBits` using
  binary powering for the transient check.

## References

* Adapted from `lean/Proofs/NavigationSynthesis.lean` in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open FunctionalGraph

attribute [local instance] lexOrder

variable {n : ℕ}

/-- Combine depth, cycle-label, and a supplied transient-reachability flag into the exact
reachability bit and first hitting time. -/
theorem synthesis_navigation_given_flag (f : BitString n → BitString n)
    (depth : Circuit signature n (n + 2))
    (hd : ∀ x, word (depth.eval interpretation x) =
      BitVec.ofNat (n + 2) (transientDepth f x))
    (label : Circuit signature n (labelWidth n))
    (hl : ∀ x, label.eval interpretation x = canonicalLabel f x)
    (transientReach : Circuit signature (n + n) 1)
    (htr : ∀ z, 0 < transientDepth f (inputRight z) →
      (transientReach.eval interpretation z 0 = true ↔
        ∃ t, f^[t] (inputLeft z) = inputRight z)) :
    Synthesis interpretation (inputs (n + n))
      (Set.range fun i z => navigationBits f (inputLeft z) (inputRight z) i)
      (2 + 2 * depth.size + 2 * label.size + transientReach.size +
        50 * (n + 4) ^ 2 + (49 * n + 138)) := by
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
  have hdx := synthesis_depthWord f depth hd s0 inputLeft hleft (hc0 false)
  have hdy := synthesis_depthWord f depth hd s0 inputRight hright (hc0 false)
  have hlx := synthesis_label_parts f label hl s0 inputLeft hleft
  have hly := synthesis_label_parts f label hl s0 inputRight hright
  have hfeatures := (hdx.union hdy).union (hlx.union hly)
  let s1 := s0 ∪ ((wordWires (fun z => depthWord f (inputLeft z)) ∪
      wordWires (fun z => depthWord f (inputRight z))) ∪
    ((wires (fun z => canonicalCycle f (inputLeft z)) ∪
        wordWires (fun z => lengthWord f (inputLeft z)) ∪
        wordWires (fun z => phaseWord f (inputLeft z))) ∪
      (wires (fun z => canonicalCycle f (inputRight z)) ∪
        wordWires (fun z => lengthWord f (inputRight z)) ∪
        wordWires (fun z => phaseWord f (inputRight z)))))
  have hc1 (b : Bool) : (fun _ : BitString (n + n) => b) ∈ s1 := Or.inl (hc0 b)
  have hdx1 (bit : Fin (n + 3)) :
      (fun z => (depthWord f (inputLeft z)).getLsbD bit.val) ∈ s1 :=
    Or.inr (Or.inl (Or.inl ⟨bit, rfl⟩))
  have hdy1 (bit : Fin (n + 3)) :
      (fun z => (depthWord f (inputRight z)).getLsbD bit.val) ∈ s1 :=
    Or.inr (Or.inl (Or.inr ⟨bit, rfl⟩))
  have hrepx1 : wires (fun z => canonicalCycle f (inputLeft z)) ⊆ s1 :=
    fun _ h => Or.inr (Or.inr (Or.inl (Or.inl (Or.inl h))))
  have hell1 (bit : Fin (n + 3)) :
      (fun z => (lengthWord f (inputLeft z)).getLsbD bit.val) ∈ s1 :=
    Or.inr (Or.inr (Or.inl (Or.inl (Or.inr ⟨bit, rfl⟩))))
  have hpx1 (bit : Fin (n + 3)) :
      (fun z => (phaseWord f (inputLeft z)).getLsbD bit.val) ∈ s1 :=
    Or.inr (Or.inr (Or.inl (Or.inr ⟨bit, rfl⟩)))
  have hrepy1 : wires (fun z => canonicalCycle f (inputRight z)) ⊆ s1 :=
    fun _ h => Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))
  have hpy1 (bit : Fin (n + 3)) :
      (fun z => (phaseWord f (inputRight z)).getLsbD bit.val) ∈ s1 :=
    Or.inr (Or.inr (Or.inr (Or.inr ⟨bit, rfl⟩)))
  let diff := fun z => navigationGap f (inputLeft z) (inputRight z)
  have hsub : Synthesis interpretation s1 (wordWires diff) (13 * (n + 3) + 1) :=
    Synthesis.word_sub (s := s1)
      (fun z => depthWord f (inputLeft z)) (fun z => depthWord f (inputRight z)) hdx1 hdy1
  have hyZero := Synthesis.word_eq_const (s := s1)
    (fun z => depthWord f (inputRight z)) hdy1 0
  have hrepEq := synthesis_bits_eq s1
    (fun z => canonicalCycle f (inputLeft z)) (fun z => canonicalCycle f (inputRight z))
    hrepx1 hrepy1
  have htrSynth : Synthesis interpretation s1
      {fun z => transientReach.eval interpretation z 0} transientReach.size := by
    refine (Synthesis.circuit (I := interpretation) (s := s1) transientReach
      (fun i z => z i) (fun i => Or.inl (Or.inl ⟨i, rfl⟩))).mono Set.Subset.rfl ?_ le_rfl
    rintro _ rfl
    exact ⟨0, rfl⟩
  let sumx := fun z => phaseWord f (inputLeft z) + depthWord f (inputLeft z)
  have hsumx := Synthesis.word_add (s := s1)
    (fun z => phaseWord f (inputLeft z))
    (fun z => depthWord f (inputLeft z)) hpx1 hdx1
  let s2 := s1 ∪ (((wordWires diff ∪
    {fun z => decide (depthWord f (inputRight z) = 0)}) ∪
      {fun z => decide (canonicalCycle f (inputLeft z) = canonicalCycle f (inputRight z))}) ∪
      ({fun z => transientReach.eval interpretation z 0} ∪ wordWires sumx))
  have hc2 (b : Bool) : (fun _ : BitString (n + n) => b) ∈ s2 := Or.inl (hc1 b)
  let cycDist := fun z => navigationDistance f (inputLeft z) (inputRight z)
  have hsubm : Synthesis interpretation s2 (wordWires cycDist) (50 * (n + 4) ^ 2) :=
    synthesis_subMod s2
      (fun z => phaseWord f (inputRight z))
      sumx
      (fun z => lengthWord f (inputLeft z))
      (fun bit => Or.inl (hpy1 bit))
      (fun bit => Or.inr (Or.inr (Or.inr ⟨bit, rfl⟩)))
      (fun bit => Or.inl (hell1 bit))
      (hc2 false)
  let s3 := s2 ∪ wordWires cycDist
  have hcycAdd := Synthesis.word_add (s := s3)
    (fun z => depthWord f (inputLeft z)) cycDist
    (fun bit => Or.inl (Or.inl (hdx1 bit)))
    (fun bit => Or.inr ⟨bit, rfl⟩)
  let cycTime := fun z => depthWord f (inputLeft z) + cycDist z
  let s4 := s3 ∪ wordWires cycTime
  have hflagMux : Synthesis interpretation s4
      {fun z => if decide (depthWord f (inputRight z) = 0)
        then decide (canonicalCycle f (inputLeft z) = canonicalCycle f (inputRight z))
        else transientReach.eval interpretation z 0} 4 :=
    Synthesis.mux
      (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr rfl))))))
      (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr rfl)))))
      (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl rfl)))))
  have htimeMux := Synthesis.word_mux (s := s4) cycTime diff
    (fun z => decide (depthWord f (inputRight z) = 0))
    (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr rfl))))))
    (fun bit => Or.inr ⟨bit, rfl⟩)
    (fun bit => Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl ⟨bit, rfl⟩))))))
  have hflagEq : (fun z => if decide (depthWord f (inputRight z) = 0)
      then decide (canonicalCycle f (inputLeft z) = canonicalCycle f (inputRight z))
      else transientReach.eval interpretation z 0) =
      fun z => navigationFlag f (inputLeft z) (inputRight z) := by
    funext z
    rw [navigationFlag_eq_reaches]
    simp only [decide_eq_true_eq, depthWord_eq_zero_iff]
    by_cases hz : transientDepth f (inputRight z) = 0
    · simp only [hz, ite_true, reaches]
      exact decide_eq_decide.mpr Iff.rfl
    · simp only [hz, ite_false]
      apply Bool.eq_iff_iff.mpr
      rw [htr z (Nat.pos_of_ne_zero hz), ← reaches_iff]
  have htimeEq : (fun z => if decide (depthWord f (inputRight z) = 0) then cycTime z else diff z) =
      fun z => navigationTime f (inputLeft z) (inputRight z) := by
    funext z
    simp only [navigationTime, cycTime, cycDist, diff, decide_eq_true_eq]
  rw [hflagEq] at hflagMux
  rw [htimeEq] at htimeMux
  have hchain := hconst.trans (hfeatures.trans
    ((((hsub.union hyZero).union hrepEq).union (htrSynth.union hsumx)).trans
      (hsubm.trans (hcycAdd.trans (hflagMux.union htimeMux)))))
  refine hchain.mono Set.Subset.rfl ?_ (by omega)
  rintro _ ⟨i, rfl⟩
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · exact Or.inl (funext fun z => by simp [navigationBits])
  · exact Or.inr ⟨⟨b.val, by omega⟩, funext fun z => by simp [navigationBits]⟩

/-- Combine depth, cycle-label, and binary-powering circuits into the navigation word. -/
theorem synthesis_navigation (f : BitString n → BitString n) (K : ℕ)
    (hpowers : ∀ j < n + 1, ∃ pow : Circuit signature n n,
      pow.Computes interpretation f^[2 ^ j] ∧ pow.size ≤ K)
    (depth : Circuit signature n (n + 2))
    (hd : ∀ x, word (depth.eval interpretation x) =
      BitVec.ofNat (n + 2) (transientDepth f x))
    (label : Circuit signature n (labelWidth n))
    (hl : ∀ x, label.eval interpretation x = canonicalLabel f x) :
    Synthesis interpretation (inputs (n + n))
      (Set.range fun i z => navigationBits f (inputLeft z) (inputRight z) i)
      (4 + 4 * depth.size + 2 * label.size + (n + 1) * (K + 4 * n) +
        50 * (n + 4) ^ 2 + (73 * n + 198)) := by
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
  have hdx := synthesis_depthWord f depth hd s0 inputLeft hleft (hc0 false)
  have hdy := synthesis_depthWord f depth hd s0 inputRight hright (hc0 false)
  let s1 := s0 ∪ (wordWires (fun z => depthWord f (inputLeft z)) ∪
    wordWires (fun z => depthWord f (inputRight z)))
  have hdx1 (bit : Fin (n + 3)) :
      (fun z => (depthWord f (inputLeft z)).getLsbD bit.val) ∈ s1 :=
    Or.inr (Or.inl ⟨bit, rfl⟩)
  have hdy1 (bit : Fin (n + 3)) :
      (fun z => (depthWord f (inputRight z)).getLsbD bit.val) ∈ s1 :=
    Or.inr (Or.inr ⟨bit, rfl⟩)
  let diff := fun z => navigationGap f (inputLeft z) (inputRight z)
  have hsub : Synthesis interpretation s1 (wordWires diff) (13 * (n + 3) + 1) :=
    Synthesis.word_sub (s := s1)
      (fun z => depthWord f (inputLeft z)) (fun z => depthWord f (inputRight z)) hdx1 hdy1
  have hult := Synthesis.word_ult (s := s1)
    (fun z => depthWord f (inputLeft z)) (fun z => depthWord f (inputRight z)) hdx1 hdy1
  let s2 : Set (BooleanFunction (n + n)) := s1 ∪ (wordWires diff ∪
    {fun z : BitString (n + n) => (depthWord f (inputLeft z)).ult (depthWord f (inputRight z))})
  have hleSynth : Synthesis interpretation s2
      {fun z => !(depthWord f (inputLeft z)).ult (depthWord f (inputRight z))} 1 :=
    (Synthesis.of_mem (Or.inr (Or.inr rfl))).not
  let diffBits : BitString (n + n) → BitString (n + 1) :=
    fun z (i : Fin (n + 1)) => (diff z).getLsbD i.val
  have hvar := synthesis_binary_powering (m := n + 1) f K hpowers s2 inputLeft diffBits
    (fun _ h => Or.inl (Or.inl (hleft h)))
    (by rintro _ ⟨i, rfl⟩; exact Or.inr (Or.inl ⟨⟨i.val, by omega⟩, rfl⟩))
  let s3 : Set (BooleanFunction (n + n)) := s2 ∪
    ({fun z : BitString (n + n) => !(depthWord f (inputLeft z)).ult (depthWord f (inputRight z))} ∪
      wires (fun z => f^[(word (diffBits z)).toNat] (inputLeft z)))
  have hmatchEq := synthesis_bits_eq s3
    (fun z => f^[(word (diffBits z)).toNat] (inputLeft z)) inputRight
    (fun _ h => Or.inr (Or.inr h))
    (fun _ h => Or.inl (Or.inl (Or.inl (hright h))))
  let s4 : Set (BooleanFunction (n + n)) :=
    s3 ∪ {fun z : BitString (n + n) =>
      decide (f^[(word (diffBits z)).toNat] (inputLeft z) = inputRight z)}
  have htrFlag : Synthesis interpretation s4
      {fun z => (!(depthWord f (inputLeft z)).ult (depthWord f (inputRight z))) &&
        decide (f^[(word (diffBits z)).toNat] (inputLeft z) = inputRight z)} 1 :=
    (Synthesis.of_mem (Or.inl (Or.inr (Or.inl rfl)))).and (Synthesis.of_mem (Or.inr rfl))
  have htrAll := hconst.trans ((hdx.union hdy).trans ((hsub.union hult).trans
    ((hleSynth.union hvar).trans (hmatchEq.trans htrFlag))))
  obtain ⟨transientReach, htrEval, htrSize⟩ := htrAll.exists_circuit
  have htrSpec (z : BitString (n + n)) (hy : 0 < transientDepth f (inputRight z)) :
      transientReach.eval interpretation z 0 = true ↔
        ∃ t, f^[t] (inputLeft z) = inputRight z := by
    rw [htrEval z]
    change ((!(depthWord f (inputLeft z)).ult (depthWord f (inputRight z))) &&
      decide (f^[(word (diffBits z)).toNat] (inputLeft z) = inputRight z)) = true ↔ _
    rw [Bool.and_eq_true, Bool.not_eq_true', BitVec.ult, decide_eq_false_iff_not, not_lt,
      toNat_depthWord, toNat_depthWord, decide_eq_true_eq]
    have hnotper : inputRight z ∉ Function.periodicPts f :=
      fun h => ne_of_gt hy ((transientDepth_eq_zero_iff f (inputRight z)).mpr h)
    rw [exists_iterate_eq_iff_of_not_mem_periodicPts f (inputLeft z) (inputRight z) hnotper]
    have hdiffToNat (hle : transientDepth f (inputRight z) ≤ transientDepth f (inputLeft z)) :
        (word (diffBits z)).toNat =
          transientDepth f (inputLeft z) - transientDepth f (inputRight z) := by
      have hw : word (diffBits z) = (diff z).setWidth (n + 1) := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        rw [getLsbD_word _ ⟨i, hi⟩]
        simp [diffBits, hi]
      have hlt :
          transientDepth f (inputLeft z) - transientDepth f (inputRight z) < 2 ^ (n + 1) := by
        have := transientDepth_lt_two_pow f (inputLeft z)
        have hpow1 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ']
        lia
      rw [hw, BitVec.toNat_setWidth, toNat_navigationGap f _ _ hle, Nat.mod_eq_of_lt hlt]
    constructor
    · rintro ⟨hle, he⟩
      exact ⟨hle, by rwa [hdiffToNat hle] at he⟩
    · rintro ⟨hle, he⟩
      exact ⟨hle, by rwa [hdiffToNat hle]⟩
  have hmain := synthesis_navigation_given_flag f depth hd label hl transientReach htrSpec
  refine hmain.mono Set.Subset.rfl Set.Subset.rfl ?_
  omega

end Cslib.Circuits.Boolean.Iteration
