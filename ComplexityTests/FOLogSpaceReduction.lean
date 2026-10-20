/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.LogSpace.FirstOrder.Reduction
import ComplexityTests.FOLogSpace

/-!
# Tests: order-free interpretations as logarithmic-space transducers

The total transducer applies to interpretations with a genuinely empty domain, and to dimension
zero, including on an empty input universe. Nullary output relations still have one-bit truth
tables in both cases. Malformed inputs produce malformed outputs. A nontrivial definable graph
query instantiates the reduction and both class-closure corollaries. Axiom guards cover the new
machine theorem and the headline reduction theorem.
-/

namespace ComplexityTests.FOLogSpaceReduction

open FirstOrder Language Structure CategoryTheory Cslib.Logic Cslib.Complexity
open FO FO.Interpretation ComplexityTests.FaginEncoding ComplexityTests.FOLogSpace

/-- An interpretation with no elements but a true nullary relation. -/
def emptyDomain : Interpretation Language.graph nullaryLanguage (Fin 1) where
  domain := ⊥
  rel _ := ⊤

/-- A zero-dimensional interpretation with one element and a false nullary relation. -/
def zeroDimension : Interpretation Language.graph nullaryLanguage (Fin 0) where
  domain := ⊤
  rel _ := ⊥

example : Turing.MultiTapeTM.ComputableInLogSpace
    (emptyDomain.encodedMap graphVocabulary nullaryVocabulary (Equiv.refl _))
    encStructure encStructure :=
  emptyDomain.computableInLogSpace_encodedMap graphVocabulary nullaryVocabulary (Equiv.refl _)

example : Turing.MultiTapeTM.ComputableInLogSpace
    (zeroDimension.encodedMap graphVocabulary nullaryVocabulary (Equiv.refl _))
    encStructure encStructure :=
  zeroDimension.computableInLogSpace_encodedMap graphVocabulary nullaryVocabulary (Equiv.refl _)

/-- The domain filter can discard every element of a nonempty input. The nullary relation's
one-bit table survives. -/
example : emptyDomain.encodedMap graphVocabulary nullaryVocabulary (Equiv.refl _) edge =
    (0, [ [true] ]) := by
  classical
  have ha : graphVocabulary.WellFormed edge := by decide +kernel
  rw [encodedMap, ite_eq_left ha]
  let _ := graphVocabulary.decode edge
  apply Prod.ext
  · change modelCard emptyDomain (Equiv.refl _) edge.1 = 0
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro u _
    rintro ⟨_, hd⟩
    exact hd
  · simp only [Vocabulary.encode, nullaryVocabulary, List.ofFn_succ, List.ofFn_zero]
    simp only [Vocabulary.relTable]
    simp only [FO.Interpretation.relMap_model]
    simp only [emptyDomain, Formula.Realize, BoundedFormula.realize_top, decide_true,
      List.ofFn_const]
    rfl

/-- A dimension-zero interpretation produces one element even on the empty input universe;
the false nullary relation is encoded by a one-bit false table. -/
example : zeroDimension.encodedMap graphVocabulary nullaryVocabulary (Equiv.refl _)
    (0, [ [] ]) = (1, [ [false] ]) := by
  classical
  have ha : graphVocabulary.WellFormed (0, [ [] ]) := by decide +kernel
  rw [encodedMap, ite_eq_left ha]
  let _ := graphVocabulary.decode (0, [ [] ])
  apply Prod.ext
  · change modelCard zeroDimension (Equiv.refl _) 0 = 1
    simp only [modelCard, domainRank, pow_zero, Finset.range_one, Finset.filter_singleton]
    have h : zeroDimension.InDomain (Equiv.refl _) 0 0 :=
      ⟨by decide, by simp [zeroDimension, Formula.Realize]⟩
    rw [ite_eq_left h]
    rfl
  · simp only [Vocabulary.encode, nullaryVocabulary, List.ofFn_succ, List.ofFn_zero]
    simp only [Vocabulary.relTable]
    simp only [FO.Interpretation.relMap_model]
    simp only [zeroDimension, Formula.Realize, BoundedFormula.realize_bot, decide_false,
      List.ofFn_const]
    rfl

/-- A malformed input cannot accidentally become a valid target instance. -/
example : ¬ nullaryVocabulary.WellFormed
    (zeroDimension.encodedMap graphVocabulary nullaryVocabulary (Equiv.refl _) (0, [])) := by
  have ha : ¬ graphVocabulary.WellFormed (0, []) := by decide +kernel
  rw [encodedMap, ite_eq_right ha]
  simp [Vocabulary.WellFormed]

private theorem loopClass_isoClosed :
    IsoClosed {M : Bundled Language.graph.Structure | M ⊨ hasLoop} :=
  (show Definable {M | M ⊨ hasLoop} from ⟨hasLoop, fun _ _ => Iff.rfl⟩).isoClosed

/-- The class has both positive and negative instances, as checked in `FOLogSpace`. -/
example : LogSpaceReducible encStructure encStructure
    (graphVocabulary.queryLanguage {M | M ⊨ hasLoop})
    (graphVocabulary.queryLanguage {M | M ⊨ hasLoop}) :=
  (Reduces.refl loopClass_isoClosed).logSpaceReducible graphVocabulary graphVocabulary
    loopClass_isoClosed

example : graphVocabulary.queryLanguage {M | M ⊨ hasLoop} ∈ L encStructure :=
  (Reduces.refl loopClass_isoClosed).queryLanguage_mem_L graphVocabulary graphVocabulary
    loopClass_isoClosed (graphVocabulary.queryLanguage_mem_L hasLoop)

example : graphVocabulary.queryLanguage {M | M ⊨ hasLoop} ∈ P encStructure :=
  (Reduces.refl loopClass_isoClosed).queryLanguage_mem_P graphVocabulary graphVocabulary
    loopClass_isoClosed (L_subset_P (graphVocabulary.queryLanguage_mem_L hasLoop))

/--
info: 'Cslib.Logic.FO.Interpretation.computableInLogSpace_encodedMap' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Interpretation.computableInLogSpace_encodedMap

/--
info: 'Cslib.Logic.FO.Reduces.logSpaceReducible' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Reduces.logSpaceReducible

/--
info: 'Cslib.Logic.FO.Reduces.queryLanguage_mem_L' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Reduces.queryLanguage_mem_L

/--
info: 'Cslib.Logic.FO.Reduces.queryLanguage_mem_P' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Reduces.queryLanguage_mem_P

end ComplexityTests.FOLogSpaceReduction
