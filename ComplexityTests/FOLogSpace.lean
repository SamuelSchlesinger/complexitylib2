/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.LogSpace.FirstOrder
import ComplexityTests.FaginEncoding

/-!
# Tests: first-order model checking in logarithmic space

Concrete sentences over the vocabulary of graphs and over a nullary vocabulary have query
languages in `L`; the problems are nontrivial (an encoded structure in, one out, including the
empty structure), malformed inputs are out, the definable-class corollary applies, and the usual
closure properties of `L` carry over. Axiom guards cover the headline results and the
logarithmic-space machinery: query machines and counter programs.
-/

namespace ComplexityTests.FOLogSpace

open FirstOrder Language Structure CategoryTheory Cslib.Logic Cslib.Complexity
open ComplexityTests.FaginEncoding

/-- Some vertex has a loop. -/
def hasLoop : Language.graph.Sentence :=
  (adj.boundedFormula₂ (Term.var (Sum.inr 0)) (Term.var (Sum.inr 0))).ex

/-- Every vertex has a loop. -/
def allLoops : Language.graph.Sentence :=
  (adj.boundedFormula₂ (Term.var (Sum.inr 0)) (Term.var (Sum.inr 0))).all

/-- The nullary relation holds. -/
def nullaryHolds : nullaryLanguage.Sentence := Relations.boundedFormula nullarySymbol ![]

/-! ### Membership in `L` -/

example : graphVocabulary.queryLanguage {M | M ⊨ hasLoop} ∈ L encStructure :=
  graphVocabulary.queryLanguage_mem_L hasLoop

example : graphVocabulary.queryLanguage {M | M ⊨ allLoops} ∈ L encStructure :=
  graphVocabulary.queryLanguage_mem_L allLoops

/-- Nullary relations are read from their one-bit tables. -/
example : nullaryVocabulary.queryLanguage {M | M ⊨ nullaryHolds} ∈ L encStructure :=
  nullaryVocabulary.queryLanguage_mem_L nullaryHolds

/-- The corollary for definable classes. -/
example : graphVocabulary.queryLanguage {M | M ⊨ hasLoop} ∈ L encStructure :=
  FO.Definable.queryLanguage_mem_L graphVocabulary ⟨hasLoop, fun _ _ => Iff.rfl⟩

/-- The complement, within all inputs, and polynomial time. -/
example : (graphVocabulary.queryLanguage {M | M ⊨ hasLoop})ᶜ ∈ L encStructure :=
  compl_mem_L (graphVocabulary.queryLanguage_mem_L hasLoop)

example : graphVocabulary.queryLanguage {M | M ⊨ hasLoop} ∈ P encStructure :=
  L_subset_P (graphVocabulary.queryLanguage_mem_L hasLoop)

example : graphVocabulary.queryLanguage {M | M ⊨ hasLoop} ∈ NL encStructure :=
  L_subset_NL (graphVocabulary.queryLanguage_mem_L hasLoop)

/-! ### The problems are nontrivial -/

theorem realize_hasLoop (a : EncodedStructure) :
    graphVocabulary.decoded a ⊨ hasLoop ↔
      ∃ x : Fin a.1, (graphVocabulary.table a ⟨2, adj⟩).getD (tupleIndex ![x, x]) false = true := by
  simp only [hasLoop, Sentence.Realize, Formula.Realize, BoundedFormula.realize_ex,
    BoundedFormula.realize_rel₂]
  rfl

theorem realize_allLoops (a : EncodedStructure) :
    graphVocabulary.decoded a ⊨ allLoops ↔
      ∀ x : Fin a.1, (graphVocabulary.table a ⟨2, adj⟩).getD (tupleIndex ![x, x]) false = true := by
  simp only [allLoops, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_rel₂]
  rfl

/-- A vertex with a loop is in. -/
example : ((1, [ [true] ]) : EncodedStructure) ∈
    graphVocabulary.queryLanguage {M | M ⊨ hasLoop} := by
  refine ⟨by decide +kernel, (realize_hasLoop _).mpr ⟨0, ?_⟩⟩
  decide +kernel

/-- The edge has no loop. -/
example : edge ∉ graphVocabulary.queryLanguage {M | M ⊨ hasLoop} := by
  rintro ⟨-, h⟩
  obtain ⟨x, hx⟩ := (realize_hasLoop _).mp h
  revert hx
  fin_cases x <;> decide +kernel

/-- **The empty structure**: every vertex of the empty graph has a loop, vacuously, and none
has one. -/
example : ((0, [ [] ]) : EncodedStructure) ∈
    graphVocabulary.queryLanguage {M | M ⊨ allLoops} :=
  ⟨by decide +kernel, (realize_allLoops _).mpr fun x => x.elim0⟩

example : ((0, [ [] ]) : EncodedStructure) ∉
    graphVocabulary.queryLanguage {M | M ⊨ hasLoop} := by
  rintro ⟨-, h⟩
  obtain ⟨x, -⟩ := (realize_hasLoop _).mp h
  exact x.elim0

/-- Malformed inputs are out, even when the sentence holds vacuously in the decoded structure. -/
example : ((0, []) : EncodedStructure) ∉ graphVocabulary.queryLanguage {M | M ⊨ allLoops} :=
  fun h => absurd h.1 (by decide +kernel)

/-! ### Axioms -/

/--
info: 'Cslib.Logic.Vocabulary.queryLanguage_mem_L' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.Vocabulary.queryLanguage_mem_L

/--
info: 'Cslib.Logic.FO.Definable.queryLanguage_mem_L' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Definable.queryLanguage_mem_L

/--
info: 'Cslib.Logic.Vocabulary.reaches_shapeCode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.Vocabulary.reaches_shapeCode

/--
info: 'Cslib.Logic.Vocabulary.reaches_compile' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.Vocabulary.reaches_compile

/--
info: 'Turing.QueryMachine.computableInLogSpace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.QueryMachine.computableInLogSpace

/--
info: 'Turing.CounterProgram.computableInLogSpace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.CounterProgram.computableInLogSpace

/--
info: 'Turing.CounterProgram.computableInLogSpace_of_reaches' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.CounterProgram.computableInLogSpace_of_reaches

end ComplexityTests.FOLogSpace
