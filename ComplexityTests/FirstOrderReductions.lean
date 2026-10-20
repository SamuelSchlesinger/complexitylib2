/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Fagin.SAT
import Complexity.Logics.FirstOrder.Problems.ColoringReduction
import Complexity.Logics.FirstOrder.Problems.ColoringToCNF
import Complexity.Logics.FirstOrder.Problems.IndependentSetReduction
import Complexity.Logics.SecondOrder.Coloring
import Complexity.Logics.SecondOrder.IndependentSet

/-!
# Tests for order-free reductions to SAT and 3COL

Concrete CNF structures inside and outside SAT and 3SAT; the graphs of an unsatisfiable 3-CNF
structure, of the empty clause and of a clause with four literals, which are not three-colorable;
the compiled interpretation of a tagged interpretation, through `copiesEquiv`; clients of the
headline reductions (3COL and 3SAT reduce to SAT, 3SAT reduces to 3COL, and these compose); and
axiom guards. Milestone-two clients exercise the reverse coloring reduction, both outcomes of
the occurrence-graph reduction on a nontrivial universe, and the independent-set ESO sentence.
-/

namespace ComplexityTests.FirstOrderReductions

open FirstOrder Language Structure CategoryTheory Cslib.Logic Cslib.Logic.FO Cslib.Complexity

/-! ### Concrete CNF structures -/

/-- The formula `x ∧ ¬x`: element `0` names the clause `x₀`, element `1` the clause `¬x₀`. -/
@[instance_reducible]
def contradiction : cnf.Structure (Fin 2) where
  RelMap R x := match R with
    | .pos => x 0 = 0 ∧ x 1 = 0
    | .neg => x 0 = 1 ∧ x 1 = 0

/-- The formula `x`: element `0` names the clause `x₀`. -/
@[instance_reducible]
def unitClause : cnf.Structure (Fin 1) where
  RelMap R _ := match R with
    | .pos => True
    | .neg => False

/-- The formula with the empty clause. -/
@[instance_reducible]
def emptyClause : cnf.Structure (Fin 1) where
  RelMap _ _ := False

/-- Every element names the clause `x₀ ∨ x₁ ∨ ¬x₀ ∨ ¬x₁`, with four literals. -/
@[instance_reducible]
def wideClause : cnf.Structure (Fin 2) where
  RelMap _ _ := True

theorem not_satisfiable_contradiction : ¬(letI := contradiction; cnf.Satisfiable (Fin 2)) := by
  let _ := contradiction
  rintro ⟨A, hA⟩
  obtain ⟨y, ⟨⟨-, hy⟩, h⟩ | ⟨⟨h01, -⟩, -⟩⟩ := hA 0
  · obtain ⟨z, ⟨⟨h10, -⟩, -⟩ | ⟨⟨-, hz⟩, h'⟩⟩ := hA 1
    · simp at h10
    · change y = 0 at hy
      change z = 0 at hz
      subst hy hz
      exact h' h
  · simp at h01

theorem satisfiable_unitClause : letI := unitClause; cnf.Satisfiable (Fin 1) := by
  let _ := unitClause
  exact ⟨fun _ => True, fun _ => ⟨0, .inl ⟨trivial, trivial⟩⟩⟩

theorem not_satisfiable_emptyClause : ¬(letI := emptyClause; cnf.Satisfiable (Fin 1)) := by
  let _ := emptyClause
  rintro ⟨A, hA⟩
  obtain ⟨y, ⟨h, -⟩ | ⟨h, -⟩⟩ := hA 0 <;> exact h

theorem isThreeCNF_contradiction : letI := contradiction; cnf.IsThreeCNF (Fin 2) := by
  let _ := contradiction
  intro c
  rw [cnf.encard_literals_le_three_iff]
  rintro ⟨l, hlit, hl⟩
  have h0 (i : Fin 4) : (l i).2 = 0 := by
    have := hlit i
    rcases hb : (l i).1 <;> simp only [cnf.mem_literals, hb, cnf.lit_true, cnf.lit_false] at this
    · exact this.2
    · exact this.2
  have hinj : Function.Injective fun i => (l i).1 :=
    fun i j h => hl (Prod.ext h ((h0 i).trans (h0 j).symm))
  have := Fintype.card_le_of_injective _ hinj
  simp at this

theorem not_isThreeCNF_wideClause : ¬(letI := wideClause; cnf.IsThreeCNF (Fin 2)) := by
  let _ := wideClause
  intro h
  refine (cnf.encard_literals_le_three_iff 0).1 (h 0)
    ⟨![(true, 0), (true, 1), (false, 0), (false, 1)], fun _ => trivial, ?_⟩
  decide

/-- SAT has members and non-members, so the classes in the headline results are not trivial. -/
example : (letI := unitClause; (Bundled.of (Fin 1) : Bundled cnf.Structure)) ∈ cnf.SAT :=
  satisfiable_unitClause

example : (letI := contradiction; (Bundled.of (Fin 2) : Bundled cnf.Structure)) ∉
    cnf.ThreeSAT :=
  fun h => not_satisfiable_contradiction h.2

/-- The graph of the unsatisfiable 3-CNF structure `x ∧ ¬x` is not three-colorable. -/
example : ¬(letI := contradiction;
    graph.Colorable 3 (cnf.coloringInterpretation.Model (Fin 2))) := by
  let _ := contradiction
  rw [cnf.colorable_coloringInterpretation_iff]
  exact fun h => not_satisfiable_contradiction h.2

/-- The graph of the empty clause is not three-colorable. -/
example : ¬(letI := emptyClause;
    graph.Colorable 3 (cnf.coloringInterpretation.Model (Fin 1))) := by
  let _ := emptyClause
  rw [cnf.colorable_coloringInterpretation_iff]
  exact fun h => not_satisfiable_emptyClause h.2

/-- The graph of a clause with four literals is not three-colorable, although the clause is
satisfiable: it is not a 3-CNF structure. -/
example : ¬(letI := wideClause;
    graph.Colorable 3 (cnf.coloringInterpretation.Model (Fin 2))) := by
  let _ := wideClause
  rw [cnf.colorable_coloringInterpretation_iff]
  exact fun h => not_isThreeCNF_wideClause h.1

/-- The graph of the satisfiable formula `x` is three-colorable. -/
example : letI := unitClause; graph.Colorable 3 (cnf.coloringInterpretation.Model (Fin 1)) := by
  let _ := unitClause
  rw [cnf.colorable_coloringInterpretation_iff]
  exact ⟨cnf.isThreeCNF_of_subsingleton, satisfiable_unitClause⟩

/-- The compiled interpretation applied to `x ∧ ¬x`, a disjoint union of two copies of the graph
of the tagged interpretation, one for each ordered pair of distinct elements, is not
three-colorable. -/
example : ¬(letI := contradiction; graph.Colorable 3
    ((cnf.coloringInterpretation.toInterpretation cnf.coloringSubsingleton).Model (Fin 2))) := by
  let _ := contradiction
  intro h
  have h' := graph.Colorable.of_equiv (TaggedInterpretation.copiesEquiv _).symm h
  rw [graph.colorable_copies_iff, cnf.colorable_coloringInterpretation_iff] at h'
  exact not_satisfiable_contradiction h'.2

/-! ### Clients of the reductions -/

/-- **3COL reduces to SAT**, through the grounding of its defining sentence. -/
example : Reduces graph.ThreeColorable.{0} cnf.SAT.{0} :=
  graph.definable_ThreeColorable.reduces_SAT fun _ _ => graph.colorable_of_isEmpty

/-- **3SAT reduces to SAT**, through Fagin's theorem and the NP-hardness of SAT. -/
example : Reduces cnf.ThreeSAT.{0} cnf.SAT.{0} :=
  cnf.reduces_SAT_of_queryLanguage_mem_NP cnf.vocabulary cnf.isoClosed_ThreeSAT
    cnf.queryLanguage_ThreeSAT_mem_NP
    fun _ _ => ⟨cnf.isThreeCNF_of_isEmpty, cnf.satisfiable_of_isEmpty⟩

/-- The reductions compose: 3SAT reduces to 3COL, which reduces to SAT. -/
example : Reduces cnf.ThreeSAT.{0} cnf.SAT.{0} :=
  cnf.reduces_ThreeSAT_ThreeColorable.trans
    (graph.definable_ThreeColorable.reduces_SAT fun _ _ => graph.colorable_of_isEmpty)
    cnf.isoClosed_SAT

/-- 3COL is existential second-order definable, as it reduces to SAT. -/
example : ESO.Definable graph.ThreeColorable.{0} :=
  (ESO.definable_iff_reduces_SAT fun _ _ => graph.colorable_of_isEmpty).2
    (graph.definable_ThreeColorable.reduces_SAT fun _ _ => graph.colorable_of_isEmpty)

/-- The classes containing every empty structure that are first-order reducible to SAT are the
classes in NP closed under isomorphism; SAT itself is one. -/
example : Reduces cnf.SAT.{0} cnf.SAT.{0} :=
  (cnf.reduces_SAT_iff_isoClosed_and_queryLanguage_mem_NP cnf.vocabulary
    fun _ _ => cnf.satisfiable_of_isEmpty).2 ⟨cnf.isoClosed_SAT, cnf.queryLanguage_SAT_mem_NP⟩

/-- 3SAT reduces to classical 3COL by an order-free interpretation. -/
example : Reduces cnf.ThreeSAT.{0} graph.SimpleThreeColorable.{0} :=
  cnf.reduces_ThreeSAT_SimpleThreeColorable

/-! ### Milestone-two clients -/

/-- Every clause contains a positive literal, on a nontrivial universe. -/
@[instance_reducible]
def positiveClauses : cnf.Structure (Fin 2) where
  RelMap R _ := match R with
    | .pos => True
    | .neg => False

/-- The occurrence graph of a satisfiable nontrivial structure has the requested independent set. -/
example : letI := positiveClauses;
    (Bundled.of (cnf.independentSetInterpretation.Model (Fin 2)) : Bundled sizedGraph.Structure) ∈
      sizedGraph.IndependentSet := by
  let _ := positiveClauses
  rw [cnf.mem_independentSet_iff_satisfiable]
  exact ⟨fun _ => True, fun _ => ⟨0, .inl ⟨trivial, trivial⟩⟩⟩

/-- The contradiction has no independent set of the requested size. -/
example : ¬(letI := contradiction;
    (Bundled.of (cnf.independentSetInterpretation.Model (Fin 2)) : Bundled sizedGraph.Structure) ∈
      sizedGraph.IndependentSet) := by
  let _ := contradiction
  rw [cnf.mem_independentSet_iff_satisfiable]
  exact not_satisfiable_contradiction

/-- The ESO sentence rejects the same concrete no-instance. -/
example : ¬(letI := contradiction;
    sizedGraph.independentSetSentence.Realize
      (cnf.independentSetInterpretation.Model (Fin 2))) := by
  let _ := contradiction
  rw [sizedGraph.realize_independentSetSentence]
  change (Bundled.of (cnf.independentSetInterpretation.Model (Fin 2)) :
    Bundled sizedGraph.Structure) ∉ sizedGraph.IndependentSet
  rw [cnf.mem_independentSet_iff_satisfiable]
  exact not_satisfiable_contradiction

/-- The graph of a satisfiable unit clause maps back to a satisfiable 3-CNF structure. -/
example : letI := unitClause;
    cnf.IsThreeCNF
        (graph.cnfInterpretation.Model (cnf.coloringInterpretation.Model (Fin 1))) ∧
      cnf.Satisfiable
        (graph.cnfInterpretation.Model (cnf.coloringInterpretation.Model (Fin 1))) := by
  let _ := unitClause
  refine ⟨graph.isThreeCNF_cnfInterpretation, ?_⟩
  rw [graph.satisfiable_cnfInterpretation_iff, cnf.colorable_coloringInterpretation_iff]
  exact ⟨cnf.isThreeCNF_of_subsingleton, satisfiable_unitClause⟩

/-- The two order-free 3SAT/3COL interpretations compose. -/
example : Reduces cnf.ThreeSAT.{0} cnf.ThreeSAT.{0} :=
  cnf.reduces_ThreeSAT_ThreeColorable.trans graph.reduces_ThreeColorable_ThreeSAT
    cnf.isoClosed_ThreeSAT

example : ReducesNontrivial cnf.SAT.{0} sizedGraph.IndependentSet.{0} :=
  cnf.reducesNontrivial_SAT_IndependentSet

example : ESO.Definable sizedGraph.Clique.{0} := sizedGraph.definable_Clique

example : ESO.Definable sizedGraph.VertexCover.{0} := sizedGraph.definable_VertexCover

/-- The empty-clause coloring graph maps to an unsatisfiable 3-CNF structure. -/
example : ¬(letI := emptyClause;
    cnf.Satisfiable
      (graph.cnfInterpretation.Model (cnf.coloringInterpretation.Model (Fin 1)))) := by
  let _ := emptyClause
  rw [graph.satisfiable_cnfInterpretation_iff, cnf.colorable_coloringInterpretation_iff]
  exact fun h => not_satisfiable_emptyClause h.2

/-- A graph with a loop, even on a singleton universe, maps to an unsatisfiable CNF structure. -/
example : ¬(letI : Language.graph.Structure (Fin 1) := { RelMap := fun _ _ => True };
    cnf.Satisfiable (graph.cnfInterpretation.Model (Fin 1))) := by
  let : Language.graph.Structure (Fin 1) := { RelMap := fun _ _ => True }
  rw [graph.satisfiable_cnfInterpretation_iff]
  rintro ⟨f, hf⟩
  exact hf 0 0 trivial rfl

/-- The satisfiable unit clause supplies a concrete member of classical 3COL. -/
example : letI := unitClause;
    (Bundled.of (cnf.coloringInterpretation.Model (Fin 1)) : Bundled Language.graph.Structure) ∈
      graph.SimpleThreeColorable := by
  let _ := unitClause
  exact ⟨cnf.simpleGraph_coloringInterpretation cnf.isThreeCNF_of_subsingleton
    satisfiable_unitClause.literals_nonempty,
    cnf.colorable_coloringInterpretation_iff.2
      ⟨cnf.isThreeCNF_of_subsingleton, satisfiable_unitClause⟩⟩

/-- An unsatisfiable formula supplies a non-member of classical 3COL. -/
example : ¬(letI := contradiction;
    (Bundled.of (cnf.coloringInterpretation.Model (Fin 2)) : Bundled Language.graph.Structure) ∈
      graph.SimpleThreeColorable) := by
  let _ := contradiction
  exact fun h => not_satisfiable_contradiction
    (cnf.colorable_coloringInterpretation_iff.1 h.2).2

/-- The nontrivial notion is strictly weaker than unrestricted order-free reducibility. -/
example : ReducesNontrivial cnf.SAT.{0} sizedGraph.IndependentSet.{0} ∧
    ¬Reduces cnf.SAT.{0} sizedGraph.IndependentSet.{0} :=
  ⟨cnf.reducesNontrivial_SAT_IndependentSet, cnf.not_reduces_SAT_IndependentSet⟩

/-- Composing the occurrence graph with graph complementation gives a nontrivial reduction. -/
example : ReducesNontrivial cnf.SAT.{0} sizedGraph.Clique.{0} :=
  cnf.reducesNontrivial_SAT_IndependentSet.trans_reduces
    sizedGraph.qfReduces_IndependentSet_Clique.reduces sizedGraph.isoClosed_Clique

/-- Independent set exercises reflexivity and extension across the small structures. -/
example : Reduces sizedGraph.IndependentSet.{0} sizedGraph.IndependentSet.{0} :=
  .of_reducesNontrivial (.refl sizedGraph.isoClosed_IndependentSet)
    (fun _ _ _ => sizedGraph.mem_IndependentSet_of_subsingleton)
    (fun _ _ _ => sizedGraph.mem_IndependentSet_of_subsingleton)

/-- The tagged palette is nonempty, so its compiled interpretation preserves nontriviality and
can be followed by another reduction that only promises correctness on nontrivial structures. -/
example : ReducesNontrivial cnf.ThreeSAT.{0} graph.ThreeColorable.{0} := by
  apply ReducesNontrivial.trans_of_nontrivial
    (cnf.coloringInterpretation.toInterpretation (Interpretation.empty cnf Language.graph))
    ?_ (.refl graph.isoClosed_ThreeColorable) graph.isoClosed_ThreeColorable
  apply TaggedInterpretation.nontrivial_and_mem_iff_toInterpretation
    graph.isoClosed_ThreeColorable graph.copyInvariant_ThreeColorable
  · intro M _ _ _
    exact ⟨⟨.trueV, Fin.elim0, formula_realize_top⟩⟩
  · intro M _ _
    exact cnf.colorable_coloringInterpretation_iff.symm

/-- The nonempty-structure corollary applies even to a class excluding every empty structure. -/
example : ∃ (ι : Type) (_ : Finite ι) (I : Interpretation cnf cnf ι),
    ∀ (M : Bundled.{0} cnf.Structure) [Finite M] [Nonempty M],
      ¬IsEmpty M ↔ (Bundled.of (I.Model M) : Bundled cnf.Structure) ∈ cnf.SAT :=
  (ESO.Definable.of_fo FO.Definable.isEmpty.compl).exists_interpretation_SAT_of_nonempty

/-- The Fagin corollary has the same nonempty client. -/
example : ∃ (ι : Type) (_ : Finite ι) (I : Interpretation cnf cnf ι),
    ∀ (M : Bundled.{0} cnf.Structure) [Finite M] [Nonempty M],
      ¬IsEmpty M ↔ (Bundled.of (I.Model M) : Bundled cnf.Structure) ∈ cnf.SAT :=
  cnf.exists_interpretation_SAT_of_queryLanguage_mem_NP cnf.vocabulary
    FO.Definable.isEmpty.compl.isoClosed
    ((ESO.Definable.of_fo FO.Definable.isEmpty.compl).queryLanguage_mem_NP cnf.vocabulary)

/-- Membership follows from an order-free reduction to SAT. -/
example : cnf.vocabulary.queryLanguage cnf.ThreeSAT ∈ NP encStructure :=
  cnf.queryLanguage_mem_NP_of_reduces_SAT cnf.vocabulary
    (cnf.reduces_ThreeSAT_ThreeColorable.trans
      (graph.definable_ThreeColorable.reduces_SAT fun _ _ => graph.colorable_of_isEmpty)
      cnf.isoClosed_SAT)

/-! ### Axioms -/

/--
info: 'Cslib.Logic.ESO.Definable.reduces_SAT' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Definable.reduces_SAT

/--
info: 'Cslib.Logic.ESO.definable_iff_reduces_SAT' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.definable_iff_reduces_SAT

/--
info: 'Cslib.Logic.ESO.Sentence.satisfiable_groundInterpretation_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Sentence.satisfiable_groundInterpretation_iff

/--
info: 'Cslib.Logic.FO.cnf.reduces_SAT_of_queryLanguage_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.cnf.reduces_SAT_of_queryLanguage_mem_NP

/--
info: 'Cslib.Logic.FO.cnf.exists_interpretation_SAT_of_queryLanguage_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.cnf.exists_interpretation_SAT_of_queryLanguage_mem_NP

/--
info: 'Cslib.Logic.FO.cnf.queryLanguage_mem_NP_of_reduces_SAT' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.cnf.queryLanguage_mem_NP_of_reduces_SAT

/--
info: 'Cslib.Logic.FO.cnf.reduces_SAT_iff_isoClosed_and_queryLanguage_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.cnf.reduces_SAT_iff_isoClosed_and_queryLanguage_mem_NP

/--
info: 'Cslib.Logic.FO.cnf.queryLanguage_SAT_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.cnf.queryLanguage_SAT_mem_NP

/--
info: 'Cslib.Logic.FO.cnf.queryLanguage_ThreeSAT_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.cnf.queryLanguage_ThreeSAT_mem_NP

/--
info: 'Cslib.Logic.FO.cnf.definable_ThreeSAT' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.cnf.definable_ThreeSAT

/--
info: 'Cslib.Logic.FO.cnf.colorable_coloringInterpretation_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.cnf.colorable_coloringInterpretation_iff

/--
info: 'Cslib.Logic.FO.cnf.reduces_ThreeSAT_ThreeColorable' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.cnf.reduces_ThreeSAT_ThreeColorable

/--
info: 'Cslib.Logic.FO.cnf.reduces_ThreeSAT_SimpleThreeColorable' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.cnf.reduces_ThreeSAT_SimpleThreeColorable

/--
info: 'Cslib.Logic.FO.Reduces.of_tagged' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Reduces.of_tagged

/--
info: 'Cslib.Logic.FO.graph.reduces_ThreeColorable_ThreeSAT' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.graph.reduces_ThreeColorable_ThreeSAT

/--
info: 'Cslib.Logic.FO.cnf.reducesNontrivial_SAT_IndependentSet' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.cnf.reducesNontrivial_SAT_IndependentSet

/--
info: 'Cslib.Logic.FO.sizedGraph.definable_IndependentSet' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.sizedGraph.definable_IndependentSet

/--
info: 'Cslib.Logic.FO.sizedGraph.definable_Clique' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.sizedGraph.definable_Clique

/--
info: 'Cslib.Logic.FO.sizedGraph.definable_VertexCover' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.sizedGraph.definable_VertexCover

/--
info: 'Cslib.Logic.ESO.Definable.exists_interpretation_SAT_of_nonempty' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Definable.exists_interpretation_SAT_of_nonempty

/--
info: 'Cslib.Logic.FO.cnf.not_reduces_SAT_IndependentSet' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.cnf.not_reduces_SAT_IndependentSet

/--
info: 'Cslib.Logic.FO.cnf.mem_independentSet_iff_satisfiable' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.cnf.mem_independentSet_iff_satisfiable

/--
info: 'Cslib.Logic.FO.graph.satisfiable_cnfInterpretation_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.graph.satisfiable_cnfInterpretation_iff

/--
info: 'Cslib.Logic.FO.ReducesNontrivial.of_tagged' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.ReducesNontrivial.of_tagged

/--
info: 'Cslib.Logic.FO.Reduces.of_reducesNontrivial' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Reduces.of_reducesNontrivial

end ComplexityTests.FirstOrderReductions
