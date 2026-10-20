/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Fagin.SAT
import Complexity.Logics.FirstOrder.Problems.ColoringReduction
import Complexity.Logics.SecondOrder.Coloring

/-!
# Tests for first-order reductions to SAT and 3COL

Concrete CNF structures inside and outside SAT and 3SAT; the graphs of an unsatisfiable 3-CNF
structure, of the empty clause and of a clause with four literals, which are not three-colorable;
the compiled interpretation of a tagged interpretation, through `copiesEquiv`; clients of the
headline reductions (3COL and 3SAT reduce to SAT, 3SAT reduces to 3COL, and these compose); and
axiom guards.
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

/-- The classes containing the empty structure that are first-order reducible to SAT are the
classes in NP closed under isomorphism; SAT itself is one. -/
example : Reduces cnf.SAT.{0} cnf.SAT.{0} :=
  (cnf.reduces_SAT_iff_isoClosed_and_queryLanguage_mem_NP cnf.vocabulary
    fun _ _ => cnf.satisfiable_of_isEmpty).2 ⟨cnf.isoClosed_SAT, cnf.queryLanguage_SAT_mem_NP⟩

/-- Classical 3COL is in NP, as 3SAT reduces to it and it reduces to SAT. -/
example : Reduces cnf.ThreeSAT.{0} graph.SimpleThreeColorable.{0} :=
  cnf.reduces_ThreeSAT_SimpleThreeColorable

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

end ComplexityTests.FirstOrderReductions
