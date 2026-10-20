/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Fagin.SAT
import Complexity.Logics.FirstOrder.Problems.Coloring

/-!
# Tests for first-order reductions to SAT and 3COL

Concrete CNF structures inside and outside SAT, the graph of an unsatisfiable 3-CNF structure,
which is not three-colorable, clients of the headline reductions (3COL and 3SAT reduce to SAT,
3SAT reduces to 3COL, and these compose), and axiom guards.
-/

namespace ComplexityTests.FirstOrderReductions

open FirstOrder Language Structure CategoryTheory Cslib.Logic Cslib.Logic.FO Cslib.Complexity

/-! ### Concrete CNF structures -/

/-- The formula `x ∧ ¬x`: element `0` names the clause `x₀`, element `1` the clause `¬x₀`. -/
@[instance_reducible]
def contradiction : CNF.language.Structure (Fin 2) where
  RelMap R x := match R with
    | .pos => x 0 = 0 ∧ x 1 = 0
    | .neg => x 0 = 1 ∧ x 1 = 0

/-- The formula `x`: element `0` names the clause `x₀`. -/
@[instance_reducible]
def unitClause : CNF.language.Structure (Fin 1) where
  RelMap R _ := match R with
    | .pos => True
    | .neg => False

/-- The formula with the empty clause. -/
@[instance_reducible]
def emptyClause : CNF.language.Structure (Fin 1) where
  RelMap _ _ := False

theorem not_satisfiable_contradiction : ¬(letI := contradiction; CNF.Satisfiable (Fin 2)) := by
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

theorem satisfiable_unitClause : letI := unitClause; CNF.Satisfiable (Fin 1) := by
  let _ := unitClause
  exact ⟨fun _ => True, fun _ => ⟨0, .inl ⟨trivial, trivial⟩⟩⟩

theorem not_satisfiable_emptyClause : ¬(letI := emptyClause; CNF.Satisfiable (Fin 1)) := by
  let _ := emptyClause
  rintro ⟨A, hA⟩
  obtain ⟨y, ⟨h, -⟩ | ⟨h, -⟩⟩ := hA 0 <;> exact h

theorem isThreeCNF_contradiction : letI := contradiction; CNF.IsThreeCNF (Fin 2) := by
  let _ := contradiction
  intro c
  rw [CNF.encard_literals_le_three_iff]
  rintro ⟨l, hlit, hl⟩
  have h0 (i : Fin 4) : (l i).2 = 0 := by
    have := hlit i
    rcases hb : (l i).1 <;> simp only [CNF.mem_literals, hb, CNF.lit_true, CNF.lit_false] at this
    · exact this.2
    · exact this.2
  have hinj : Function.Injective fun i => (l i).1 :=
    fun i j h => hl (Prod.ext h ((h0 i).trans (h0 j).symm))
  have := Fintype.card_le_of_injective _ hinj
  simp at this

/-- SAT has members and non-members, so the classes in the headline results are not trivial. -/
example : (letI := unitClause; (Bundled.of (Fin 1) : Bundled CNF.language.Structure)) ∈ CNF.sat :=
  satisfiable_unitClause

example : (letI := contradiction; (Bundled.of (Fin 2) : Bundled CNF.language.Structure)) ∉
    CNF.threeSat :=
  fun h => not_satisfiable_contradiction h.2

/-- The graph of the unsatisfiable 3-CNF structure `x ∧ ¬x` is not three-colorable. -/
example : ¬(letI := contradiction;
    Coloring.Colorable 3 (CNF.coloringInterpretation.Model (Fin 2))) := by
  let _ := contradiction
  rw [CNF.colorable_coloringInterpretation_iff]
  exact fun h => not_satisfiable_contradiction h.2

/-- The graph of the satisfiable formula `x` is three-colorable. -/
example : letI := unitClause; Coloring.Colorable 3 (CNF.coloringInterpretation.Model (Fin 1)) := by
  let _ := unitClause
  rw [CNF.colorable_coloringInterpretation_iff]
  exact ⟨CNF.isThreeCNF_of_subsingleton, satisfiable_unitClause⟩

/-! ### Clients of the reductions -/

/-- **3COL reduces to SAT**, through the grounding of its defining sentence. -/
example : Reduces Coloring.threeCol.{0} CNF.sat.{0} :=
  Coloring.definable_threeCol.reduces_sat fun _ _ => Coloring.colorable_of_isEmpty

/-- **3SAT reduces to SAT**, through Fagin's theorem and the NP-hardness of SAT. -/
example : Reduces CNF.threeSat.{0} CNF.sat.{0} :=
  CNF.reduces_sat_of_mem_NP CNF.vocabulary CNF.isoClosed_threeSat CNF.queryLanguage_threeSat_mem_NP
    fun _ _ => ⟨CNF.isThreeCNF_of_isEmpty, CNF.satisfiable_of_isEmpty⟩

/-- The reductions compose: 3SAT reduces to 3COL, which reduces to SAT. -/
example : Reduces CNF.threeSat.{0} CNF.sat.{0} :=
  CNF.reduces_threeSat_threeCol.trans
    (Coloring.definable_threeCol.reduces_sat fun _ _ => Coloring.colorable_of_isEmpty)
    CNF.isoClosed_sat

/-- 3COL is in NP: it reduces to SAT, so it is existential second-order definable. -/
example : ESO.Definable Coloring.threeCol.{0} :=
  (ESO.definable_iff_reduces_sat fun _ _ => Coloring.colorable_of_isEmpty).2
    (Coloring.definable_threeCol.reduces_sat fun _ _ => Coloring.colorable_of_isEmpty)

/-- The class of finite structures in NP containing the empty structure are those reducible to
SAT; SAT itself is one. -/
example : Reduces CNF.sat.{0} CNF.sat.{0} :=
  (CNF.reduces_sat_iff_mem_NP CNF.vocabulary fun _ _ => CNF.satisfiable_of_isEmpty).2
    ⟨CNF.isoClosed_sat, CNF.queryLanguage_sat_mem_NP⟩

/-! ### Axioms -/

/--
info: 'Cslib.Logic.ESO.Definable.reduces_sat' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Definable.reduces_sat

/--
info: 'Cslib.Logic.ESO.definable_iff_reduces_sat' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.definable_iff_reduces_sat

/--
info: 'Cslib.Logic.FO.CNF.reduces_sat_of_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.CNF.reduces_sat_of_mem_NP

/--
info: 'Cslib.Logic.FO.CNF.reduces_sat_iff_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.CNF.reduces_sat_iff_mem_NP

/--
info: 'Cslib.Logic.FO.CNF.queryLanguage_sat_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.CNF.queryLanguage_sat_mem_NP

/--
info: 'Cslib.Logic.FO.CNF.reduces_threeSat_threeCol' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.CNF.reduces_threeSat_threeCol

/--
info: 'Cslib.Logic.FO.Reduces.of_tagged' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Reduces.of_tagged

end ComplexityTests.FirstOrderReductions
