/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.FirstOrder.Problems.IndependentSet
import Complexity.Logics.FirstOrder.Projection.Graph
import Complexity.Tactic.FirstOrder

/-!
# Tests for first-order automation

Exercise `fo_qf`, `fo_simp` and `fo_reduction` on formulas, interpretations, projections and
reductions, including their documented failure modes: quantified formulas are not
quantifier-free, bare relation constructors block `simp`, and a domain formula that may fail
leaves the semantic goal about the interpreted structure. The classes of independent sets and
cliques are shown nonvacuous and distinct on a two-vertex structure.
-/

namespace ComplexityTests.FirstOrderAutomation

open FirstOrder Language Structure CategoryTheory Cslib.Logic Cslib.Logic.FO sizedGraph

/-! ### `fo_qf` -/

section QF

variable {L : Language} (R : L.Relations 2) (S : L.Relations 1)

example : (∼(rel₂ R (0 : Fin 2) 1) ⊔ varEq 0 1 ⇔ rel₁ S 0 ⊓ ⊤ : L.Formula (Fin 2)).IsQF := by
  fo_qf

example :
    (Formula.iInf fun i : Fin 3 => (rel₂ R i 0).relabel Fin.succ : L.Formula (Fin 4)).IsQF := by
  fo_qf

example : (le R (0 : Fin 2) 1 ⟹ lt R 1 0 : L.Formula (Fin 2)).IsQF := by
  fo_qf

example {φ : L.Formula (Fin 1)} (hφ : φ.IsQF) : (atVar φ (2 : Fin 3) ⊓ ∼(atVar φ 0)).IsQF := by
  fo_qf

example {L' : Language} [L'.IsRelational] {I : Interpretation L L' (Fin 2)} (hI : I.IsQF)
    {φ : L'.Formula (Fin 3)} (hφ : φ.IsQF) :
    (I.onFormula φ ⊓ I.domain.relabel fun i => (0, i)).IsQF := by
  fo_qf

example [L.IsRelational] : ((Interpretation.id L).comp (Interpretation.id L)).IsQF := by
  fo_qf

example {L' : Language} {I : Interpretation L L' (Fin 2)} (hI : I.IsQF) {n : ℕ}
    (R' : L'.Relations n) : (I.rel R' ⟹ ∼(I.rel R')).IsQF := by
  fo_qf

example {N N' L' : Language} {I : Projection N N' L L' (Fin 2)} (hI : I.IsQF) {n : ℕ}
    (R' : L'.Relations n) : ((I.rel R').not.relabel id).IsQF ∧ I.numeric.IsQF := by
  exact ⟨by fo_qf, by fo_qf⟩

/-- Without a hypothesis, an abstract interpretation is not known to be quantifier-free. -/
example {L' : Language} (_I : Interpretation L L' (Fin 2)) : True := by
  fail_if_success have : _I.IsQF := by fo_qf
  trivial

/-- A quantified formula is not quantifier-free, and `fo_qf` fails on it. -/
example : ¬ (∀' R.boundedFormula₂ &0 &0 : L.Sentence).IsQF := by
  fail_if_success have : (∀' R.boundedFormula₂ &0 &0 : L.Sentence).IsQF := by fo_qf
  exact BoundedFormula.not_all_isQF _

end QF

/-- Concrete interpretations are split by relation symbol and unfolded. -/
example : complementEdges.IsQF := by fo_qf

example : (complementEdges.comp complementSize).IsQF := by fo_qf

example (N : Language) : (Projection.offDiagonalComplement N).toInterpretation.IsQF := by fo_qf

example : ((Projection.offDiagonalComplement Language.empty).comp
    (Projection.offDiagonalComplement Language.empty)).IsQF := by
  fo_qf

/-- Closure under isomorphism is registered in the same rule set. -/
example : IsoClosed Clique.{0} := by fo_qf

/-! ### `fo_simp` -/

section Simp

variable {M : Type*} [sizedGraph.Structure M]

example (x : Fin 2 → M) :
    (∼(rel₂ sizedGraph.adj 0 1) ⊓ varEq 0 1 ⊔ rel₁ sizedGraph.size 1 :
      sizedGraph.Formula (Fin 2)).Realize x ↔
      ¬ RelMap sizedGraph.adj ![x 0, x 1] ∧ x 0 = x 1 ∨ RelMap sizedGraph.size ![x 1] := by
  fo_simp

example (x y : M) :
    (complementEdges.unitStructure M).RelMap sizedGraph.adj ![x, y] ↔
      ¬ RelMap sizedGraph.adj ![x, y] ∧ x ≠ y := by
  fo_simp

example (x : complementSize.Model M) :
    RelMap sizedGraph.size ![x] ↔ ¬ RelMap sizedGraph.size ![x.1 ()] := by
  fo_simp

example (x y : M) (h : (complementSize.unitStructure M).RelMap sizedGraph.adj ![x, y]) :
    RelMap sizedGraph.adj ![x, y] := by
  fo_simp at h
  exact h

/-- A bare constructor inside a formula is well typed only after unfolding the language, and
`fo_simp` makes no progress on it; the abbreviation `sizedGraph.adj` is rewritten. -/
example (x : Fin 2 → M) :
    (rel₂ (L := sizedGraph) .adj (0 : Fin 2) 1).Realize x ↔
      RelMap sizedGraph.adj ![x 0, x 1] := by
  fail_if_success fo_simp
  exact realize_rel₂ x _ 0 1

end Simp

/-! ### `fo_reduction` -/

/-- A first-order reduction which is not required to be quantifier-free. -/
example : Reduces IndependentSet.{0} Clique.{0} := by
  fo_reduction complementEdges [mem_IndependentSet, mem_Clique]
  exact fun _ _ => exists_congr fun _ => and_congr_right fun _ =>
    ⟨fun h _ hx _ hy hxy => ⟨h hx hy hxy, hxy⟩, fun h _ hx _ hy hxy => (h hx hy hxy).1⟩

/-- Restrict a structure to the elements of its size relation. -/
def restrictToSize : Interpretation sizedGraph sizedGraph Unit where
  domain := rel₁ sizedGraph.size ()
  rel
    | .adj => rel₂ sizedGraph.adj (0, ()) (1, ())
    | .size => rel₁ sizedGraph.size (0, ())

/-- All structures of the vocabulary `sizedGraph`. -/
abbrev allStructures : Set (Bundled.{0} sizedGraph.Structure) := Set.univ

/-- When the domain formula need not hold, the semantic goal is about the interpreted structure,
even though the target class is closed under isomorphism. -/
example (_hK : IsoClosed allStructures) : QFReduces allStructures allStructures := by
  fo_reduction restrictToSize
  guard_target =ₛ ∀ (M : Bundled.{0} sizedGraph.Structure) [Finite M], M ∈ allStructures ↔
    Bundled.of (c := sizedGraph.Structure) (restrictToSize.Model M) ∈ allStructures
  exact fun _ _ => Iff.rfl

/-! ### Nonvacuity of the classes -/

/-- Two vertices, both in the size relation, adjacent exactly when `edge` holds. -/
@[instance_reducible]
def twoVertices (edge : Prop) : sizedGraph.Structure (Fin 2) where
  RelMap
    | .adj, x => edge ∧ x 0 ≠ x 1
    | .size, _ => True

private theorem eq_univ_of_ncard_eq {s : Set (Fin 2)}
    (h : s.ncard = (Set.univ : Set (Fin 2)).ncard) : s = Set.univ :=
  Set.eq_of_subset_of_ncard_le (Set.subset_univ s) h.ge

/-- Without the edge, both vertices form an independent set but not a clique. -/
example : Bundled.mk (Fin 2) (twoVertices False) ∈ IndependentSet.{0} ∧
    Bundled.mk (Fin 2) (twoVertices False) ∉ Clique.{0} := by
  let _ := twoVertices False
  refine ⟨⟨Set.univ, rfl, fun _ _ _ _ _ h => h.1⟩, fun ⟨s, hs, hcl⟩ => ?_⟩
  rw [eq_univ_of_ncard_eq hs] at hcl
  exact (hcl (Set.mem_univ 0) (Set.mem_univ 1) (by decide)).1

/-- With the edge, both vertices form a clique but not an independent set. -/
example : Bundled.mk (Fin 2) (twoVertices True) ∈ Clique.{0} ∧
    Bundled.mk (Fin 2) (twoVertices True) ∉ IndependentSet.{0} := by
  let _ := twoVertices True
  refine ⟨⟨Set.univ, rfl, fun _ _ _ _ h => ⟨trivial, by simpa using h⟩⟩, fun ⟨s, hs, hind⟩ => ?_⟩
  rw [eq_univ_of_ncard_eq hs] at hind
  exact hind (Set.mem_univ 0) (Set.mem_univ 1) (by decide) ⟨trivial, by decide⟩

/-! ### Axioms -/

/--
info: 'Cslib.Logic.FO.sizedGraph.qfReduces_IndependentSet_Clique' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms qfReduces_IndependentSet_Clique

/--
info: 'Cslib.Logic.FO.sizedGraph.qfReduces_Clique_IndependentSet' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms qfReduces_Clique_IndependentSet

/--
info: 'Cslib.Logic.FO.sizedGraph.qfReduces_IndependentSet_VertexCover' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms qfReduces_IndependentSet_VertexCover

/--
info: 'Cslib.Logic.FO.sizedGraph.qfReduces_VertexCover_IndependentSet' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms qfReduces_VertexCover_IndependentSet

/--
info: 'Cslib.Logic.FO.sizedGraph.qfReduces_Clique_VertexCover' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms qfReduces_Clique_VertexCover

/--
info: 'Cslib.Logic.FO.sizedGraph.qfReduces_VertexCover_Clique' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms qfReduces_VertexCover_Clique

/--
info: 'Cslib.Logic.FO.sizedGraph.isoClosed_VertexCover' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isoClosed_VertexCover

/--
info: 'Cslib.Logic.FO.QFReduces.trans' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QFReduces.trans

/--
info: 'Cslib.Logic.FO.QFReduces.of_unitStructure' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QFReduces.of_unitStructure

/--
info: 'Cslib.Logic.FO.Projection.isQF_offDiagonalComplement' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Projection.isQF_offDiagonalComplement

end ComplexityTests.FirstOrderAutomation
