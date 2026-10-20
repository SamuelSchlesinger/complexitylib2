/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.Expander.Existence
import Complexity.Logics.Propositional.Resolution.TseitinExpander

/-!
# Tests: Tseitin formulas and their resolution lower bounds

Tseitin formulas on a triangle and on a multigraph with a self-loop and parallel edges: incidence,
satisfiability by total charge, connectivity, and the width lower bound on the triangle;
satisfiability of the hypotheses of the expander bounds; and the axioms of the headline theorems.
-/

namespace ComplexityTests.ProofComplexity.Tseitin

open Cslib Cslib.Logic.PL Finset

/-! ### A triangle -/

/-- The triangle on `Fin 3`: edge `i` joins `i` and `i + 1`. -/
private def triangle : Fin 3 → Sym2 (Fin 3) := fun i => s(i, i + 1)

example : Multigraph.incidence triangle 0 = {0, 2} := by decide

private theorem connected_triangle : (Multigraph.toSimpleGraph triangle).Connected :=
  (Multigraph.connected_toSimpleGraph_iff triangle).2 ⟨⟨0⟩, by decide⟩

/-- One charged vertex: odd total charge, so unsatisfiable. -/
example : ¬ (CNF.tseitinFormula triangle fun v => decide (v = 0)).Satisfiable :=
  CNF.not_satisfiable_tseitinFormula (by decide)

/-- Two charged vertices: even total charge, so satisfiable on the connected triangle. -/
example : (CNF.tseitinFormula triangle fun v => decide (v ≠ 0)).Satisfiable :=
  (CNF.satisfiable_tseitinFormula_iff connected_triangle).2 (by decide)

/-- Every set of one or two vertices of the triangle has two edges leaving it, so `2 ≤ e(G)`. -/
private theorem two_le_minBalancedCut_triangle : 2 ≤ Multigraph.minBalancedCut triangle :=
  (Multigraph.le_minBalancedCut_iff triangle (by decide)).2 (by decide)

/-- Resolution refutations of the unsatisfiable Tseitin formula on the triangle have width at least
`2`. -/
example : ¬ (CNF.tseitinFormula triangle fun v => decide (v = 0)).RefutableInWidth 1 := fun h => by
  have := Tseitin.minBalancedCut_le_of_refutableInWidth connected_triangle h
  have := two_le_minBalancedCut_triangle
  omega

/-- The clauses of the Tseitin formula on the triangle have two literals, and there are at most
`3 * 2 ^ 2` of them. -/
example : (CNF.tseitinFormula triangle fun v => decide (v = 0)).length ≤ 3 * 2 ^ 2 :=
  CNF.length_tseitinFormula_le fun v => by revert v; decide

/-! ### Self-loops and parallel edges -/

/-- Two parallel edges between `0` and `1`, and a self-loop at `0`. -/
private def multi : Fin 3 → Sym2 (Fin 2) := ![s(0, 1), s(0, 1), s(0, 0)]

/-- The self-loop does not count towards the parity of its vertex. -/
example : Multigraph.incidence multi 0 = {0, 1} := by decide

private theorem connected_multi : (Multigraph.toSimpleGraph multi).Connected :=
  (Multigraph.connected_toSimpleGraph_iff multi).2 ⟨⟨0⟩, by decide⟩

example : ¬ (CNF.tseitinFormula multi ![true, false]).Satisfiable :=
  CNF.not_satisfiable_tseitinFormula (by decide)

example : (CNF.tseitinFormula multi ![true, true]).Satisfiable :=
  (CNF.satisfiable_tseitinFormula_iff connected_multi).2 (by decide)

/-! ### The hypotheses of the expander bounds are satisfiable -/

/-- The width bound for rotation maps applies to the expanders. -/
example (n : ℕ) [Nontrivial (Fin n)] : 0 < (RotationMap.expander (Fin n)).edgeExpansion :=
  lt_of_lt_of_le (by norm_num) (RotationMap.le_edgeExpansion_expander (Fin n))

/-- The size bound for rotation maps applies to the expanders on `2196000` vertices. -/
example : Fintype.card (Fin 120) + 2 ≤
    (RotationMap.expander (Fin 2196000)).edgeExpansion * Fintype.card (Fin 2196000) / 3 := by
  have := RotationMap.le_edgeExpansion_expander (Fin 2196000)
  simp only [Fintype.card_fin]
  push_cast
  linarith

/-! ### Axioms -/

/--
info: 'Cslib.Logic.PL.CNF.not_satisfiable_tseitinFormula' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.not_satisfiable_tseitinFormula

/--
info: 'Cslib.Logic.PL.CNF.satisfiable_tseitinFormula_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.satisfiable_tseitinFormula_iff

/--
info: 'Cslib.Logic.PL.Tseitin.exists_card_edgeCut_le_width' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.Tseitin.exists_card_edgeCut_le_width

/--
info: 'Cslib.Logic.PL.Tseitin.minBalancedCut_le_of_refutableInWidth' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.Tseitin.minBalancedCut_le_of_refutableInWidth

/--
info: 'Cslib.Logic.PL.Tseitin.exp_le_of_refutableInSize' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.Tseitin.exp_le_of_refutableInSize

/--
info: 'Cslib.Logic.PL.CNF.exp_le_of_refutableInSize' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.exp_le_of_refutableInSize

/--
info: 'Cslib.Logic.PL.Tseitin.edgeExpansion_mul_card_div_three_le_of_refutableInWidth' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.Tseitin.edgeExpansion_mul_card_div_three_le_of_refutableInWidth

/--
info: 'Cslib.Logic.PL.Tseitin.exp_edgeExpansion_le_of_refutableInSize' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.Tseitin.exp_edgeExpansion_le_of_refutableInSize

/--
info: 'Cslib.Logic.PL.CNF.exists_forall_refutableInSize_exp_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.exists_forall_refutableInSize_exp_le

end ComplexityTests.ProofComplexity.Tseitin
