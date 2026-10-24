/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Approximation.IndependentSet
import Complexity.Computability.Complexity.Classes.Space.GeneralizedGeography

/-!
# Tests: inapproximability of graph problems, and Generalized Geography

Minimization gap problems on a concrete objective; the values of small graphs; yes- and
no-instances of the gap problems of MAX-E3SAT, maximum independent set, maximum clique and minimum
vertex cover at the constants of the hardness theorems, so that their NP-hardness statements are not
vacuous. Small instances of Generalized Geography won and lost by the first player, including
undeclared targets and revisits; members and non-members of `TQBFCNF`, including a formula with a
free variable, and their images under the reduction to Generalized Geography. The axioms of the
headline theorems.
-/

namespace ComplexityTests.GapGraphsGeography

open Cslib Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Minimization gap problems -/

/-- The gap problem of the identity objective on natural numbers, between `1` and `3`. -/
private noncomputable def gapNat : PromiseProblem ℕ :=
  PromiseProblem.gapMin (fun n => (n : ℝ)) (fun _ => 1) (fun _ => 3)

example : (0 : ℕ) ∈ gapNat.yes := by norm_num [gapNat]

example : (5 : ℕ) ∈ gapNat.no := by norm_num [gapNat]

/-- `2` is in neither set: it is outside the promise. -/
example : (2 : ℕ) ∉ gapNat.yes ∧ (2 : ℕ) ∉ gapNat.no := by norm_num [gapNat]

/-- With instance-dependent thresholds `c n = n` and `s n = 2 n`, the instance `0` has `c 0 = s 0`
and is never a no-instance. -/
example : (0 : ℕ) ∉ (PromiseProblem.gapMin (fun _ => (7 : ℝ)) (fun n : ℕ => (n : ℝ))
    (fun n : ℕ => 2 * (n : ℝ))).no := by
  norm_num

/-! ### Values of graphs -/

/-- A single vertex is an independent set. -/
example : 1 ≤ Graph.indepNum ([0], []) :=
  Graph.le_indepNum_iff.2 ⟨{⟨0, by simp⟩}, by simp, rfl⟩

/-- A graph without declared vertices has independence number `0` and vertex cover number `0`. -/
example : Graph.indepNum ([], []) = 0 ∧ Graph.vertexCoverNum ([], []) = 0 := by
  have h := Graph.indepNum_le_card ([], [])
  simp only [List.toFinset_nil, Finset.card_empty, Nat.le_zero] at h
  exact ⟨h, by rw [Graph.vertexCoverNum_eq_card_sub_indepNum, h]; rfl⟩

/-- Complementing a graph exchanges independent sets and cliques. -/
example (G : Graph) : G.compl.cliqueNum = G.indepNum := Graph.cliqueNum_compl G

/-! ### Yes- and no-instances at the constants of the hardness theorems -/

private noncomputable abbrev s₀ : ℝ := 1 - 1 / (3 * 2 ^ 77)

/-- A satisfiable formula with three literals in its clause. -/
private def satFormula : CNF ℕ := [[(0, true), (0, true), (0, true)]]

private theorem satFormula_mem_yes : satFormula ∈ (GapExactThreeSAT s₀).yes := by
  rw [yes_GapExactThreeSAT]
  refine ⟨fun c hc => by simp [satFormula] at hc; simp [hc], fun _ => true, ?_⟩
  simp [satFormula]

private theorem contradiction_mem_no :
    GapExactThreeSAT.contradiction ∈ (GapExactThreeSAT s₀).no := by
  rw [mem_no_GapExactThreeSAT (by norm_num), GapExactThreeSAT.unsatVal_contradiction]
  refine ⟨fun c hc => ?_, by norm_num⟩
  simp only [GapExactThreeSAT.contradiction, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> rfl

/-- The gap problem of MAX-3SAT has a yes- and a no-instance with clauses of three literals. -/
example :
    satFormula ∈ (GapThreeSAT s₀).yes ∧ GapExactThreeSAT.contradiction ∈ (GapThreeSAT s₀).no :=
  ⟨satFormula_mem_yes.1, contradiction_mem_no.1⟩

/-- A reduction of promise problems carries yes- and no-instances. -/
private theorem nonempty_of_polyTimeReducible {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {X : PromiseProblem α} {Y : PromiseProblem β}
    (h : PromiseProblem.PolyTimeReducible encA encB X Y) {a b : α} (ha : a ∈ X.yes)
    (hb : b ∈ X.no) : (∃ y, y ∈ Y.yes) ∧ ∃ y, y ∈ Y.no :=
  let ⟨f, _, hyes, hno⟩ := h
  ⟨⟨f a, hyes ha⟩, ⟨f b, hno hb⟩⟩

example : (∃ x, x ∈ (GapIndependentSet s₀).yes) ∧ ∃ x, x ∈ (GapIndependentSet s₀).no :=
  nonempty_of_polyTimeReducible (polyTimeReducible_GapThreeSAT_GapIndependentSet (by norm_num))
    satFormula_mem_yes.1 contradiction_mem_no.1

example : (∃ x, x ∈ (GapClique s₀).yes) ∧ ∃ x, x ∈ (GapClique s₀).no :=
  nonempty_of_polyTimeReducible ((polyTimeReducible_GapThreeSAT_GapIndependentSet
    (by norm_num)).trans polyTimeReducible_GapIndependentSet_GapClique)
    satFormula_mem_yes.1 contradiction_mem_no.1

example : (∃ x, x ∈ (GapVertexCover (1 + 1 / (3 * 2 ^ 78))).yes) ∧
    ∃ x, x ∈ (GapVertexCover (1 + 1 / (3 * 2 ^ 78))).no := by
  have h := polyTimeReducible_GapExactThreeSAT_GapVertexCover (s := s₀) (by norm_num)
  rw [show (1 + (1 - s₀) / 2 : ℝ) = 1 + 1 / (3 * 2 ^ 78) by norm_num] at h
  exact nonempty_of_polyTimeReducible h satFormula_mem_yes contradiction_mem_no

/-! ### Generalized Geography -/

/-- With one arc from the start, the first player moves and the second player is stuck. -/
example : ((([0, 1], [(0, 1)]) : Graph), 0) ∈ GeneralizedGeography := by
  rw [mem_GeneralizedGeography, Graph.geographyWins_iff]
  refine ⟨1, by simp, by simp, by simp, ?_⟩
  rw [Graph.geographyWins_iff]
  simp

/-- On a path of two arcs, the second player makes the last move. -/
example : ((([0, 1, 2], [(0, 1), (1, 2)]) : Graph), 0) ∉ GeneralizedGeography := by
  rw [mem_GeneralizedGeography, Graph.not_geographyWins_iff]
  intro w hw _ _
  obtain rfl : w = 1 := by simpa using hw
  rw [Graph.geographyWins_iff]
  refine ⟨2, by simp, by simp, by simp, ?_⟩
  rw [Graph.geographyWins_iff]
  simp

/-- An arc to an undeclared vertex is not a move. -/
example : ((([0], [(0, 1)]) : Graph), 0) ∉ GeneralizedGeography := by
  rw [mem_GeneralizedGeography, Graph.geographyWins_iff]
  simp

/-- On a cycle of two arcs, the second player cannot return to the visited start. -/
example : ((([0, 1], [(0, 1), (1, 0)]) : Graph), 0) ∈ GeneralizedGeography := by
  rw [mem_GeneralizedGeography, Graph.geographyWins_iff]
  refine ⟨1, by simp, by simp, by simp, ?_⟩
  rw [Graph.geographyWins_iff]
  simp

/-- `∃ x₀, ∀ x₁, x₀` is true. -/
private theorem mem_TQBFCNF_ex :
    (([(0, 1)], [[(0, true)]]) : List (ℕ × ℕ) × CNF ℕ) ∈ TQBFCNF := by
  rw [TQBFCNF, Set.mem_ofPred_eq, mem_TQBF]
  decide

/-- `∃ x₀, ∀ x₁, x₁` is false. -/
private theorem notMem_TQBFCNF_all :
    (([(0, 1)], [[(1, true)]]) : List (ℕ × ℕ) × CNF ℕ) ∉ TQBFCNF := by
  rw [TQBFCNF, Set.mem_ofPred_eq, mem_TQBF]
  decide

/-- `∃ x₀, ∀ x₁, x₂` has a free variable. -/
private theorem notMem_TQBFCNF_free :
    (([(0, 1)], [[(2, false)]]) : List (ℕ × ℕ) × CNF ℕ) ∉ TQBFCNF := by
  rw [TQBFCNF, Set.mem_ofPred_eq, mem_TQBF]
  decide

example : GeneralizedGeography.reduce ([(0, 1)], [[(0, true)]]) ∈ GeneralizedGeography :=
  (GeneralizedGeography.reduce_mem_iff _).2 mem_TQBFCNF_ex

example : GeneralizedGeography.reduce ([(0, 1)], [[(1, true)]]) ∉ GeneralizedGeography :=
  fun h => notMem_TQBFCNF_all ((GeneralizedGeography.reduce_mem_iff _).1 h)

example : GeneralizedGeography.reduce ([(0, 1)], [[(2, false)]]) ∉ GeneralizedGeography :=
  fun h => notMem_TQBFCNF_free ((GeneralizedGeography.reduce_mem_iff _).1 h)

/-! ### Axioms -/

/--
info: 'Cslib.Complexity.GapExactThreeSAT_npHard' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.GapExactThreeSAT_npHard

/--
info: 'Cslib.Complexity.GapIndependentSet_npHard' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.GapIndependentSet_npHard

/--
info: 'Cslib.Complexity.GapClique_npHard' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.GapClique_npHard

/--
info: 'Cslib.Complexity.GapVertexCover_npHard' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.GapVertexCover_npHard

/--
info: 'Cslib.Complexity.TQBFCNF_pspaceComplete' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.TQBFCNF_pspaceComplete

/--
info: 'Cslib.Complexity.GeneralizedGeography_mem_PSPACE' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.GeneralizedGeography_mem_PSPACE

/--
info: 'Cslib.Complexity.GeneralizedGeography_pspaceHard' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.GeneralizedGeography_pspaceHard

/--
info: 'Cslib.Complexity.GeneralizedGeography_pspaceComplete' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.GeneralizedGeography_pspaceComplete

end ComplexityTests.GapGraphsGeography
