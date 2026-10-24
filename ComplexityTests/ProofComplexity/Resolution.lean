/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.Resolution.TreeLike
import Complexity.Logics.Propositional.Resolution.SizeWidth

/-!
# Tests: resolution proofs, tree-like resolution and the size–width tradeoff

Widths of clauses with repeated literals; a concrete resolution refutation, its size and width;
a tree-like refutation, its decision tree and the decision tree's refutation; restrictions of a
proof; instances of the hypotheses of the size–width theorems; and the axioms of the headline
theorems.
-/

namespace ComplexityTests.ProofComplexity.Resolution

open Cslib Cslib.Logic.PL

/-! ### Width -/

/-- Repeated literals count once. -/
example : Clause.width ([(0, true), (0, true), (1, false)] : Clause ℕ) = 2 := by decide

/-- Complementary literals count twice. -/
example : Clause.width ([(0, true), (0, false)] : Clause ℕ) = 2 := by decide

/-! ### A refutation -/

/-- `x₀ ∧ (¬x₀ ∨ x₁) ∧ ¬x₁`. -/
private def φ : CNF ℕ := [[(0, true)], [(0, false), (1, true)], [(1, false)]]

/-- Resolve `x₀` with `¬x₀ ∨ x₁` to `x₁`, and `x₁` with `¬x₁` to the empty clause. -/
private def proof : List (Clause ℕ) := [[], [(1, true)], [(1, false)], [(0, false), (1, true)],
  [(0, true)]]

example : Clause.resolvent ([(0, true)] : Clause ℕ) [(0, false), (1, true)] 0 = [(1, true)] := by
  decide

example : Clause.resolvent ([(1, true)] : Clause ℕ) [(1, false)] 1 = [] := by decide

private theorem isProof : φ.IsProof proof := by
  have h₃ : φ.IsProof [[(1, false)], [(0, false), (1, true)], [(0, true)]] :=
    ((CNF.IsProof.nil.mem (by decide)).mem (by decide)).mem (by decide)
  have h₄ := h₃.resolvent (c₁ := [(0, true)]) (c₂ := [(0, false), (1, true)]) 0 (by decide)
    (by decide) (by decide) (by decide)
  have h₅ := h₄.resolvent (c₁ := [(1, true)]) (c₂ := [(1, false)]) 1 (by decide) (by decide)
    (by decide) (by decide)
  exact h₅

example : φ.RefutableInSize 5 := ⟨proof, isProof, by decide, le_rfl⟩

example : φ.RefutableInWidth 2 := ⟨proof, isProof, by decide, by decide⟩

example : ¬ φ.Satisfiable :=
  CNF.exists_refutableInSize_iff_not_satisfiable.1 ⟨5, proof, isProof, by decide, le_rfl⟩

/-- Fixing `x₁` to `false` leaves a refutation of `x₀ ∧ ¬x₀`, with at most as many lines. -/
example : φ.restrict 1 false = [[(0, true)], [(0, false)]] := by decide

example : ∃ ls, (φ.restrict 1 false).IsProof ls ∧ [] ∈ ls ∧ ls.length ≤ 5 := by
  obtain ⟨ls, h, hlen, hsub, -⟩ := isProof.restrict 1 false
  obtain ⟨c, hc, hsub'⟩ := hsub [] (by decide) (by decide)
  obtain rfl : c = [] := List.eq_nil_iff_forall_not_mem.2 fun l hl => by simpa using hsub' l hl
  exact ⟨ls, h, hc, hlen.trans (by decide)⟩

/-- Restricting `φ` by the partial assignment fixing `x₁ ↦ false` gives the same two clauses. -/
example : φ.restrictBy (fun v => if v = 1 then some false else none) =
    [[(0, true)], [(0, false)]] := by
  decide

example : ∃ ls, (φ.restrictBy (fun v => if v = 1 then some false else none)).IsProof ls ∧
    [] ∈ ls ∧ ls.length ≤ 5 := by
  obtain ⟨ls, h, hsub, ks, hks, -, hF⟩ :=
    isProof.restrictBy (fun v => if v = 1 then some false else none)
  obtain ⟨c, hc, hsub'⟩ := hsub [] (by decide) (by decide)
  obtain rfl : c = [] := List.eq_nil_iff_forall_not_mem.2 fun l hl => by simpa using hsub' l hl
  exact ⟨ls, h, hc, hF.length_eq.trans_le (hks.length_le.trans (by decide))⟩

/-! ### Tree-like refutations and decision trees -/

/-- `x₀ ∧ ¬x₀`. -/
private def ψ : CNF ℕ := [[(0, true)], [(0, false)]]

/-- The tree-like refutation of `ψ`, resolving its two clauses. -/
private def treeRefutation : ψ.Derivation [] :=
  .resolvent (c₁ := [(0, true)]) (c₂ := [(0, false)]) 0 (.mem (by decide)) (.mem (by decide))
    (by decide) (by decide)

example : treeRefutation.size = 3 := rfl

example : treeRefutation.toDecisionTree = .node 0 (.leaf [(0, true)]) (.leaf [(0, false)]) := rfl

example : treeRefutation.toDecisionTree.FindsFalsifiedClause ψ :=
  treeRefutation.findsFalsifiedClause_toDecisionTree

/-- A DPLL tree querying `x₀` twice finds a falsified clause; it gives a tree-like refutation. -/
private def dpllTree : DecisionTree ℕ (Clause ℕ) :=
  .node 0 (.leaf [(0, true)]) (.node 0 (.leaf [(0, true)]) (.leaf [(0, false)]))

private theorem findsFalsifiedClause_dpllTree : dpllTree.FindsFalsifiedClause ψ := fun σ => by
  cases h : σ 0 <;> simp [dpllTree, DecisionTree.eval, h, ψ]

example : ∃ d : ψ.Derivation [], d.size + 1 ≤ 6 :=
  findsFalsifiedClause_dpllTree.exists_derivation

/-! ### The size–width tradeoff -/

/-- Short tree-like refutations are narrow: `3 ≤ 2 ^ 2` nodes give width at most `1 + 2`. -/
example : ψ.RefutableInWidth 3 :=
  CNF.RefutableInWidth.of_derivation (k := 1) (b := 2) (by decide) treeRefutation rfl (by decide)

/-- The hypothesis `s (2N - d) ^ b < (2N) ^ b` is satisfiable: `3 * (2 - 1) ^ 2 < 2 ^ 2`. -/
example : ψ.RefutableInWidth (max 1 1 + 2) :=
  CNF.RefutableInWidth.of_refutableInSize (s := 3) (N := 1) (by decide) (by decide)
    treeRefutation.refutableInSize (by decide)

example : ∃ w : ℕ, φ.RefutableInWidth w ∧ (w : ℝ) ≤ 2 + 2 * √(2 * 2 * Real.log 5) + 2 := by
  exact_mod_cast CNF.exists_refutableInWidth_le_of_refutableInSize (k := 2) (N := 2)
    (by decide) (by decide) ⟨proof, isProof, by decide, le_rfl⟩

/-- The size–width theorem includes the boundary case of no variables and one proof line. -/
example : ∃ w : ℕ, CNF.RefutableInWidth ([[]] : CNF ℕ) w ∧ (w : ℝ) ≤ 2 := by
  have hs : CNF.RefutableInSize ([[]] : CNF ℕ) 1 :=
    ⟨[[]], CNF.IsProof.nil.mem (by simp), by simp, le_rfl⟩
  simpa using CNF.exists_refutableInWidth_le_of_refutableInSize (k := 0) (N := 0)
    (by simp) (by decide) hs

/-- The empty, satisfiable formula has no resolution refutation. -/
example : ¬ ∃ s, CNF.RefutableInSize ([] : CNF ℕ) s := by
  rw [CNF.exists_refutableInSize_iff_not_satisfiable, not_not]
  exact ⟨fun _ => false, rfl⟩

/-! ### Axioms -/

/--
info: 'Cslib.Logic.PL.CNF.derives_iff_exists_isProof' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.derives_iff_exists_isProof

/--
info: 'Cslib.Logic.PL.CNF.IsProof.restrict' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.IsProof.restrict

/--
info: 'Cslib.Logic.PL.CNF.IsProof.lift' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.IsProof.lift

/--
info: 'Cslib.Logic.PL.CNF.IsProof.restrictBy' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.IsProof.restrictBy

/--
info: 'Cslib.Logic.PL.CNF.RefutableInWidth.of_restrict' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.RefutableInWidth.of_restrict

/--
info: 'Cslib.Logic.PL.CNF.RefutableInWidth.of_refutableInSize' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.RefutableInWidth.of_refutableInSize

/--
info: 'Cslib.Logic.PL.CNF.exists_refutableInWidth_le_of_refutableInSize' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.exists_refutableInWidth_le_of_refutableInSize

/--
info: 'Cslib.Logic.PL.CNF.RefutableInWidth.of_derivation' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.RefutableInWidth.of_derivation

/--
info: 'Cslib.Logic.PL.CNF.Derivation.findsFalsifiedClause_toDecisionTree' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.Derivation.findsFalsifiedClause_toDecisionTree

/--
info: 'Cslib.DecisionTree.FindsFalsifiedClause.exists_derivation' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.DecisionTree.FindsFalsifiedClause.exists_derivation

end ComplexityTests.ProofComplexity.Resolution
