/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.CookLevin.Counting
import Complexity.Computability.Complexity.CookLevin.Parsimonious
import Complexity.Computability.Complexity.Problems.CountingSAT
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Parsimonious Cook–Levin and counting completeness tests

Concrete counts check that `SharpSAT` counts assignments of the occurring variables only, that
the counting problems are nontrivial, and that the parsimonious reduction applies to a
nonconstant function in `#P`.
-/

namespace ComplexityTests.CountingCompleteness

open Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM

/-! ### Concrete counts -/

/-- The empty formula has one satisfying assignment, of no variables. -/
theorem sharpSAT_nil : SharpSAT [] = 1 :=
  CNF.modelCount_eq_one_iff.2 ⟨fun _ => false, rfl, fun _ _ v hv => by simp [CNF.vars] at hv⟩

/-- A contradictory formula has none. -/
theorem sharpSAT_contradiction : SharpSAT [[(0, true)], [(0, false)]] = 0 := by
  refine Nat.eq_zero_of_not_pos fun h => ?_
  obtain ⟨σ, hσ⟩ := CNF.modelCount_pos_iff.1 h
  cases h0 : σ 0 <;> simp [h0] at hσ

/-- The clause `x₀ ∨ x₁` has three satisfying assignments of its two variables; variables that
do not occur are not counted. -/
example : SharpSAT [[(0, true), (1, true)]] = 3 := by decide

/-- A tautological clause on one variable has two satisfying assignments. -/
example : SharpSAT [[(0, true), (0, false)]] = 2 := by decide

/-! ### The problems are nontrivial -/

example : [] ∈ ParitySAT := by simp [ParitySAT, sharpSAT_nil]
example : [[(0, true), (0, false)]] ∉ ParitySAT := by change ¬Odd (SharpSAT _); decide
example : [] ∈ USAT := SharpSAT.mem_USAT_iff.2 sharpSAT_nil
example : [[(0, true), (0, false)]] ∉ USAT := by rw [SharpSAT.mem_USAT_iff]; decide
example : [[(0, true), (0, false)]] ∈ ModSAT 3 := by change SharpSAT _ % 3 ≠ 0; decide
example : [[(0, true), (0, false)]] ∉ ModSAT 2 := by change ¬SharpSAT _ % 2 ≠ 0; decide
example : ([[(0, true), (1, true)]], 3) ∈ SharpSATAtLeast := by change 3 ≤ SharpSAT _; decide
example : ([[(0, true), (1, true)]], 4) ∉ SharpSATAtLeast := by change ¬4 ≤ SharpSAT _; decide
example : ([[(0, true), (1, true)]], 3) ∈ SharpSATExact := by change SharpSAT _ = 3; decide
example : ([[(0, true), (1, true)]], 2) ∉ SharpSATExact := by change ¬SharpSAT _ = 2; decide
example : ([[(0, true)], [(0, false)]], 0) ∈ SharpSATExact := sharpSAT_contradiction
example : [] ∈ MAJSAT := by simp [MAJSAT, sharpSAT_nil, CNF.vars]
example : [[(0, true), (1, true)]] ∈ MAJSAT := by
  change 2 ^ (CNF.vars _).toFinset.card < 2 * SharpSAT _; decide
example : [[(0, true)], [(0, false)]] ∉ MAJSAT := by
  simp [MAJSAT, sharpSAT_contradiction]
example : [[(0, true)]] ∉ MAJSAT := by
  change ¬2 ^ (CNF.vars _).toFinset.card < 2 * SharpSAT _; decide
example : [[(0, true)], [(1, true)]] ∉ MAJSAT := by
  change ¬2 ^ (CNF.vars _).toFinset.card < 2 * SharpSAT _; decide
example : (padMajority [] 0).vars.toFinset.card = 1 := by decide
example : SharpSAT (padMajority [] 0) = 1 := by decide
example : padMajority [] 0 ∉ MAJSAT := by
  change ¬2 ^ (CNF.vars _).toFinset.card < 2 * SharpSAT _; decide
example : (padMajority [[(0, true)]] 0).vars.toFinset.card = 2 := by decide
example : SharpSAT (padMajority [[(0, true)]] 0) = 2 := by decide
example : padMajority [[(0, true)]] 0 ∉ MAJSAT := by
  change ¬2 ^ (CNF.vars _).toFinset.card < 2 * SharpSAT _; decide
example : padMajority [[(0, true), (1, true)]] 1 ∈ MAJSAT := by
  rw [padMajority_mem_MAJSAT_iff]; decide
example : padMajority [[(0, true), (1, true)]] 2 ∉ MAJSAT := by
  rw [padMajority_mem_MAJSAT_iff]; decide

/-! ### Clients of the parsimonious reduction -/

/-- The number of words of the input's length starting with `true`, a nonconstant function in
`#P`, reduces parsimoniously to `#SAT`. -/
example : ParsimoniousReducible encBits encCNF
    (fun w => acceptCount (fun x : List Bool × List Bool => x.2.headD false) w
      (Polynomial.X.eval (encBits w).length)) SharpSAT :=
  CookLevin.SharpSAT_sharpPHard encBits _ ⟨Polynomial.X, _, by fun_prop, fun _ => rfl⟩

/-- `ModP 2 = ⊕P` and `ModSAT 2 = ⊕SAT` give the same complete problem twice. -/
example : PolyTimeComplete (ModP 2) encCNF ParitySAT := ModSAT_two ▸ ModSAT_modPComplete 2

/-- Hardness for `NP` is an instance of the generic notion. -/
example : PolyTimeComplete NP encCNF SAT :=
  polyTimeComplete_NP_iff.2 CookLevin.SAT_npComplete

/-! ### Headline axiom guards -/

/--
info: 'Cslib.Complexity.CookLevin.modelCount_tableau' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.modelCount_tableau

/--
info: 'Cslib.Complexity.CookLevin.modelCount_reduce' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.modelCount_reduce

/--
info: 'Cslib.Complexity.SharpSAT.mem_SharpP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SharpSAT.mem_SharpP

/--
info: 'Cslib.Complexity.CookLevin.SharpSAT_sharpPComplete' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.SharpSAT_sharpPComplete

/--
info: 'Cslib.Complexity.ParitySAT_parityPComplete' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ParitySAT_parityPComplete

/--
info: 'Cslib.Complexity.USAT_usComplete' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.USAT_usComplete

/--
info: 'Cslib.Complexity.ModSAT_modPComplete' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ModSAT_modPComplete

/--
info: 'Cslib.Complexity.compl_ModSAT_coModPComplete' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.compl_ModSAT_coModPComplete

/--
info: 'Cslib.Complexity.SharpSATAtLeast_ppComplete' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SharpSATAtLeast_ppComplete

/--
info: 'Cslib.Complexity.MAJSAT_mem_PP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.MAJSAT_mem_PP

/--
info: 'Cslib.Complexity.MAJSAT_ppHard' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.MAJSAT_ppHard

/--
info: 'Cslib.Complexity.MAJSAT_ppComplete' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.MAJSAT_ppComplete

/--
info: 'Cslib.Complexity.SharpSATExact_ceqPComplete' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SharpSATExact_ceqPComplete

/--
info: 'Cslib.Complexity.compl_SharpSATExact_coCeqPComplete' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.compl_SharpSATExact_coCeqPComplete

end ComplexityTests.CountingCompleteness
