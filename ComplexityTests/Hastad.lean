/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Approximation.Hastad
import Complexity.Computability.PCP.Approximation.MaxExactThreeSAT

/-!
# Tests: Håstad's 3-bit linear test and its soundness against Label Cover

Concrete evaluations and non-vacuity checks for exact 3-clauses (`Clause.IsExactThreeDistinct`,
`CNF.IsExactThreeDistinct`), the `7 / 8` random-assignment bound (`unsatVal_le_one_eighth`), the
Long Code and table folding (`longCode`, `foldTable`), mod-2 subset projection (`projectSet`),
Håstad's 3-bit linear test on a concrete Label Cover graph, and `#print axioms` guards for the
headline theorems.
-/

namespace ComplexityTests.Hastad

open Cslib Cslib.BitString Cslib.Complexity Cslib.Logic.PL Cslib.PCP Cslib.PCP.Encoded Finset

/-! ### Exact 3-clauses and the `7 / 8` bound -/

/-- A concrete clause with three distinct variables satisfies `Clause.IsExactThreeDistinct`. -/
example : Clause.IsExactThreeDistinct ([(0, true), (1, false), (2, true)] : Clause ℕ) := by
  decide

/-- A clause with a repeated variable does not satisfy `Clause.IsExactThreeDistinct`. -/
example : ¬ Clause.IsExactThreeDistinct ([(0, true), (0, false), (2, true)] : Clause ℕ) := by
  decide

/-- The eight clauses on the distinct variables `0, 1, 2`, one for each sign pattern: every
assignment falsifies exactly one of them. -/
private def eightClauses : CNF ℕ :=
  [[(0, true), (1, true), (2, true)], [(0, true), (1, true), (2, false)],
    [(0, true), (1, false), (2, true)], [(0, true), (1, false), (2, false)],
    [(0, false), (1, true), (2, true)], [(0, false), (1, true), (2, false)],
    [(0, false), (1, false), (2, true)], [(0, false), (1, false), (2, false)]]

/-- `eightClauses` has three distinct variables per clause and `unsatVal = 1 / 8`, witnessing
tightness of `unsatVal_le_one_eighth`. -/
example : eightClauses.unsatVal = 1 / 8 := by
  have h3 : eightClauses.IsExactThreeDistinct := by decide
  refine le_antisymm h3.unsatVal_le_one_eighth ((CNF.le_unsatVal_iff _).2 fun σ => ?_)
  have hlen : eightClauses.length = 8 := rfl
  have hcount : eightClauses.countUnsat σ = 1 := by
    cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2 <;>
      simp [eightClauses, CNF.countUnsat, Clause.eval, Literal.eval, h0, h1, h2]
  rw [hcount, hlen]
  norm_num

/-! ### Long Code, folding, mod-2 projection, and multi-edge Label Cover -/

example : longCode (0 : Fin 2) (fun i => i == 0) = true := rfl

example : IsOdd (foldTable false (fun _ : Bool → Bool => false)) :=
  isOdd_foldTable false _

/-- Under the constant projection `fun _ : Bool => ()`, a two-element set `{false, true}` has even
fiber cardinality and therefore projects to `∅`. -/
example : projectSet (fun _ : Bool => ()) ({false, true} : Finset Bool) = ∅ := by
  decide

/-- A singleton `{false}` has odd fiber cardinality and therefore projects to `{()}`. -/
example : projectSet (fun _ : Bool => ()) ({false} : Finset Bool) = {()} := by
  decide

/-- A concrete 1-edge Label Cover instance on `Bool` with identity projection `id`. -/
private def oneEdgeGraph : Graph (Bool → Bool) :=
  ⟨1, [⟨0, 0, id⟩]⟩

/-- On `oneEdgeGraph`, the constant `false` labelling satisfies the single edge and yields Long Code
tables achieving linear acceptance `1 - δ`. -/
example (δ : ℝ) :
    (∀ w, IsOdd (longCode ((fun _ : ℕ => false) w))) ∧
      Hastad.hastadGraphLinearProb oneEdgeGraph δ
        (fun _ => longCode false) (fun _ => longCode false) = 1 - δ :=
  Hastad.hastadGraphProb_longCode_of_satisfies (by decide : oneEdgeGraph.edges ≠ []) δ
    (fun d hd => by
      simp only [oneEdgeGraph, List.mem_singleton] at hd
      subst hd
      rfl)

/-- The soundness threshold `η` of `hastad_gapLabelCover_dichotomy` does not depend on the label
sets: one `η` serves instances over `Bool → Bool` and over `Fin 3 → Bool`. -/
example : ∃ η : ℝ, 0 < η ∧
    (∀ g : Graph (Bool → Bool), g.edges ≠ [] → g ∈ (GapLabelCover Bool Bool 1 η).no →
      ∀ B A, (∀ w, IsOdd (B w)) →
        Hastad.hastadGraphLinearProb g (1 / 4) B A ≤ 1 / 2 + 4 * (1 / 16)) ∧
    (∀ g : Graph (Fin 3 → Bool), g.edges ≠ [] → g ∈ (GapLabelCover (Fin 3) Bool 1 η).no →
      ∀ B A, (∀ w, IsOdd (B w)) →
        Hastad.hastadGraphLinearProb g (1 / 4) B A ≤ 1 / 2 + 4 * (1 / 16)) := by
  obtain ⟨η, hη, h⟩ := Hastad.hastad_gapLabelCover_dichotomy (ε := 1 / 16) (δ := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨η, hη, fun _ hg => (h hg).2, fun _ hg => (h hg).2⟩

/-! ### Axioms -/

/--
info: 'Cslib.Logic.PL.Clause.IsExactThreeDistinct.expect_eval_eq_false' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.Clause.IsExactThreeDistinct.expect_eval_eq_false

/--
info: 'Cslib.Logic.PL.Clause.IsExactThreeDistinct.expect_eval_eq_true' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.Clause.IsExactThreeDistinct.expect_eval_eq_true

/--
info: 'Cslib.Logic.PL.CNF.IsExactThreeDistinct.unsatVal_le_one_eighth' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.IsExactThreeDistinct.unsatVal_le_one_eighth

/--
info: 'Cslib.Logic.PL.CNF.IsExactThreeDistinct.exists_countUnsat_le_div_eight' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.IsExactThreeDistinct.exists_countUnsat_le_div_eight

/--
info: 'Cslib.BitString.IsOdd.fourierCoeff_empty' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.IsOdd.fourierCoeff_empty

/--
info: 'Cslib.BitString.chi_comp_eq_chi_projectSet' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.chi_comp_eq_chi_projectSet

/--
info: 'Cslib.PCP.Hastad.hastadLinearCorr_eq_sum' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Hastad.hastadLinearCorr_eq_sum

/--
info: 'Cslib.PCP.Hastad.sum_spectralWeight_le_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Hastad.sum_spectralWeight_le_one

/--
info: 'Cslib.PCP.Hastad.hastadLinearCorr_sq_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Hastad.hastadLinearCorr_sq_le

/--
info: 'Cslib.PCP.Hastad.hastadGraphLinearCorr_sq_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Hastad.hastadGraphLinearCorr_sq_le

/--
info: 'Cslib.PCP.Hastad.hastad_gapLabelCover_dichotomy' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Hastad.hastad_gapLabelCover_dichotomy

end ComplexityTests.Hastad
