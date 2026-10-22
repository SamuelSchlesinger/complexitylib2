/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Approximation.Hastad

/-!
# Tests: Håstad's 3-bit linear test and its soundness against Label Cover

Concrete evaluations and non-vacuity checks for exact 3-clauses (`Clause.IsExactThreeDistinct`,
`CNF.IsExactThreeDistinct`), the `7 / 8` random-assignment bound (`unsatVal_le_one_eighth`), the
4-clause XOR gadget (`xorThreeCNF`), the Long Code and table folding (`longCode`, `foldTable`),
mod-2 subset projection (`projectSet`), Håstad's 3-bit linear and E3-CNF tests on a concrete Label
Cover graph, and `#print axioms` guards for the headline theorems.
-/

namespace ComplexityTests.Hastad

open Cslib Cslib.BitString Cslib.Complexity Cslib.Logic.PL Cslib.PCP Cslib.PCP.Hastad
  Cslib.PCP.Encoded Finset

/-! ### Exact 3-clauses and the 4-clause XOR gadget -/

/-- A concrete clause with three distinct variables satisfies `Clause.IsExactThreeDistinct`. -/
example : Clause.IsExactThreeDistinct ([(0, true), (1, false), (2, true)] : Clause ℕ) := by
  decide

/-- A clause with a repeated variable does not satisfy `Clause.IsExactThreeDistinct`. -/
example : ¬ Clause.IsExactThreeDistinct ([(0, true), (0, false), (2, true)] : Clause ℕ) := by
  decide

/-- The 4-clause XOR gadget on distinct variables `0, 1, 2` is an exact 3-CNF on distinct
variables. -/
example : (xorThreeCNF 0 1 2 false).IsExactThreeDistinct :=
  isExactThreeDistinct_xorThreeCNF (by decide) (by decide) (by decide) false

/-- When the parity matches (`false ^^ false ^^ false = false`), all 4 clauses of `xorThreeCNF`
are satisfied (`countUnsat = 0`). -/
example : (xorThreeCNF 0 1 2 false).countUnsat (fun _ => false) = 0 := by
  decide

/-- When the parity fails (`true ^^ false ^^ false = true ≠ false`), exactly 1 of the 4 clauses of
`xorThreeCNF` is falsified (`countUnsat = 1`). -/
example : (xorThreeCNF 0 1 2 false).countUnsat (fun i => i == 0) = 1 := by
  decide

/-- The 8-clause formula encoding `x₀ ⊕ x₁ ⊕ x₂ = 0` and `x₀ ⊕ x₁ ⊕ x₂ = 1` on distinct variables
`0, 1, 2` has `IsExactThreeDistinct` and exact `unsatVal = 1 / 8`, witnessing tightness of the
`1 / 8` bound. -/
private def eightClauseContradiction : CNF ℕ :=
  xorThreeCNF 0 1 2 false ++ xorThreeCNF 0 1 2 true

private theorem isExactThreeDistinct_eightClauseContradiction :
    eightClauseContradiction.IsExactThreeDistinct := by
  intro c hc
  rw [eightClauseContradiction, List.mem_append] at hc
  rcases hc with hc | hc
  · exact isExactThreeDistinct_xorThreeCNF (by decide) (by decide) (by decide) false c hc
  · exact isExactThreeDistinct_xorThreeCNF (by decide) (by decide) (by decide) true c hc

example : eightClauseContradiction.unsatVal = 1 / 8 := by
  have h3 := isExactThreeDistinct_eightClauseContradiction
  refine le_antisymm h3.unsatVal_le_one_eighth ((CNF.le_unsatVal_iff _).2 fun σ => ?_)
  have hlen : eightClauseContradiction.length = 8 := rfl
  have hcount : eightClauseContradiction.countUnsat σ = 1 := by
    simp only [eightClauseContradiction, CNF.countUnsat, List.countP_append]
    change (xorThreeCNF 0 1 2 false).countUnsat σ + (xorThreeCNF 0 1 2 true).countUnsat σ = 1
    rw [countUnsat_xorThreeCNF, countUnsat_xorThreeCNF]
    cases (σ 0 ^^ σ 1) ^^ σ 2 <;> rfl
  rw [hcount, hlen]
  norm_num

/-- `eightClauseContradiction` is a yes-instance of `GapExactThreeDistinctSAT (7 / 8) (3 / 4)`. -/
example : eightClauseContradiction ∈ (GapExactThreeDistinctSAT (7 / 8) (3 / 4)).yes := by
  simp only [GapExactThreeDistinctSAT, PromiseProblem.yes_restrict,
    PromiseProblem.mem_yes_gapMax, Set.mem_inter_iff, Set.mem_ofPred_eq]
  have h3 := isExactThreeDistinct_eightClauseContradiction
  exact ⟨by linarith [h3.unsatVal_le_one_eighth], h3⟩

/-! ### Long Code, folding, mod-2 projection, and multi-edge Label Cover -/

example : longCode (0 : Fin 2) (fun i => i == 0) = true := rfl

example : IsFolded (foldTable false (fun _ : Bool → Bool => false)) :=
  isFolded_foldTable false _

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
    (∀ w, IsFolded (longCode ((fun _ : ℕ => false) w))) ∧
      hastadGraphLinearProb oneEdgeGraph δ
        (fun _ => longCode false) (fun _ => longCode false) = 1 - δ :=
  hastadGraphProb_longCode_of_satisfies (by decide : oneEdgeGraph.edges ≠ []) δ
    (fun d hd => by
      simp only [oneEdgeGraph, List.mem_singleton] at hd
      subst hd
      rfl)

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
info: 'Cslib.PCP.Hastad.IsFolded.fourierCoeff_empty' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Hastad.IsFolded.fourierCoeff_empty

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

/--
info: 'Cslib.Complexity.no_GapExactThreeDistinctSAT_eq_empty' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.no_GapExactThreeDistinctSAT_eq_empty

end ComplexityTests.Hastad
