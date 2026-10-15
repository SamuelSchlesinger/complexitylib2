/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity

/-!
# Axiom audit

Every headline theorem of the library is listed here with a `#guard_msgs` check that it depends
on no axioms beyond `propext`, `Classical.choice` and `Quot.sound`. Add an entry whenever a
theorem is promoted to "headline" status in `ROADMAP.md`.
-/

namespace ComplexityTests.Axioms

/--
info: 'Cslib.Complexity.CookLevin.tableau_satisfiable_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.CookLevin.tableau_satisfiable_iff

/--
info: 'Cslib.Complexity.CookLevin.reduce_mem_SAT_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.CookLevin.reduce_mem_SAT_iff

/--
info: 'Cslib.Complexity.CookLevin.SAT_npComplete_of_polyTime' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.CookLevin.SAT_npComplete_of_polyTime

/--
info: 'Cslib.Complexity.SAT.isVerifier' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.SAT.isVerifier

/--
info: 'Cslib.Complexity.mem_ThreeSAT_toThreeSAT_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.mem_ThreeSAT_toThreeSAT_iff

/--
info: 'Cslib.Logic.PL.CNF.satisfiable_relabel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Logic.PL.CNF.satisfiable_relabel

/--
info: 'Cslib.PolynomiallyBounded.polynomial_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.PolynomiallyBounded.polynomial_eval

/--
info: 'Cslib.Circuits.Boolean.PPoly.of_mem_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Boolean.PPoly.of_mem_P

/--
info: 'Cslib.Circuits.Boolean.PPoly.exists_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Boolean.PPoly.exists_not_mem

/--
info: 'Cslib.Complexity.SAT.toIndependentSet_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.SAT.toIndependentSet_mem_iff

/--
info: 'Cslib.Circuits.Boolean.PPoly.exists_of_mem_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Boolean.PPoly.exists_of_mem_P

/--
info: 'Cslib.Circuits.Boolean.MachineSimulation.acceptedWithin_mem_PPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.MachineSimulation.acceptedWithin_mem_PPoly

/--
info: 'Cslib.Complexity.Graph.compl_mem_Clique_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.Graph.compl_mem_Clique_iff

/--
info: 'Cslib.Circuits.Boolean.PPoly.of_boundedError' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.PPoly.of_boundedError

/--
info: 'Cslib.Circuits.Boolean.PPoly.of_mem_BPP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.PPoly.of_mem_BPP

/--
info: 'Cslib.card_filter_card_filter_le_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.card_filter_card_filter_le_le

/--
info: 'Cslib.Circuits.Boolean.PPoly.of_oneSidedError' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.PPoly.of_oneSidedError

/--
info: 'Cslib.Circuits.Boolean.PPoly.of_mem_RP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.PPoly.of_mem_RP

/--
info: 'Cslib.Complexity.RP_subset_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.RP_subset_NP

/--
info: 'Cslib.Circuits.Boolean.mem_PPoly_iff_exists_mem_SIZE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.mem_PPoly_iff_exists_mem_SIZE

/--
info: 'Cslib.Circuits.Boolean.complexity_le_of_boundedError' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.complexity_le_of_boundedError

/--
info: 'Cslib.Circuits.Boolean.complexity_le_of_oneSidedError' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.complexity_le_of_oneSidedError

/--
info: 'Cslib.Circuits.Boolean.PPoly.of_mem_coRP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.PPoly.of_mem_coRP

/--
info: 'Cslib.containsSunflower_of_forall_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.containsSunflower_of_forall_card_le

/--
info: 'Cslib.Circuits.Approximation.Scheme.card_failures_le_cost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Approximation.Scheme.card_failures_le_cost

/--
info: 'Cslib.Circuits.Monotone.two_pow_two_mul_sqrt_lt_ecomplexity_clique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Monotone.two_pow_two_mul_sqrt_lt_ecomplexity_clique

/--
info: 'Cslib.Circuits.Monotone.choose_le_or_pow_le_mul_size' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Monotone.choose_le_or_pow_le_mul_size

/--
info: 'Cslib.Circuits.Monotone.two_rpow_sqrt_lt_size' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Monotone.two_rpow_sqrt_lt_size

/--
info: 'Cslib.Circuits.Circuit.essential_le_size' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.essential_le_size

/--
info: 'Cslib.Circuits.Boolean.PPoly.exists_of_mem_BPP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.PPoly.exists_of_mem_BPP

/--
info: 'Cslib.Circuits.Boolean.PPoly.exists_of_mem_RP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.PPoly.exists_of_mem_RP

/--
info: 'Cslib.Circuits.Boolean.SIZE_ssubset' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.SIZE_ssubset

/--
info: 'Cslib.Circuits.Monotone.exists_computes_clique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Monotone.exists_computes_clique

/--
info: 'Cslib.Circuits.Boolean.SIZE_pow_ssubset' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.SIZE_pow_ssubset

/--
info: 'Cslib.Circuits.Circuit.essential_le_depth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.essential_le_depth

/--
info: 'Cslib.Circuits.Monotone.edgeCount_le_two_pow_depth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Monotone.edgeCount_le_two_pow_depth

/--
info: 'Cslib.Circuits.Boolean.three_mul_le_cost_of_computes_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.three_mul_le_cost_of_computes_parity

/--
info: 'Cslib.Circuits.Boolean.three_mul_le_complexity_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.three_mul_le_complexity_parity

/--
info: 'Cslib.Circuits.Boolean.isLeast_cost_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.isLeast_cost_parity

/--
info: 'Cslib.Circuits.Formula.sq_card_hammingEdges_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Formula.sq_card_hammingEdges_le

/--
info: 'Cslib.Circuits.Boolean.isLeast_leafSize_parity_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.isLeast_leafSize_parity_two_pow

/--
info: 'Cslib.Circuits.Boolean.mul_le_leafSize_of_computes_threshold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.mul_le_leafSize_of_computes_threshold

/--
info: 'Cslib.DecisionTree.complexity_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.DecisionTree.complexity_parity

/--
info: 'Cslib.DecisionTree.complexity_le_certificateComplexityFor_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.DecisionTree.complexity_le_certificateComplexityFor_mul

/--
info: 'Cslib.Circuits.Boolean.prod_card_subfunctions_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.prod_card_subfunctions_le

/--
info: 'Cslib.Circuits.Boolean.mul_le_leafSize_of_computes_elementDistinctness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.mul_le_leafSize_of_computes_elementDistinctness

/--
info: 'Cslib.Circuits.Boolean.formulaDepth_eq_ecomplexity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.formulaDepth_eq_ecomplexity

/--
info: 'Cslib.Circuits.Boolean.exists_monoidProgram_computes_of_formulaDepth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.exists_monoidProgram_computes_of_formulaDepth

/--
info: 'Cslib.BranchingPrograms.MonoidProgram.Computes.exists_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BranchingPrograms.MonoidProgram.Computes.exists_formula

/--
info: 'Cslib.BranchingPrograms.MonoidProgram.exists_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BranchingPrograms.MonoidProgram.exists_formula

/--
info: 'Cslib.DecisionTree.eval_toDNF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.DecisionTree.eval_toDNF

/--
info: 'Cslib.Circuits.Boolean.Restriction.card_withFree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Restriction.card_withFree

/--
info: 'Cslib.Logic.PL.DNF.eval_canonicalTree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.DNF.eval_canonicalTree

/--
info: 'Cslib.Logic.PL.DNF.complexity_lt_of_forall_pathLength_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.DNF.complexity_lt_of_forall_pathLength_lt

/--
info: 'Cslib.Logic.PL.DNF.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.DNF.decode_encode

/--
info: 'Cslib.Logic.PL.DNF.card_switching_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.DNF.card_switching_le

/--
info: 'Turing.MultiTapeTM.runFrom_shadow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.runFrom_shadow

/--
info: 'Turing.MultiTapeTM.runFrom_clearShadowed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.runFrom_clearShadowed

/--
info: 'Turing.MultiTapeTM.exists_runPath_seq_space' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.exists_runPath_seq_space

/--
info: 'Turing.MultiTapeTM.exists_runPath_tidy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.exists_runPath_tidy

/--
info: 'Turing.MultiTapeTM.ComputesInTimeAndSpace.computesTidily_tidy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputesInTimeAndSpace.computesTidily_tidy

/--
info: 'Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace

/--
info: 'Cslib.Circuits.Boolean.Restriction.card_extensions' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Restriction.card_extensions

/--
info: 'Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_computes_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_computes_parity

/--
info: 'Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_formula_computes_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_formula_computes_parity

/--
info: 'Cslib.Circuits.Boolean.parity_notMem_AC0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.parity_notMem_AC0

/--
info: 'Cslib.PolynomiallyBounded.eventually_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PolynomiallyBounded.eventually_lt_two_pow

/--
info: 'Cslib.Circuits.Boolean.majority_notMem_AC0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.majority_notMem_AC0

/--
info: 'Cslib.Circuits.Circuit.depth_comp_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.depth_comp_le

/--
info: 'Cslib.Circuits.Circuit.depth_append_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.depth_append_le

/--
info: 'Cslib.Circuits.Boolean.ConstDepth.compl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.ConstDepth.compl

/--
info: 'Cslib.Circuits.Boolean.AC0_ssubset_TC0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.AC0_ssubset_TC0

/--
info: 'Cslib.Circuits.Circuit.eval_mapOp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.eval_mapOp

/--
info: 'Cslib.Circuits.Boolean.Smolensky.exists_lowDegree_approx' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Smolensky.exists_lowDegree_approx

/--
info: 'Cslib.BitString.card_agree_parity_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.card_agree_parity_le

/--
info: 'Cslib.Circuits.Boolean.Smolensky.two_mul_two_pow_le_size_of_computes_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Smolensky.two_mul_two_pow_le_size_of_computes_parity

/--
info: 'Cslib.Circuits.Boolean.Smolensky.parity_notMem_AC0Mod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Smolensky.parity_notMem_AC0Mod

/--
info: 'Cslib.Circuits.Boolean.ConstDepth.parity_mem_of_majority_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.ConstDepth.parity_mem_of_majority_mem

/--
info: 'Cslib.Circuits.Boolean.parity_mem_TC0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.parity_mem_TC0

/--
info: 'Cslib.Circuits.Boolean.Smolensky.majority_notMem_AC0Mod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Smolensky.majority_notMem_AC0Mod

/--
info: 'Cslib.Circuits.Boolean.Smolensky.TC0_not_subset_AC0Mod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Smolensky.TC0_not_subset_AC0Mod

/--
info: 'Cslib.Circuits.Boolean.exists_formula_depthWith_le_four_mul_clog' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.exists_formula_depthWith_le_four_mul_clog

/--
info: 'Cslib.Circuits.Boolean.leafSize_le_two_pow_depthWith_binaryCost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.leafSize_le_two_pow_depthWith_binaryCost

/--
info: 'Cslib.Circuits.Boolean.formulaDepth_le_four_mul_clog' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.formulaDepth_le_four_mul_clog

/--
info: 'Cslib.BitString.sum_fourierCoeff_mul_chi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.sum_fourierCoeff_mul_chi

/--
info: 'Cslib.BitString.expect_mul_eq_sum_fourierCoeff_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.expect_mul_eq_sum_fourierCoeff_mul

/--
info: 'Cslib.BitString.sum_fourierCoeff_sq_signVal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.sum_fourierCoeff_sq_signVal

/--
info: 'Cslib.DecisionTree.fourierCoeff_eq_zero_of_depth_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.DecisionTree.fourierCoeff_eq_zero_of_depth_lt

/--
info: 'Cslib.IsGrading.exists_sdiff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.IsGrading.exists_sdiff

/--
info: 'Cslib.BitString.expect_sum_fourierCoeff_piecewise_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.expect_sum_fourierCoeff_piecewise_sq

/--
info: 'Cslib.Circuits.Boolean.complexity_existsGuess_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.complexity_existsGuess_le

/--
info: 'Cslib.Logic.PL.CNF.derives_nil_iff_not_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.derives_nil_iff_not_satisfiable

/--
info: 'Cslib.Circuits.Boolean.ModelChecking.exists_formula_realize_structure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.ModelChecking.exists_formula_realize_structure

/--
info: 'card_mul_sum_choose_le_of_two_mul_lt_hammingDist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms card_mul_sum_choose_le_of_two_mul_lt_hammingDist

/--
info: 'Cslib.Circuits.Boolean.NC_subset_AC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.NC_subset_AC

/--
info: 'Cslib.Circuits.Boolean.Unbounded.two_pow_mul_card_filter_exists_not_shallow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Unbounded.two_pow_mul_card_filter_exists_not_shallow_le

/--
info: 'Cslib.Circuits.Boolean.Unbounded.sum_fourierCoeff_sq_le_of_computes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Unbounded.sum_fourierCoeff_sq_le_of_computes

/--
info: 'Cslib.Logic.PL.CNF.sum_two_rpow_card_isolated_div_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.sum_two_rpow_card_isolated_div_le

/--
info: 'Cslib.Logic.PL.CNF.sparsification' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.sparsification

/--
info: 'exists_pow_le_card_mul_sum_choose_of_le_hammingDist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_pow_le_card_mul_sum_choose_of_le_hammingDist

/--
info: 'Cslib.Logic.PL.CNF.card_isolatedInputs_mul_two_rpow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.card_isolatedInputs_mul_two_rpow_le

/--
info: 'Cslib.Logic.PL.CNF.two_pow_le_length_of_eval_eq_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.two_pow_le_length_of_eval_eq_parity

/--
info: 'Cslib.Logic.PL.CNF.two_rpow_le_length_of_any_eval_eq_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.two_rpow_le_length_of_any_eval_eq_parity

/--
info: 'Cslib.Logic.PL.CNF.exists_any_eval_eq_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.exists_any_eval_eq_parity

/--
info: 'Cslib.Logic.PL.CNF.sum_two_rpow_sum_inv_critWidth_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.sum_two_rpow_sum_inv_critWidth_le

/--
info: 'Cslib.Logic.PL.CNF.two_rpow_sqrt_sub_one_le_of_any_eval_eq_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.two_rpow_sqrt_sub_one_le_of_any_eval_eq_parity

/--
info: 'Cslib.Circuits.Boolean.AltFormula.exists_of_isSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.AltFormula.exists_of_isSymmetric

/--
info: 'Cslib.Circuits.Boolean.Unbounded.exists_circuit_of_isSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Unbounded.exists_circuit_of_isSymmetric

/--
info: 'Cslib.Logic.PL.ClauseSet.sparsification' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.ClauseSet.sparsification

/--
info: 'Cslib.Logic.PL.CNF.two_pow_mul_min_le_of_any_eval_eq_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.two_pow_mul_min_le_of_any_eval_eq_parity

/--
info: 'exists_prod_le_card_mul_card_filter_hammingDist_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_prod_le_card_mul_card_filter_hammingDist_lt

/--
info: 'Cslib.Circuits.Boolean.Unbounded.two_rpow_lt_add_size_of_computes_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Unbounded.two_rpow_lt_add_size_of_computes_parity

/--
info: 'Cslib.Circuits.Boolean.Unbounded.pow_lt_size_of_computes_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Unbounded.pow_lt_size_of_computes_parity

/--
info: 'Cslib.Communication.parity_communication_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Communication.parity_communication_lower_bound

/--
info: 'Cslib.Circuits.Boolean.Unbounded.two_rpow_lt_add_size_of_computes_majority' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Unbounded.two_rpow_lt_add_size_of_computes_majority

/--
info: 'Cslib.Circuits.Boolean.Unbounded.pow_lt_size_of_computes_majority' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Unbounded.pow_lt_size_of_computes_majority

/--
info: 'Cslib.Logic.PL.ClauseSet.card_solutions_le_of_not_containsSubcube' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.ClauseSet.card_solutions_le_of_not_containsSubcube

/--
info: 'Cslib.Logic.PL.eventually_two_rpow_le_sigmaThreeSize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.eventually_two_rpow_le_sigmaThreeSize

/--
info: 'Cslib.Circuits.Boolean.AltFormula.two_rpow_lt_size_of_eval_eq_majority' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.AltFormula.two_rpow_lt_size_of_eval_eq_majority

/--
info: 'Cslib.Circuits.Boolean.AltFormula.exists_majority' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.AltFormula.exists_majority

/--
info: 'Cslib.Communication.strictMajority_communication_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Communication.strictMajority_communication_lower_bound

/--
info: 'Cslib.BitString.exists_mirror_set' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.exists_mirror_set

/--
info: 'Cslib.BitString.influence_eq_sum_fourierCoeff_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.influence_eq_sum_fourierCoeff_sq

/--
info: 'Cslib.BitString.totalInfluence_signVal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.totalInfluence_signVal

/--
info: 'Cslib.BitString.expect_sub_expect_sq_le_totalInfluence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.expect_sub_expect_sq_le_totalInfluence

/--
info: 'Cslib.BitString.fourierCoeff_noiseOp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.fourierCoeff_noiseOp

/--
info: 'Cslib.BitString.noiseStability_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.noiseStability_eq_sum

/--
info: 'Cslib.BitString.noiseSensitivity_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.noiseSensitivity_eq_sum

/--
info: 'Cslib.BitString.fourierCoeff_convolution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.fourierCoeff_convolution

/--
info: 'Cslib.BitString.exists_eq_parityOn_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.exists_eq_parityOn_iff

/--
info: 'Cslib.BitString.blrAcceptance_eq_sum_fourierCoeff_pow_three' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.blrAcceptance_eq_sum_fourierCoeff_pow_three

/--
info: 'Cslib.BitString.exists_hammingDist_parityOn_le_of_le_blrAcceptance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.exists_hammingDist_parityOn_le_of_le_blrAcceptance

/--
info: 'Cslib.Logic.PL.CNF.rpow_mul_two_rpow_sqrt_sub_one_le_of_any_eval_eq_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.rpow_mul_two_rpow_sqrt_sub_one_le_of_any_eval_eq_parity

/--
info: 'Cslib.Logic.PL.DNF.rpow_mul_two_rpow_sqrt_sub_one_le_of_all_eval_eq_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.DNF.rpow_mul_two_rpow_sqrt_sub_one_le_of_all_eval_eq_parity

/--
info: 'Cslib.Circuits.Boolean.AC_subset_NC_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.AC_subset_NC_succ

/--
info: 'Cslib.Circuits.Boolean.iUnion_NC_eq_iUnion_AC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.iUnion_NC_eq_iUnion_AC

/--
info: 'Cslib.Circuits.Boolean.Unbounded.exists_deMorgan_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Unbounded.exists_deMorgan_simulation

/--
info: 'Cslib.DecisionTree.totalInfluence_le_depth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.DecisionTree.totalInfluence_le_depth

/--
info: 'Cslib.Circuits.Monotone.eformulaDepth_eq_ecomplexity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Monotone.eformulaDepth_eq_ecomplexity

/--
info: 'Cslib.exists_forall_exists_add_mem_of_card_mul_card_compl_pow_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.exists_forall_exists_add_mem_of_card_mul_card_compl_pow_lt

/--
info: 'Cslib.BitString.mem_iff_exists_forall_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.mem_iff_exists_forall_exists

/--
info: 'Cslib.BitString.mem_iff_forall_exists_forall' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.mem_iff_forall_exists_forall

/--
info: 'Cslib.Circuits.Boolean.NC_one_eq_polyLength_perm_five' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.NC_one_eq_polyLength_perm_five

/--
info: 'Cslib.Circuits.Boolean.NC_one_eq_polyLength_end' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.NC_one_eq_polyLength_end

/--
info: 'Cslib.Circuits.Boolean.mem_NC_one_iff_formulaDepth_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.mem_NC_one_iff_formulaDepth_le

/--
info: 'Cslib.Circuits.Circuit.size_toFormula_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.size_toFormula_lt

/--
info: 'Cslib.Crypto.PRG.Generator.exists_half_add_div_le_predictionExperiment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.Generator.exists_half_add_div_le_predictionExperiment

/--
info: 'Cslib.Crypto.PRG.Generator.Unpredictable.secure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.Generator.Unpredictable.secure

/--
info: 'Cslib.Crypto.PRG.Generator.Secure.unpredictable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.Generator.Secure.unpredictable

/--
info: 'Cslib.Probability.IsPairwiseIndependentHash.three_quarters_mul_le_dens_filter_mem_image' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
open Cslib.Probability in
#print axioms IsPairwiseIndependentHash.three_quarters_mul_le_dens_filter_mem_image

/--
info: 'Cslib.Probability.IsPairwiseIndependentHash.three_sixteenths_le_dens_filter_card_filter_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
open Cslib.Probability in
#print axioms IsPairwiseIndependentHash.three_sixteenths_le_dens_filter_card_filter_eq_one

/--
info: 'Cslib.Probability.isPairwiseIndependentHash_affineHash' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.isPairwiseIndependentHash_affineHash

/--
info: 'Cslib.Probability.ApproximateCounting.three_quarters_le_dens_filter_affineHashEstimate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.ApproximateCounting.three_quarters_le_dens_filter_affineHashEstimate

/--
info: 'Cslib.RotationMap.spectralExpansion_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_le_iff

/--
info: 'Cslib.RotationMap.abs_card_interedges_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.abs_card_interedges_sub_le

/--
info: 'Cslib.RotationMap.abs_card_interedges_sub_le_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.abs_card_interedges_sub_le_mul_sqrt

/--
info: 'Cslib.RotationMap.le_card_interedges_compl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.le_card_interedges_compl

/--
info: 'Cslib.RotationMap.exists_isSimple_toSimpleGraph_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.exists_isSimple_toSimpleGraph_eq

/--
info: 'Cslib.BitString.abs_expect_signVal_xorMajority_mul_signVal_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.abs_expect_signVal_xorMajority_mul_signVal_le

/--
info: 'Cslib.BitString.two_mul_card_agree_xorMajority_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.two_mul_card_agree_xorMajority_le

/--
info: 'Cslib.BitString.card_filter_selfCorrect_ne_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.card_filter_selfCorrect_ne_le

/--
info: 'Cslib.BitString.one_sub_two_mul_le_expect_selfCorrect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.one_sub_two_mul_le_expect_selfCorrect

/--
info: 'Cslib.BitString.exists_eq_hadamardCode_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.exists_eq_hadamardCode_iff

/--
info: 'Cslib.BitString.two_mul_hammingDist_hadamardCode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.two_mul_hammingDist_hadamardCode

/--
info: 'Cslib.BitString.eq_of_hammingDist_hadamardCode_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.eq_of_hammingDist_hadamardCode_le

/--
info: 'Cslib.BitString.one_sub_two_mul_le_expect_selfCorrect_eq_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.one_sub_two_mul_le_expect_selfCorrect_eq_apply

/--
info: 'Cslib.BitString.existsUnique_hammingDist_hadamardCode_le_of_le_blrAcceptance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.existsUnique_hammingDist_hadamardCode_le_of_le_blrAcceptance

/--
info: 'Cslib.BitString.hadamardCode_tensor_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.hadamardCode_tensor_tensor

/--
info: 'Cslib.BitString.one_div_four_le_expect_hadamardCode_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.one_div_four_le_expect_hadamardCode_tensor

/--
info: 'Cslib.BitString.eq_tensor_of_lt_tensorTestAcceptance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.eq_tensor_of_lt_tensorTestAcceptance

/--
info: 'Cslib.BitString.hadamardCode_eq_of_lt_equationTestAcceptance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.hadamardCode_eq_of_lt_equationTestAcceptance

/--
info: 'Cslib.BitString.exists_forall_hadamardCode_tensor_eq_of_le_blrAcceptance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.exists_forall_hadamardCode_tensor_eq_of_le_blrAcceptance

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.exists_predictionExperiment_le_hardwiredExperiment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.exists_predictionExperiment_le_hardwiredExperiment

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.exists_half_add_div_le_hardwiredExperiment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.exists_half_add_div_le_hardwiredExperiment

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.exists_half_add_div_le_card_nextBitGuess_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.exists_half_add_div_le_card_nextBitGuess_eq

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.exists_dependsOn_half_add_div_le_card_nextBitGuess_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.exists_dependsOn_half_add_div_le_card_nextBitGuess_eq

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.exists_complexity_le_half_add_div_le_card_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.exists_complexity_le_half_add_div_le_card_eq

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.toReal_realExperiment_sub_toReal_idealExperiment_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.toReal_realExperiment_sub_toReal_idealExperiment_lt

/--
info: 'Cslib.Circuits.Boolean.complexity_le_of_dependsOn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.complexity_le_of_dependsOn

/--
info: 'Cslib.Circuits.Boolean.dist_complexity_le_of_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.dist_complexity_le_of_cover

/--
info: 'Cslib.Circuits.Boolean.complexityGiven_le_of_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.complexityGiven_le_of_cover

/--
info: 'Cslib.Circuits.Boolean.SparseSynthesis.complexity_indicator_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.SparseSynthesis.complexity_indicator_le

/--
info: 'Cslib.Circuits.Boolean.SparseSynthesis.complexityOn_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.SparseSynthesis.complexityOn_le

/--
info: 'Cslib.Circuits.Boolean.SparseSynthesis.dist_complexity_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.SparseSynthesis.dist_complexity_le

/--
info: 'Cslib.Circuits.Boolean.SparseSynthesis.dist_complexity_single_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.SparseSynthesis.dist_complexity_single_le

/--
info: 'Cslib.Circuits.Boolean.SparseSynthesis.exists_hard_indicator' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.SparseSynthesis.exists_hard_indicator

/--
info: 'Cslib.Circuits.Boolean.SparseSynthesis.not_isLittleO_of_dist_complexity_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.SparseSynthesis.not_isLittleO_of_dist_complexity_le

/--
info: 'Cslib.Circuits.Boolean.SparseSynthesis.le_vcDim_circuitSets' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.SparseSynthesis.le_vcDim_circuitSets

/--
info: 'Cslib.RotationMap.card_mul_one_sub_secondEigenvalue_div_two_le_edgeExpansion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.card_mul_one_sub_secondEigenvalue_div_two_le_edgeExpansion

/--
info: 'Cslib.RotationMap.expect_mul_walk_le_of_mul_card_le_card_interedges_compl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.expect_mul_walk_le_of_mul_card_le_card_interedges_compl

/--
info: 'Cslib.RotationMap.secondEigenvalue_le_one_sub_edgeExpansion_sq_div' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.secondEigenvalue_le_one_sub_edgeExpansion_sq_div

/--
info: 'Cslib.RotationMap.edgeExpansion_le_card_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.edgeExpansion_le_card_mul_sqrt

/--
info: 'Cslib.RotationMap.spectralExpansion_eq_secondEigenvalue_of_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_eq_secondEigenvalue_of_nonneg

/--
info: 'Cslib.RotationMap.spectralExpansion_le_one_sub_edgeExpansion_sq_div' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_le_one_sub_edgeExpansion_sq_div

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.Design.nonempty_four_mul_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.Design.nonempty_four_mul_sq

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.Design.nonempty_of_isPrimePow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.Design.nonempty_of_isPrimePow

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.card_polynomialBlock_inter_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.card_polynomialBlock_inter_le

/--
info: 'Cslib.Probability.ApproximateCounting.le_nthRoot_and_mul_nthRoot_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.ApproximateCounting.le_nthRoot_and_mul_nthRoot_le

/--
info: 'Cslib.Probability.ApproximateCounting.dens_filter_not_relativeHashEstimate_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.ApproximateCounting.dens_filter_not_relativeHashEstimate_le

/--
info: 'Cslib.Probability.ApproximateCounting.one_sub_inv_two_pow_le_dens_filter_relativeHashEstimate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
open Cslib.Probability.ApproximateCounting in
#print axioms one_sub_inv_two_pow_le_dens_filter_relativeHashEstimate

/--
info: 'Cslib.Probability.ApproximateCounting.one_sub_inv_two_pow_le_dens_filter_affineRelativeHashEstimate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
open Cslib.Probability.ApproximateCounting in
#print axioms one_sub_inv_two_pow_le_dens_filter_affineRelativeHashEstimate

/--
info: 'Cslib.RotationMap.walk_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.walk_pow

/--
info: 'Cslib.RotationMap.spectralExpansion_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_pow

/--
info: 'Cslib.RotationMap.spectralExpansion_tensor_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_tensor_le

/--
info: 'Cslib.RotationMap.spectralExpansion_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_tensor

/--
info: 'Cslib.RotationMap.walk_zigzag' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.walk_zigzag

/--
info: 'Cslib.RotationMap.spectralExpansion_zigzag_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_zigzag_le

/--
info: 'Cslib.RotationMap.spectralExpansion_zigzag_le_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_zigzag_le_one_sub

/--
info: 'Cslib.RotationMap.walk_balancedReplacement' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.walk_balancedReplacement

/--
info: 'Cslib.RotationMap.spectralExpansion_balancedReplacement_pow_three_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_balancedReplacement_pow_three_le

/--
info: 'Cslib.RotationMap.spectralExpansion_balancedReplacement_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_balancedReplacement_le

/--
info: 'Cslib.Probability.isPairwiseIndependentHash_add_of_dens_filter_sub_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.isPairwiseIndependentHash_add_of_dens_filter_sub_eq

/--
info: 'Cslib.Probability.isPairwiseIndependentHash_add_of_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.isPairwiseIndependentHash_add_of_shift

/--
info: 'Cslib.Probability.isPairwiseIndependentHash_add_of_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.isPairwiseIndependentHash_add_of_surjective

/--
info: 'Cslib.Probability.isPairwiseIndependentHash_toeplitzHash' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.isPairwiseIndependentHash_toeplitzHash

/--
info: 'Cslib.Probability.card_toeplitzHash_seed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.card_toeplitzHash_seed

/--
info: 'Matrix.toeplitz_mulVec_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.toeplitz_mulVec_surjective

/--
info: 'Cslib.RotationMap.spectralExpansion_union_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_union_le

/--
info: 'Cslib.RotationMap.spectralExpansion_lazy_le_one_sub_edgeExpansion_sq_div' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_lazy_le_one_sub_edgeExpansion_sq_div

/--
info: 'Cslib.RotationMap.spectralExpansion_lazy_le_of_mul_card_le_card_interedges_compl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_lazy_le_of_mul_card_le_card_interedges_compl

/--
info: 'Cslib.RotationMap.card_interedges_compl_ofPerms' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.card_interedges_compl_ofPerms

/--
info: 'Cslib.RotationMap.le_edgeExpansion_ofPerms' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.le_edgeExpansion_ofPerms

/--
info: 'Cslib.RotationMap.exists_spectralExpansion_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.exists_spectralExpansion_le

/--
info: 'Cslib.RotationMap.exists_forall_exists_spectralExpansion_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.exists_forall_exists_spectralExpansion_le

/--
info: 'Cslib.exists_perms_card_le_mul_card_filter_notMem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.exists_perms_card_le_mul_card_filter_notMem

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.complexity_le_natCast_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.complexity_le_natCast_iff

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.timeBoundedComplexity_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.timeBoundedComplexity_antitone

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.iInf_timeBoundedComplexity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.iInf_timeBoundedComplexity

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.encard_setOf_complexity_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.encard_setOf_complexity_lt

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.exists_length_eq_forall_le_timeBoundedComplexity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.exists_length_eq_forall_le_timeBoundedComplexity

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.encard_setOf_length_eq_complexity_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.encard_setOf_length_eq_complexity_lt

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.Simulation.complexity_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.Simulation.complexity_le

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.Simulation.timeBoundedComplexity_le_of_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.Simulation.timeBoundedComplexity_le_of_polynomial

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.IsAdditivelyOptimal.invariance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.IsAdditivelyOptimal.invariance

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.mem_ofMultiTapeTM_run_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.mem_ofMultiTapeTM_run_iff

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.exists_simulation_literal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.exists_simulation_literal

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.Composition.complexity_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.Composition.complexity_le

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.depthBetween_add_depth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.depthBetween_add_depth

/--
info: 'Cslib.Logic.FO.Interpretation.realize_onSentence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Interpretation.realize_onSentence

/--
info: 'Cslib.Logic.FO.Interpretation.compEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Interpretation.compEquiv

/--
info: 'Cslib.Logic.FO.Interpretation.realize_onESOSentence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Interpretation.realize_onESOSentence

/--
info: 'Cslib.Logic.FO.Definable.of_reduces' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Definable.of_reduces

/--
info: 'Cslib.Logic.FO.Reduces.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Reduces.trans

/--
info: 'Cslib.Logic.FO.Definable.simpleGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Definable.simpleGraph

/--
info: 'Cslib.Logic.ESO.Sentence.realize_iff_of_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Sentence.realize_iff_of_equiv

/--
info: 'Cslib.Logic.ESO.Sentence.realize_colorable_structure_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Sentence.realize_colorable_structure_iff

/--
info: 'Cslib.Logic.ESO.Definable.of_fo' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Definable.of_fo

/--
info: 'Cslib.Logic.ESO.Definable.of_reduces' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Definable.of_reduces

/--
info: 'Cslib.Logic.ESO.Definable.colorable_simpleGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Definable.colorable_simpleGraph

/--
info: 'Cslib.RotationMap.expect_splitWalk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.expect_splitWalk

/--
info: 'Cslib.RotationMap.card_filter_splitWalk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.card_filter_splitWalk

/--
info: 'Cslib.RotationMap.sum_walkDart' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.sum_walkDart

/--
info: 'Cslib.RotationMap.expect_walkDart_mul_walkDart' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.expect_walkDart_mul_walkDart

/--
info: 'Cslib.RotationMap.sq_expect_walkDart_mul_walkDart_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.sq_expect_walkDart_mul_walkDart_sub_le

/--
info: 'Cslib.RotationMap.card_filter_killTime_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.card_filter_killTime_eq

/--
info: 'Cslib.RotationMap.card_filter_killTime_eq_and_splitWalk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.card_filter_killTime_eq_and_splitWalk

/--
info: 'Cslib.PCP.ConstraintGraph.exists_unsatFrac_eq_unsatVal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.exists_unsatFrac_eq_unsatVal

/--
info: 'Cslib.PCP.ConstraintGraph.unsatVal_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.unsatVal_eq_zero_iff

/--
info: 'Cslib.PCP.ConstraintGraph.card_mul_unsatVal_add_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.card_mul_unsatVal_add_le

/--
info: 'Cslib.PCP.ConstraintGraph.unsatVal_map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.unsatVal_map

/--
info: 'Cslib.PCP.ConstraintGraph.satisfiable_ofCNF_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.satisfiable_ofCNF_iff

/--
info: 'Cslib.PCP.ConstraintGraph.le_unsatVal_ofCNF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.le_unsatVal_ofCNF

/--
info: 'Cslib.PCP.ConstraintGraph.le_unsatVal_degreeReduce' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.le_unsatVal_degreeReduce

/--
info: 'Cslib.PCP.ConstraintGraph.spectralExpansion_preprocess_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.spectralExpansion_preprocess_le

/--
info: 'Cslib.PCP.ConstraintGraph.satisfiable_preprocess_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.satisfiable_preprocess_iff

/--
info: 'Cslib.PCP.ConstraintGraph.le_unsatVal_preprocess' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.le_unsatVal_preprocess

/--
info: 'Relation.RelatesWithinSteps.add_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Relation.RelatesWithinSteps.add_iff

/--
info: 'Relation.RelatesWithinSteps.two_pow_succ_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Relation.RelatesWithinSteps.two_pow_succ_iff

/--
info: 'Relation.reflTransGen_iff_relatesWithinSteps_two_pow_clog' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Relation.reflTransGen_iff_relatesWithinSteps_two_pow_clog

/--
info: 'Relation.reachableWithin_eq_of_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Relation.reachableWithin_eq_of_card_le

/--
info: 'Relation.IsRoundList.mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Relation.IsRoundList.mem_iff

/--
info: 'Relation.exists_isRoundList' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Relation.exists_isRoundList

/--
info: 'Relation.not_relatesWithinSteps_succ_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Relation.not_relatesWithinSteps_succ_iff

/--
info: 'Relation.not_reflTransGen_iff_exists_isRoundList' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Relation.not_reflTransGen_iff_exists_isRoundList

/--
info: 'Cslib.RotationMap.spectralExpansion_zigzagTower_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_zigzagTower_le

/--
info: 'Cslib.RotationMap.spectralExpansion_zigzagTower_le_two_div_five' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_zigzagTower_le_two_div_five

/--
info: 'Cslib.RotationMap.card_zigzagTowerVertex_of_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.card_zigzagTowerVertex_of_equiv

/--
info: 'Cslib.RotationMap.spectralExpansion_zigzagTowerBase_le_one_div_five' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_zigzagTowerBase_le_one_div_five

/--
info: 'Cslib.RotationMap.exists_spectralExpansion_zigzagTower_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.exists_spectralExpansion_zigzagTower_le

/--
info: 'Cslib.RAM.logGap_squaring' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RAM.logGap_squaring

/--
info: 'Cslib.RAM.bitLength_read_run_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RAM.bitLength_read_run_le

/--
info: 'Cslib.Circuits.Frontier.RectangleFree.pow_ncard_compl_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.RectangleFree.pow_ncard_compl_lt

/--
info: 'Cslib.Circuits.Frontier.Sweep.ncard_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Sweep.ncard_le

/--
info: 'Cslib.Circuits.Frontier.Multigraph.card_le_card_add_one_of_connected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Multigraph.card_le_card_add_one_of_connected

/--
info: 'Cslib.Circuits.Frontier.Network.Satisfies.splice' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Network.Satisfies.splice

/--
info: 'Cslib.Circuits.Frontier.Network.ncard_accepted_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Network.ncard_accepted_le

/--
info: 'Cslib.Circuits.Frontier.eventually_lt_of_demand' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_lt_of_demand

/--
info: 'Set.ncard_le_mul_ncard_image' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Set.ncard_le_mul_ncard_image

end ComplexityTests.Axioms
