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
info: 'Cslib.Complexity.SAT.computableTidilyInPolyTime_verifier' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.SAT.computableTidilyInPolyTime_verifier

/--
info: 'Cslib.Complexity.SAT.mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.SAT.mem_NP

/--
info: 'Cslib.Complexity.UNSAT_mem_coNP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.UNSAT_mem_coNP

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
info: 'Cslib.Circuits.Boolean.exists_monoidProgram_alternatingGroup_computes_of_mem_NC_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.exists_monoidProgram_alternatingGroup_computes_of_mem_NC_one

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
info: 'Cslib.BitString.PartialAssignment.card_withFree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.PartialAssignment.card_withFree

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
info: 'Turing.MultiTapeTM.exists_runPath_seq_space_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.exists_runPath_seq_space_le

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
info: 'Cslib.BitString.PartialAssignment.card_extensions' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.PartialAssignment.card_extensions

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
info: 'Cslib.Circuits.Boolean.NC_one_eq_polyLength_alternatingGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.NC_one_eq_polyLength_alternatingGroup

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
info: 'Cslib.Kolmogorov.DescriptionMethod.ecomplexity_le_natCast_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.ecomplexity_le_natCast_iff

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.etimeBoundedComplexity_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.etimeBoundedComplexity_antitone

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.iInf_etimeBoundedComplexity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.iInf_etimeBoundedComplexity

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.encard_setOf_ecomplexity_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.encard_setOf_ecomplexity_lt

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.exists_length_eq_forall_le_etimeBoundedComplexity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.exists_length_eq_forall_le_etimeBoundedComplexity

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.encard_setOf_length_eq_ecomplexity_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.encard_setOf_length_eq_ecomplexity_lt

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.Simulation.ecomplexity_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.Simulation.ecomplexity_le

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.Simulation.etimeBoundedComplexity_le_of_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.Simulation.etimeBoundedComplexity_le_of_polynomial

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.IsAdditivelyOptimal.invariance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.IsAdditivelyOptimal.invariance

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.mem_ofMultiTapeTM_runFor_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.mem_ofMultiTapeTM_runFor_iff

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.exists_simulation_literal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.exists_simulation_literal

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.Composition.ecomplexity_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.Composition.ecomplexity_le

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.depthBetween_add_depth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.depthBetween_add_depth

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.isPartrec_universal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.isPartrec_universal

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.isAdditivelyOptimal_universal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.isAdditivelyOptimal_universal

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
info: 'Cslib.Logic.FO.Reduces.isoClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Reduces.isoClosed

/--
info: 'Cslib.Logic.ESO.Definable.isoClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Definable.isoClosed

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
info: 'Cslib.RotationMap.mul_card_filter_ne_le_card_filter_ne_neighbor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.mul_card_filter_ne_le_card_filter_ne_neighbor

/--
info: 'Cslib.PCP.ConstraintGraph.unsatVal_reindex' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.unsatVal_reindex

/--
info: 'Cslib.PCP.RegularConstraintGraph.unsatVal_addTrivial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.RegularConstraintGraph.unsatVal_addTrivial

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
info: 'Cslib.PCP.ConstraintGraph.spectralExpansion_preprocess_expanderFamily_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.spectralExpansion_preprocess_expanderFamily_le

/--
info: 'Cslib.PCP.ConstraintGraph.le_unsatVal_preprocess_expanderFamily' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.le_unsatVal_preprocess_expanderFamily

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
info: 'Cslib.RAM.computesInTime_unitCost_repeatedSquaring' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RAM.computesInTime_unitCost_repeatedSquaring

/--
info: 'Cslib.RAM.exists_mul_pow_lt_of_computesInTime_logCost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RAM.exists_mul_pow_lt_of_computesInTime_logCost

/--
info: 'Cslib.RAM.haltsWithResult_iff_eval' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RAM.haltsWithResult_iff_eval

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
info: 'Cslib.Circuits.Frontier.RectangleBias.abs_signedCount_le_of_dependsOn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.RectangleBias.abs_signedCount_le_of_dependsOn

/--
info: 'Cslib.Circuits.Frontier.ReadOnceNBP.ncard_accepted_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.ReadOnceNBP.ncard_accepted_le

/--
info: 'Cslib.Circuits.Frontier.ReadOnceNBP.abs_signedCount_accepted_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.ReadOnceNBP.abs_signedCount_accepted_le

/--
info: 'Cslib.Circuits.Frontier.Network.accepted_branchingProgram' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Network.accepted_branchingProgram

/--
info: 'Cslib.Circuits.Frontier.Network.abs_signedCount_accepted_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Network.abs_signedCount_accepted_le

/--
info: 'Cslib.Circuits.Frontier.eventually_add_lt_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_add_lt_of_le

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

/--
info: 'Fintype.expect_sub_div_le_dens_filter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fintype.expect_sub_div_le_dens_filter

/--
info: 'Fintype.dens_filter_exists_apply_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fintype.dens_filter_exists_apply_mem

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.expect_trialAgreement' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.expect_trialAgreement

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.div_two_mul_le_dens_goodTrials' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.div_two_mul_le_dens_goodTrials

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.half_le_dens_exists_mem_goodTrials' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.half_le_dens_exists_mem_goodTrials

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.reconstructionBits_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.reconstructionBits_le

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.one_sub_pow_le_dens_mem_trialCandidates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.one_sub_pow_le_dens_mem_trialCandidates

/--
info: 'Cslib.ListCode.ListDecodes.exists_decodeBits_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.ListCode.ListDecodes.exists_decodeBits_eq_some

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.ReconstructionDecoder.etimeBoundedComplexity_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.ReconstructionDecoder.etimeBoundedComplexity_le

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.ReconstructionDecoder.etimeBoundedComplexity_le_of_random' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
open Cslib.Kolmogorov.DescriptionMethod.ReconstructionDecoder in
#print axioms etimeBoundedComplexity_le_of_random

/--
info: 'Cslib.PCP.HadamardTester.exists_inputDist_div_le_one_sub_acceptProb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.HadamardTester.exists_inputDist_div_le_one_sub_acceptProb

/--
info: 'Cslib.PCP.HadamardTester.one_div_le_one_sub_acceptProb_of_forall_not' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.HadamardTester.one_div_le_one_sub_acceptProb_of_forall_not

/--
info: 'Cslib.PCP.HadamardTester.passes_honestProof' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.HadamardTester.passes_honestProof

/--
info: 'Cslib.PCP.HadamardTester.exists_inputDist_div_le_unsatFrac' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.HadamardTester.exists_inputDist_div_le_unsatFrac

/--
info: 'Cslib.PCP.HadamardTester.forall_hadamardCode_tensor_equationCoeff_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.HadamardTester.forall_hadamardCode_tensor_equationCoeff_iff

/--
info: 'Cslib.BitString.eq_of_hammingDist_longCode_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.eq_of_hammingDist_longCode_lt

/--
info: 'Cslib.PCP.LocalTest.one_sub_acceptProb_le_card_mul_unsatFrac' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.LocalTest.one_sub_acceptProb_le_card_mul_unsatFrac

/--
info: 'Cslib.PCP.ConstraintGraph.le_unsatVal_compose' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.le_unsatVal_compose

/--
info: 'Cslib.PCP.ConstraintGraph.unsatVal_compose_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.unsatVal_compose_le

/--
info: 'Cslib.PCP.ConstraintGraph.satisfiable_compose_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.satisfiable_compose_iff

/--
info: 'Cslib.PCP.ConstraintGraph.card_edges_compose' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.card_edges_compose

/--
info: 'Cslib.PCP.RegularConstraintGraph.satisfiable_power_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.RegularConstraintGraph.satisfiable_power_iff

/--
info: 'Cslib.PCP.RegularConstraintGraph.not_satisfies_of_hit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.RegularConstraintGraph.not_satisfies_of_hit

/--
info: 'Cslib.PCP.RegularConstraintGraph.le_expect_numHits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.RegularConstraintGraph.le_expect_numHits

/--
info: 'Cslib.PCP.RegularConstraintGraph.expect_numHits_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.RegularConstraintGraph.expect_numHits_sq_le

/--
info: 'Cslib.PCP.RegularConstraintGraph.le_unsatFrac_power' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.RegularConstraintGraph.le_unsatFrac_power

/--
info: 'Cslib.PCP.RegularConstraintGraph.le_unsatVal_power' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.RegularConstraintGraph.le_unsatVal_power

/--
info: 'Cslib.RotationMap.neighbor_pow_take_rot_killedPow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.neighbor_pow_take_rot_killedPow

/--
info: 'Cslib.Circuits.Frontier.Compiler.satisfies_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Compiler.satisfies_iff

/--
info: 'Cslib.Circuits.Frontier.Compiler.connected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Compiler.connected

/--
info: 'Cslib.Circuits.Frontier.Compiler.maxDegreeLE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Compiler.maxDegreeLE

/--
info: 'Cslib.Circuits.Frontier.Compiler.cycleRank_add_ncard_read_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Compiler.cycleRank_add_ncard_read_le

/--
info: 'Cslib.Circuits.Frontier.Compiler.card_vertex_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Compiler.card_vertex_le

/--
info: 'Cslib.Circuits.Frontier.Network.logb_ncard_accepted_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Network.logb_ncard_accepted_le

/--
info: 'Cslib.Circuits.Frontier.exists_graph_of_decides' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.exists_graph_of_decides

/--
info: 'Cslib.Circuits.Frontier.eventually_lt_mul_innerSize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_lt_mul_innerSize

/--
info: 'Cslib.Circuits.Frontier.eventually_lt_innerSize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_lt_innerSize

/--
info: 'Cslib.Circuits.Circuit.innerSize_le_size' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.innerSize_le_size

/--
info: 'Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_mul_innerSize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_mul_innerSize

/--
info: 'Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_innerSize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_innerSize

/--
info: 'Cslib.Circuits.Frontier.circuitLowerBound_of_layoutBound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.circuitLowerBound_of_layoutBound

/--
info: 'Cslib.Circuits.Frontier.averageCaseBound_of_layoutBound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.averageCaseBound_of_layoutBound

/--
info: 'Cslib.Circuits.Frontier.circuitLowerBound_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.circuitLowerBound_two

/--
info: 'Cslib.Circuits.Frontier.averageCaseBound_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.averageCaseBound_two

/--
info: 'Cslib.Circuits.Frontier.layoutBound_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.layoutBound_one

/--
info: 'Cslib.Circuits.Frontier.LayoutBound.of_cubic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.LayoutBound.of_cubic

/--
info: 'Cslib.Circuits.Frontier.Multigraph.exists_width_le_cycleRank_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Multigraph.exists_width_le_cycleRank_add

/--
info: 'Cslib.Circuits.Frontier.Multigraph.Compression.exists_width_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Multigraph.Compression.exists_width_le

/--
info: 'Cslib.Circuits.Frontier.Multigraph.Compression.Saturated.card_blocks_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Multigraph.Compression.Saturated.card_blocks_le

/--
info: 'Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_threshold_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_threshold_le

/--
info: 'Real.sum_arccos_le_card_mul_arccos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Real.sum_arccos_le_card_mul_arccos

/--
info: 'InnerProductGeometry.sum_offDiag_angle_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms InnerProductGeometry.sum_offDiag_angle_le

/--
info: 'InnerProductGeometry.angle_eq_two_mul_arctan' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms InnerProductGeometry.angle_eq_two_mul_arctan

/--
info: 'ProbabilityTheory.gaussianReal_Icc_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.gaussianReal_Icc_le

/--
info: 'ProbabilityTheory.stdGaussian_map_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.stdGaussian_map_inner

/--
info: 'ProbabilityTheory.measurePreserving_toLp_pi_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.measurePreserving_toLp_pi_gaussianReal

/--
info: 'ProbabilityTheory.gaussianReal_prod_setOf_abs_le_mul_abs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.gaussianReal_prod_setOf_abs_le_mul_abs

/--
info: 'ProbabilityTheory.measureReal_stdGaussian_mem_uIoc_le_angle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.measureReal_stdGaussian_mem_uIoc_le_angle

/--
info: 'ProbabilityTheory.variance_sum_indicator_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.variance_sum_indicator_le

/--
info: 'ProbabilityTheory.measureReal_pi_le_abs_sum_indicator_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.measureReal_pi_le_abs_sum_indicator_sub_le

/--
info: 'SimpleGraph.card_edist_le_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SimpleGraph.card_edist_le_le

/--
info: 'Cslib.Circuits.Frontier.Gaussian.le_inner_unitKernelRow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Gaussian.le_inner_unitKernelRow

/--
info: 'Matrix.isTotallyRegular_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.isTotallyRegular_cauchy

/--
info: 'Matrix.isTotallyRegular_cauchyNat_zmod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.isTotallyRegular_cauchyNat_zmod

/--
info: 'Cslib.Circuits.Circuit.Computes.exists_affine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.Computes.exists_affine

/--
info: 'Cslib.Circuits.Frontier.exists_graph_of_isTotallyRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.exists_graph_of_isTotallyRegular

/--
info: 'Cslib.Circuits.Frontier.eventually_lt_mul_innerSize_of_isTotallyRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_lt_mul_innerSize_of_isTotallyRegular

/--
info: 'Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_innerSize_arith_cauchyNat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_innerSize_arith_cauchyNat

/--
info: 'Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_innerSize_cauchyNat_zmod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_innerSize_cauchyNat_zmod

/--
info: 'Cslib.Circuits.Frontier.Network.accepted_hide' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Network.accepted_hide

/--
info: 'Cslib.Circuits.Frontier.Compiler.accepted_hiddenNetwork' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Compiler.accepted_hiddenNetwork

/--
info: 'Cslib.Circuits.Frontier.exists_graph_of_nondeterministicDecides' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.exists_graph_of_nondeterministicDecides

/--
info: 'Cslib.Circuits.Frontier.eventually_lt_mul_innerSize_of_nondeterministicDecides' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_lt_mul_innerSize_of_nondeterministicDecides

/--
info: 'Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_innerSize_of_nondeterministicDecides' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_innerSize_of_nondeterministicDecides

/--
info: 'Cslib.Circuits.DecomposableDAG.ncard_accepted_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.DecomposableDAG.ncard_accepted_le

/--
info: 'Cslib.Circuits.DecomposableDAG.ncard_accepted_le_size' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.DecomposableDAG.ncard_accepted_le_size

/--
info: 'Cslib.PCP.ConstraintGraph.le_unsatVal_amplify' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.le_unsatVal_amplify

/--
info: 'Cslib.PCP.ConstraintGraph.satisfiable_amplify_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.satisfiable_amplify_iff

/--
info: 'Cslib.PCP.ConstraintGraph.card_edges_amplify' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.card_edges_amplify

/--
info: 'Cslib.PCP.ConstraintGraph.card_vertices_amplify' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.card_vertices_amplify

/--
info: 'Cslib.PCP.Dinur.min_le_unsatVal_amplify' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Dinur.min_le_unsatVal_amplify

/--
info: 'Cslib.PCP.Dinur.satisfiable_amplify_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Dinur.satisfiable_amplify_iff

/--
info: 'Cslib.PCP.Amplifier.min_le_unsatVal_iter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Amplifier.min_le_unsatVal_iter

/--
info: 'Cslib.PCP.Amplifier.gap_le_unsatVal_iter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Amplifier.gap_le_unsatVal_iter

/--
info: 'Cslib.PCP.Amplifier.unsatVal_iter_eq_zero_or_gap_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Amplifier.unsatVal_iter_eq_zero_or_gap_le

/--
info: 'Cslib.PCP.Amplifier.satisfiable_iter_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Amplifier.satisfiable_iter_iff

/--
info: 'Cslib.PCP.Amplifier.card_edges_iter_clog_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Amplifier.card_edges_iter_clog_le

/--
info: 'Cslib.PCP.Amplifier.card_vertices_iter_clog_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Amplifier.card_vertices_iter_clog_le

/--
info: 'Cslib.PCP.Dinur.satisfiable_gapGraph_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Dinur.satisfiable_gapGraph_iff

/--
info: 'Cslib.PCP.Dinur.gap_le_unsatVal_gapGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Dinur.gap_le_unsatVal_gapGraph

/--
info: 'Cslib.PCP.Dinur.unsatVal_gapGraph_eq_zero_or_gap_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Dinur.unsatVal_gapGraph_eq_zero_or_gap_le

/--
info: 'Cslib.PCP.Dinur.exists_card_gapGraph_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Dinur.exists_card_gapGraph_le

/--
info: 'Cslib.Circuits.Frontier.LayoutBound.exists_layout_componentwise' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.LayoutBound.exists_layout_componentwise

/--
info: 'Cslib.Circuits.Frontier.Multigraph.connected_induce_component' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Multigraph.connected_induce_component

/--
info: 'Cslib.Circuits.Frontier.Compiler.cycleRankOn_add_ncard_readIn_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Compiler.cycleRankOn_add_ncard_readIn_le

/--
info: 'Cslib.Circuits.Frontier.Ledger.run_eq_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Ledger.run_eq_trace

/--
info: 'Cslib.Circuits.Frontier.Ledger.run_total_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Ledger.run_total_trace

/--
info: 'Cslib.Circuits.Frontier.Ledger.ofAggregates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Ledger.ofAggregates

/--
info: 'Cslib.Circuits.Frontier.aggregates_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.aggregates_unbounded

/--
info: 'Cslib.Circuits.Frontier.aggregates_countMod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.aggregates_countMod

/--
info: 'Cslib.Circuits.Frontier.Ledger.mem_of_splice' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Ledger.mem_of_splice

/--
info: 'Cslib.Circuits.Frontier.Ledger.exists_ncard_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Ledger.exists_ncard_le

/--
info: 'Cslib.Circuits.Frontier.eventually_lt_mul_card_of_ledger' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_lt_mul_card_of_ledger

/--
info: 'Cslib.Circuits.Frontier.eventually_lt_mul_card_of_aggregates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_lt_mul_card_of_aggregates

/--
info: 'Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_mul_card_of_ledger' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_mul_card_of_ledger

/--
info: 'Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_mul_card_of_aggregates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_mul_card_of_aggregates

/--
info: 'Cslib.Circuits.Frontier.Multigraph.exists_width_le_of_edgeScore' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Multigraph.exists_width_le_of_edgeScore

/--
info: 'Cslib.Circuits.Frontier.Multigraph.exists_width_le_of_vertexScore' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Multigraph.exists_width_le_of_vertexScore

/--
info: 'Cslib.Circuits.Frontier.Multigraph.core_density' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Multigraph.core_density

/--
info: 'Cslib.Circuits.Frontier.Multigraph.Compression.Saturated.mul_card_external_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Multigraph.Compression.Saturated.mul_card_external_le

/--
info: 'Cslib.Circuits.Frontier.Gaussian.measureReal_straddleEvent_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Gaussian.measureReal_straddleEvent_le

/--
info: 'Cslib.Circuits.Frontier.Gaussian.exists_good_sample' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Gaussian.exists_good_sample

/--
info: 'Cslib.Circuits.Frontier.Gaussian.circuitCoefficient_ge_456' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Gaussian.circuitCoefficient_ge_456

/--
info: 'Cslib.Circuits.Frontier.Gaussian.exists_width_le_gaussianCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Gaussian.exists_width_le_gaussianCoefficient

/--
info: 'Cslib.Circuits.Frontier.Gaussian.cubicLayoutBound_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Gaussian.cubicLayoutBound_gaussian

/--
info: 'Cslib.Circuits.Frontier.layoutBound_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.layoutBound_gaussian

/--
info: 'Cslib.Circuits.Frontier.Gaussian.exists_width_le_vertexCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Gaussian.exists_width_le_vertexCoefficient

/--
info: 'Cslib.Circuits.Frontier.Gaussian.degreeCoefficient_three_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Gaussian.degreeCoefficient_three_le

/--
info: 'Cslib.Circuits.Frontier.layoutBound_degree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.layoutBound_degree

/--
info: 'Cslib.Circuits.Frontier.layoutBound_one_third' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.layoutBound_one_third

/--
info: 'Cslib.Circuits.Frontier.eventually_gaussian_sub_mul_lt_innerSize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_gaussian_sub_mul_lt_innerSize

/--
info: 'Cslib.Circuits.Frontier.eventually_114_div_25_sub_mul_lt_innerSize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_114_div_25_sub_mul_lt_innerSize

/--
info: 'Cslib.Circuits.Frontier.eventually_four_sub_mul_lt_innerSize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_four_sub_mul_lt_innerSize

/--
info: 'Cslib.Circuits.Frontier.Gaussian.exists_ncard_edgeCut_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Gaussian.exists_ncard_edgeCut_le

/--
info: 'Cslib.Circuits.Frontier.circuitLowerBound_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.circuitLowerBound_gaussian

/--
info: 'Cslib.Circuits.Frontier.circuitLowerBound_114_div_25' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.circuitLowerBound_114_div_25

/--
info: 'Cslib.Circuits.Frontier.circuitLowerBound_four' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.circuitLowerBound_four

/--
info: 'Cslib.Circuits.Frontier.averageCaseBound_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.averageCaseBound_gaussian

/--
info: 'Cslib.Circuits.Frontier.averageCaseBound_114_div_25' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.averageCaseBound_114_div_25

/--
info: 'Cslib.Circuits.Frontier.averageCaseBound_four' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.averageCaseBound_four

/--
info: 'Cslib.Circuits.Boolean.Threshold.exists_computes_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Threshold.exists_computes_parity

/--
info: 'Cslib.Circuits.Boolean.Threshold.parity_mem_constDepth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Threshold.parity_mem_constDepth

/--
info: 'Cslib.Circuits.Boolean.TC0_eq_constDepth_threshold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.TC0_eq_constDepth_threshold

/--
info: 'Cslib.Circuits.Frontier.Gaussian.degreeCoefficient_four' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Gaussian.degreeCoefficient_four

/--
info: 'Cslib.Circuits.Frontier.eventually_degreeCoefficient_lt_mul_innerSize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_degreeCoefficient_lt_mul_innerSize

/--
info: 'Cslib.Circuits.Frontier.eventually_seven_div_two_lt_two_mul_innerSize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_seven_div_two_lt_two_mul_innerSize

/--
info: 'Matrix.sq_sum_bilinear_mul_two_pow_rank_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.sq_sum_bilinear_mul_two_pow_rank_le

/--
info: 'Matrix.exists_submatrixRobust' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_submatrixRobust

/--
info: 'Matrix.SubmatrixRobust.le_cutRank_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.SubmatrixRobust.le_cutRank_add

/--
info: 'Matrix.dotProduct_mulVec_self_eq_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.dotProduct_mulVec_self_eq_add

/--
info: 'Cslib.BitString.quadForm_eq_of_submatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.quadForm_eq_of_submatrix

/--
info: 'Cslib.Circuits.Frontier.correlation_eq_two_mul_agreement_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.correlation_eq_two_mul_agreement_sub_one

/--
info: 'Cslib.Circuits.Frontier.sq_signedCount_quadForm_rectangle_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.sq_signedCount_quadForm_rectangle_mul_le

/--
info: 'Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le

/--
info: 'Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le_of_unread' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le_of_unread

/--
info: 'Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le_of_layout' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le_of_layout

/--
info: 'Cslib.Circuits.Frontier.sq_correlation_quadForm_le_of_unread' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.sq_correlation_quadForm_le_of_unread

/--
info: 'Cslib.Circuits.Frontier.sq_correlation_quadForm_le_of_layout' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.sq_correlation_quadForm_le_of_layout

/--
info: 'Cslib.Circuits.Frontier.eventually_abs_correlation_quadForm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_abs_correlation_quadForm_le

/--
info: 'Cslib.Circuits.Frontier.eventually_abs_correlation_quadForm_le_of_isLittleO' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_abs_correlation_quadForm_le_of_isLittleO

/--
info: 'Cslib.Circuits.Frontier.eventually_abs_correlation_quadForm_le_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_abs_correlation_quadForm_le_gaussian

/--
info: 'Cslib.Circuits.Frontier.half_le_cutRank_hardMatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.half_le_cutRank_hardMatrix

/--
info: 'Cslib.Circuits.Frontier.eventually_abs_correlation_hardForm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_abs_correlation_hardForm_le

/--
info: 'Cslib.Circuits.Frontier.exists_eventually_abs_correlation_hardForm_le_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.exists_eventually_abs_correlation_hardForm_le_of_lt

/--
info: 'Cslib.Circuits.Frontier.exists_eventually_abs_correlation_hardForm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.exists_eventually_abs_correlation_hardForm_le

/--
info: 'Cslib.Complexity.SigmaP_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SigmaP_zero

/--
info: 'Cslib.Complexity.PiP_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PiP_zero

/--
info: 'Cslib.Complexity.SigmaP_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SigmaP_one

/--
info: 'Cslib.Complexity.PiP_one_eq_coNP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PiP_one_eq_coNP

/--
info: 'Cslib.Complexity.PiP_eq_preimage_compl_SigmaP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PiP_eq_preimage_compl_SigmaP

/--
info: 'Cslib.Complexity.PH_eq_iUnion_PiP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PH_eq_iUnion_PiP

/--
info: 'Cslib.Complexity.P_subset_PH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.P_subset_PH

/--
info: 'Cslib.Complexity.coNP_subset_PH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.coNP_subset_PH

/--
info: 'Cslib.Complexity.not_alternation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.not_alternation

/--
info: 'Cslib.Complexity.BPP_subset_PP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.BPP_subset_PP

/--
info: 'Cslib.Complexity.mem_NP_iff_exists_SharpP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_NP_iff_exists_SharpP

/--
info: 'Cslib.Complexity.SharpP.exists_le_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SharpP.exists_le_two_pow

/--
info: 'Cslib.Complexity.GapP.neg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.GapP.neg

/--
info: 'Cslib.Complexity.PromiseP_eq_PromiseNP_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PromiseP_eq_PromiseNP_iff

/--
info: 'Cslib.Complexity.mem_PromiseSIZE_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_PromiseSIZE_iff

/--
info: 'Cslib.Complexity.mem_PromisePPoly_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_PromisePPoly_iff

/--
info: 'Cslib.Complexity.PCP_mono_randomness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PCP_mono_randomness

/--
info: 'Cslib.Complexity.PCP_mono_queries' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PCP_mono_queries

/--
info: 'Cslib.Complexity.CookLevin.UNSAT_coNPComplete_of_polyTime' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.UNSAT_coNPComplete_of_polyTime

/--
info: 'Cslib.Complexity.NPHard.compl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.NPHard.compl

/--
info: 'Cslib.Logic.PL.QBF.eval_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.QBF.eval_congr

/--
info: 'Cslib.Logic.PL.QBF.eval_eq_of_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.QBF.eval_eq_of_closed

/--
info: 'Cslib.BitString.card_filter_le_abs_card_filter_sub_half_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.card_filter_le_abs_card_filter_sub_half_le

/--
info: 'Cslib.Circuits.Frontier.exists_rectangleFree_two_pow_le_ncard' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.exists_rectangleFree_two_pow_le_ncard

/--
info: 'Cslib.Circuits.Frontier.exists_rectangleFree_family' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.exists_rectangleFree_family

/--
info: 'Cslib.Circuits.Frontier.exists_rectangleBias' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.exists_rectangleBias

/--
info: 'Cslib.Circuits.Frontier.exists_rectangleBias_family' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.exists_rectangleBias_family

/--
info: 'Cslib.MCSP.mem_iff_exists_circuit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.MCSP.mem_iff_exists_circuit

/--
info: 'Cslib.MCSP.ncard_setOf_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.MCSP.ncard_setOf_mem

/--
info: 'Cslib.GapMCSP.disjoint_yes_no' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.GapMCSP.disjoint_yes_no

/--
info: 'Cslib.MCSP.mem_of_twelve_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.MCSP.mem_of_twelve_mul_le

/--
info: 'Cslib.MCSP.ncard_setOf_mem_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.MCSP.ncard_setOf_mem_le

/--
info: 'Cslib.MCSP.eventually_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.MCSP.eventually_mem

/--
info: 'Cslib.MCSP.eventually_exists_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.MCSP.eventually_exists_not_mem

/--
info: 'Cslib.SuccinctMCSP.eventually_ofFunction_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.SuccinctMCSP.eventually_ofFunction_mem

/--
info: 'Cslib.MCSP.exists_card_le_sixteen_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.MCSP.exists_card_le_sixteen_mul

/--
info: 'Cslib.MCSP.exists_isAntiChecker' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.MCSP.exists_isAntiChecker

/--
info: 'Cslib.MCSP.exists_lt_complexityOn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.MCSP.exists_lt_complexityOn

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.comp

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldl

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapWith' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapWith

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.flatMapWith' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.flatMapWith

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.length

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.range' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.range

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.encoding_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.encoding_length

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_add

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_sub

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_mul

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_le

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_lt

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_pair

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_pow

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_eval

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_to_binary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_to_binary

/--
info: 'Cslib.Complexity.CookLevin.computableTidilyInPolyTime_parameters' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableTidilyInPolyTime_parameters

/--
info: 'Turing.MultiTapeTM.Universal.computableTidilyInO_universal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.Universal.computableTidilyInO_universal

/--
info: 'Turing.MultiTapeTM.Universal.computableTidilyInTimeAndSpace_universal_inPlace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.Universal.computableTidilyInTimeAndSpace_universal_inPlace

/--
info: 'Turing.MultiTapeTM.Universal.stateSpace_desc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.Universal.stateSpace_desc

/--
info: 'Turing.MultiTapeTM.Universal.simSpace_desc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.Universal.simSpace_desc

/--
info: 'Turing.MultiTapeTM.ComputableInTimeAndSpace.comp_space' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableInTimeAndSpace.comp_space

/--
info: 'Turing.MultiTapeTM.ComputableInTimeAndSpace.comp_logSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableInTimeAndSpace.comp_logSpace

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.cons' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.cons

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.listAppend' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.listAppend

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.filterWith' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.filterWith

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.filter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.filter

/--
info: 'Cslib.Logic.PL.Literal.computableTidilyInPolyTime_negate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.Literal.computableTidilyInPolyTime_negate

/--
info: 'Cslib.Logic.PL.Clause.computableTidilyInPolyTime_impLits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.Clause.computableTidilyInPolyTime_impLits

/--
info: 'Cslib.Logic.PL.Clause.computableTidilyInPolyTime_imp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.Clause.computableTidilyInPolyTime_imp

/--
info: 'Cslib.Logic.PL.Clause.computableTidilyInPolyTime_relabel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.Clause.computableTidilyInPolyTime_relabel

/--
info: 'Cslib.Logic.PL.CNF.computableTidilyInPolyTime_relabel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.computableTidilyInPolyTime_relabel

/--
info: 'Cslib.Logic.PL.CNF.computableTidilyInPolyTime_vars' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.computableTidilyInPolyTime_vars

/--
info: 'Cslib.Logic.PL.CNF.computableTidilyInPolyTime_atLeastOne' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.computableTidilyInPolyTime_atLeastOne

/--
info: 'Cslib.Logic.PL.CNF.computableTidilyInPolyTime_atMostOne' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.computableTidilyInPolyTime_atMostOne

/--
info: 'Cslib.Logic.PL.CNF.computableTidilyInPolyTime_exactlyOne' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.computableTidilyInPolyTime_exactlyOne

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.of_enc_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.of_enc_eq

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapConst' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapConst

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.flatMapConst' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.flatMapConst

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_natCast' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_natCast

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_negSucc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_negSucc

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_natCast_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_natCast_sub

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_succ

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_pred' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_pred

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_pos

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_neg

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_toNat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_toNat

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_natAbs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_natAbs

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_equivNat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_equivNat

/--
info: 'Turing.computableTidilyInPolyTime_windowList' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.computableTidilyInPolyTime_windowList

/--
info: 'Cslib.Complexity.CookLevin.computableTidilyInPolyTime_featureIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableTidilyInPolyTime_featureIndex

/--
info: 'Cslib.Complexity.CookLevin.computableTidilyInPolyTime_inPos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableTidilyInPolyTime_inPos

/--
info: 'Cslib.Complexity.CookLevin.computableTidilyInPolyTime_head' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableTidilyInPolyTime_head

/--
info: 'Cslib.Complexity.CookLevin.computableTidilyInPolyTime_cell' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableTidilyInPolyTime_cell

/--
info: 'Cslib.Complexity.CookLevin.computableTidilyInPolyTime_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableTidilyInPolyTime_holds

/--
info: 'Cslib.Complexity.CookLevin.computableTidilyInPolyTime_cert' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableTidilyInPolyTime_cert

/--
info: 'Cslib.Complexity.CookLevin.computableTidilyInPolyTime_index' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableTidilyInPolyTime_index

/--
info: 'Cslib.Complexity.CookLevin.computableTidilyInPolyTime_relabel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableTidilyInPolyTime_relabel

/--
info: 'Cslib.Complexity.CookLevin.computableTidilyInPolyTime_initClauses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableTidilyInPolyTime_initClauses

/--
info: 'Cslib.Complexity.CookLevin.computableTidilyInPolyTime_acceptClauses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableTidilyInPolyTime_acceptClauses

/--
info: 'Cslib.Complexity.CookLevin.computableTidilyInPolyTime_sitClauses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableTidilyInPolyTime_sitClauses

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.cons'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.cons'

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.listAppend'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.listAppend'

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapWithInput' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapWithInput

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.flatMapWithInput' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.flatMapWithInput

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldl_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldl_spec

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterate_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterate_spec

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterateWith_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterateWith_spec

/--
info: 'Cslib.Complexity.CookLevin.computableTidilyInPolyTime_oneHotClauses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableTidilyInPolyTime_oneHotClauses

end ComplexityTests.Axioms
