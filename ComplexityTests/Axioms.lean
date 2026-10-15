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
info: 'Turing.MultiTapeTM.HaltsAt.runFrom_shadow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.HaltsAt.runFrom_shadow

/--
info: 'Turing.MultiTapeTM.runFrom_clearShadowed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.runFrom_clearShadowed

/--
info: 'Turing.MultiTapeTM.spaceUsed_seq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.spaceUsed_seq_le

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
info: 'Cslib.Circuits.Boolean.Unbounded.exists_extension_shallow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Unbounded.exists_extension_shallow

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
info: 'Cslib.Circuits.Boolean.sum_fourierCoeff_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.sum_fourierCoeff_sq_le

/--
info: 'Cslib.Logic.PL.CNF.sum_two_rpow_card_isolated_div_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.sum_two_rpow_card_isolated_div_le

end ComplexityTests.Axioms
