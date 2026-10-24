/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Mathlib.Algebra.BigOperators.Fin
import Complexity.Foundations.BooleanAnalysis.HadamardRectangles
import Complexity.Computability.DecisionTree.InnerProduct
import Mathlib.Data.Fintype.Powerset

/-!
Boundary and nonvacuity clients for monochromatic inner-product rectangles and tree lower bounds.
-/

open Cslib Cslib.BitString Matrix

namespace ThresholdInnerProduct

-- Empty sides satisfy the bound for either color and arbitrary coordinate type.
example {ι : Type*} [Fintype ι] (B : Finset (ι → Bool)) (b : Bool) :
    (∅ : Finset (ι → Bool)).card * B.card ≤ 2 ^ Fintype.card ι :=
  card_mul_le_two_pow_of_hadamardCode_eq ∅ B b (by simp)

example {ι : Type*} [Fintype ι] (A : Finset (ι → Bool)) (b : Bool) :
    A.card * (∅ : Finset (ι → Bool)).card ≤ 2 ^ Fintype.card ι :=
  card_mul_le_two_pow_of_hadamardCode_eq A ∅ b (by simp)

-- At dimension zero the entire product is a false rectangle of area one.
example (x y : Fin 0 → Bool) : hadamardCode x y = false := by
  simp [dotProduct, Bool.zero_eq_false]

example : (Finset.univ : Finset (Fin 0 → Bool)).card *
    (Finset.univ : Finset (Fin 0 → Bool)).card = 1 := by decide

example : (Finset.univ : Finset (Fin 0 → Bool)).card *
    (Finset.univ : Finset (Fin 0 → Bool)).card ≤ 2 ^ 0 :=
  card_mul_le_two_pow_of_hadamardCode_eq
    (Finset.univ : Finset (Fin 0 → Bool)) Finset.univ false
    (fun _ _ _ _ => by simp [dotProduct, Bool.zero_eq_false])

-- The zero vector times the full cube attains the rectangle bound at every dimension.
example (n : ℕ) (y : Fin n → Bool) : hadamardCode 0 y = false := by
  simp [Bool.zero_eq_false]

example (n : ℕ) : ({0} : Finset (Fin n → Bool)).card *
    (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by simp

-- A nonempty true rectangle exercises the other color.
example : ∀ x ∈ ({fun _ : Fin 1 => true} : Finset (Fin 1 → Bool)),
    ∀ y ∈ ({fun _ : Fin 1 => true} : Finset (Fin 1 → Bool)),
      hadamardCode x y = true := by decide

example : ({fun _ : Fin 1 => true} : Finset (Fin 1 → Bool)).card *
    ({fun _ : Fin 1 => true} : Finset (Fin 1 → Bool)).card ≤ 2 ^ 1 :=
  card_mul_le_two_pow_of_hadamardCode_eq _ _ true (by decide)

-- All rectangles and both colors on the two-coordinate cube: 16*16*2 = 512 cases.
example (A B : Finset (Fin 2 → Bool)) (b : Bool) :
    (∀ x ∈ A, ∀ y ∈ B, hadamardCode x y = b) → A.card * B.card ≤ 4 := by
  revert A B b
  decide

-- Monochromaticity is essential; the entire one-coordinate product has area four, not two.
example : ¬ ∃ b, ∀ x : Fin 1 → Bool, ∀ y : Fin 1 → Bool, hadamardCode x y = b := by
  decide

private def andQuery : SeparableComparison (Fin 1 → Bool) (Fin 1 → Bool) :=
  ⟨fun x => (x 0).toNat, fun y => (y 0).toNat, 2⟩

private def andTree : DecisionTree (SeparableComparison (Fin 1 → Bool) (Fin 1 → Bool)) Bool :=
  .node andQuery (.leaf false) (.leaf true)

private theorem andTree_computes (x y : Fin 1 → Bool) :
    andTree.eval (fun q => q.eval x y) = hadamardCode x y := by
  cases hx : x 0 <;> cases hy : y 0 <;>
    norm_num [andTree, andQuery, DecisionTree.eval, SeparableComparison.eval,
      hadamardCode_apply, dotProduct, Bool.mul_eq_and, hx, hy]

example : andTree.leafCount = 2 := rfl

example : 2 ≤ andTree.leafCount ^ 2 := by
  simpa using andTree.two_pow_le_leafCount_sq_of_hadamardCode andTree_computes

private def bitAndQuery (i : Fin 2) :
    SeparableComparison (Fin 2 → Bool) (Fin 2 → Bool) :=
  ⟨fun x => (x i).toNat, fun y => (y i).toNat, 2⟩

private def twoBitTree :
    DecisionTree (SeparableComparison (Fin 2 → Bool) (Fin 2 → Bool)) Bool :=
  .node (bitAndQuery 0) (.node (bitAndQuery 1) (.leaf false) (.leaf true))
    (.node (bitAndQuery 1) (.leaf true) (.leaf false))

private theorem twoBitTree_computes (x y : Fin 2 → Bool) :
    twoBitTree.eval (fun q => q.eval x y) = hadamardCode x y := by
  cases hx0 : x 0 <;> cases hx1 : x 1 <;> cases hy0 : y 0 <;> cases hy1 : y 1 <;>
    norm_num [twoBitTree, bitAndQuery, DecisionTree.eval, SeparableComparison.eval,
      hadamardCode_apply, dotProduct, Fin.sum_univ_two, Bool.mul_eq_and, Bool.add_eq_xor,
      hx0, hx1, hy0, hy1]

example : 4 ≤ twoBitTree.leafCount ^ 2 := by
  simpa using twoBitTree.two_pow_le_leafCount_sq_of_hadamardCode twoBitTree_computes

-- A noncomputing one-leaf tree cannot satisfy the two-coordinate specification.
example : ¬ ∀ x y : Fin 2 → Bool,
    (DecisionTree.leaf false :
      DecisionTree (SeparableComparison (Fin 2 → Bool) (Fin 2 → Bool)) Bool).eval
      (fun q => q.eval x y) = hadamardCode x y := by
  intro h
  have := DecisionTree.two_pow_le_leafCount_sq_of_hadamardCode
    (DecisionTree.leaf false :
      DecisionTree (SeparableComparison (Fin 2 → Bool) (Fin 2 → Bool)) Bool) h
  norm_num [DecisionTree.leafCount] at this

-- A zero-coordinate leaf is a genuine computing witness, so no positivity assumption is hidden.
example : 1 ≤ (DecisionTree.leaf false :
    DecisionTree (SeparableComparison (Fin 0 → Bool) (Fin 0 → Bool)) Bool).leafCount ^ 2 :=
  DecisionTree.two_pow_le_leafCount_sq_of_hadamardCode
    (DecisionTree.leaf false :
      DecisionTree (SeparableComparison (Fin 0 → Bool) (Fin 0 → Bool)) Bool)
    (fun _ _ => by simp [dotProduct, Bool.zero_eq_false])

example {n : ℕ}
    (t : DecisionTree (SeparableComparison (Fin n → Bool) (Fin n → Bool)) Bool)
    (ht : ∀ x y, t.eval (fun q => q.eval x y) = hadamardCode x y) :
    2 ^ n ≤ t.leafCount ^ 2 := by
  simpa using t.two_pow_le_leafCount_sq_of_hadamardCode ht

-- Decision-list, node-count, rank, and energy bounds on `andTree` and `twoBitTree`.
private theorem andTree_isDecisionList : andTree.IsDecisionList :=
  Or.inl ⟨rfl, trivial⟩

example : 2 ≤ (andTree.nodeCount + 1) ^ 2 := by
  simpa using andTree.two_pow_le_nodeCount_add_one_sq_of_hadamardCode andTree_computes

example : 2 ≤ (andTree.depth + 1) ^ 2 := by
  simpa using
    andTree.two_pow_le_depth_add_one_sq_of_isDecisionList_hadamardCode
      andTree_isDecisionList andTree_computes

example : 4 ≤ (∑ j ∈ Finset.range (twoBitTree.rank + 1), twoBitTree.depth.choose j) ^ 2 := by
  simpa using twoBitTree.two_pow_le_sum_choose_rank_sq_of_hadamardCode twoBitTree_computes

example : (1 : ℝ) ≤
    twoBitTree.rank * Real.logb 2 (Real.exp 1 * twoBitTree.depth / twoBitTree.rank) := by
  simpa using twoBitTree.le_rank_mul_logb_depth_of_hadamardCode twoBitTree_computes

example : twoBitTree.rank / Real.exp 1 * (2 : ℝ) ^ ((2 : ℝ) / (2 * twoBitTree.rank)) ≤
    twoBitTree.depth := by
  simpa using twoBitTree.rank_mul_rpow_le_depth_of_hadamardCode twoBitTree_computes

example : 4 ≤ (∑ j ∈ Finset.range (twoBitTree.energy + 1), twoBitTree.depth.choose j) ^ 2 := by
  simpa using twoBitTree.two_pow_le_sum_choose_energy_sq_of_hadamardCode twoBitTree_computes

example : (1 : ℝ) ≤
    twoBitTree.energy * Real.logb 2 (Real.exp 1 * twoBitTree.depth / twoBitTree.energy) := by
  simpa using twoBitTree.le_energy_mul_logb_depth_of_hadamardCode twoBitTree_computes

example : twoBitTree.energy / Real.exp 1 * (2 : ℝ) ^ ((2 : ℝ) / (2 * twoBitTree.energy)) ≤
    twoBitTree.depth := by
  simpa using twoBitTree.energy_mul_rpow_le_depth_of_hadamardCode twoBitTree_computes

-- Bi-monotone comparison tree computing 1-bit inner product via `BiMonotoneComparison.ofMin`.
private noncomputable def andBiQuery :
    BiMonotoneComparison (Fin 1 → Bool) (Fin 1 → Bool) :=
  BiMonotoneComparison.ofMin (fun x => (x 0).toNat) (fun y => (y 0).toNat) 1

private noncomputable def andBiTree :
    DecisionTree (BiMonotoneComparison (Fin 1 → Bool) (Fin 1 → Bool)) Bool :=
  .node andBiQuery (.leaf false) (.leaf true)

private theorem andBiTree_computes (x y : Fin 1 → Bool) :
    andBiTree.eval (fun q => q.eval x y) = hadamardCode x y := by
  cases hx : x 0 <;> cases hy : y 0 <;>
    norm_num [andBiTree, andBiQuery, DecisionTree.eval, BiMonotoneComparison.eval_ofMin,
      hadamardCode_apply, dotProduct, Bool.mul_eq_and, hx, hy]

example : 2 ≤ andBiTree.leafCount ^ 2 := by
  simpa using andBiTree.two_pow_le_leafCount_sq_of_biMonotone_hadamardCode andBiTree_computes

/--
info: 'Cslib.DecisionTree.two_pow_le_leafCount_sq_of_biMonotone_hadamardCode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DecisionTree.two_pow_le_leafCount_sq_of_biMonotone_hadamardCode

/--
info: 'Cslib.DecisionTree.two_pow_le_nodeCount_add_one_sq_of_hadamardCode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DecisionTree.two_pow_le_nodeCount_add_one_sq_of_hadamardCode

/--
info: 'Cslib.DecisionTree.two_pow_le_depth_add_one_sq_of_isDecisionList_hadamardCode' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DecisionTree.two_pow_le_depth_add_one_sq_of_isDecisionList_hadamardCode

/--
info: 'Cslib.DecisionTree.two_pow_le_sum_choose_rank_sq_of_hadamardCode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DecisionTree.two_pow_le_sum_choose_rank_sq_of_hadamardCode

/--
info: 'Cslib.DecisionTree.le_rank_mul_logb_depth_of_hadamardCode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DecisionTree.le_rank_mul_logb_depth_of_hadamardCode

/--
info: 'Cslib.DecisionTree.rank_mul_rpow_le_depth_of_hadamardCode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DecisionTree.rank_mul_rpow_le_depth_of_hadamardCode

/--
info: 'Cslib.DecisionTree.two_pow_le_sum_choose_energy_sq_of_hadamardCode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DecisionTree.two_pow_le_sum_choose_energy_sq_of_hadamardCode

/--
info: 'Cslib.DecisionTree.le_energy_mul_logb_depth_of_hadamardCode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DecisionTree.le_energy_mul_logb_depth_of_hadamardCode

/--
info: 'Cslib.DecisionTree.energy_mul_rpow_le_depth_of_hadamardCode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DecisionTree.energy_mul_rpow_le_depth_of_hadamardCode

end ThresholdInnerProduct
