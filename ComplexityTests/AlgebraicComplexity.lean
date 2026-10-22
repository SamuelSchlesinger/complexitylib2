/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Arithmetic.Determinant
import Complexity.Computability.Circuit.Arithmetic.VNP
import Complexity.Foundations.Data.Matrix.Permanent
import Mathlib.Algebra.Field.ZMod

/-!
# Algebraic complexity: VP, VNP and the determinant

Circuits compute formal polynomials: over `ZMod 2` a squaring circuit computes `X ^ 2`, which agrees
with `X` as a function but not as a polynomial. The product monomial is a projection of the
`2 × 2` determinant, and the products of `n` variables form a p-projection of the determinant
family, so they are in `VP` by closure. Repeated squaring has small circuits but is not in `VP`.
The determinant circuits evaluate concrete determinants, a Boolean sum is computed, and the
determinant family is in `VNP`. The permanent expands along row 0 and its generic family is a
p-family. Named axiom guards cover the headline theorems.
-/

namespace ComplexityTests.AlgebraicComplexity

open Cslib Cslib.Circuits Cslib.Circuits.Arithmetic MvPolynomial

/-! ### Formal polynomials, not functions -/

private def square : Circuit (arithSignature (ZMod 2)) 1 1 :=
  Circuit.oneGate .mul fun _ => 0

example : square.polynomial 0 = X 0 ^ 2 := by
  simp [square, Circuit.polynomial, Circuit.eval_oneGate, sq]

-- As a function on `ZMod 2`, the square is the identity.
example (x : Fin 1 → ZMod 2) : square.eval (arithInterpretation (ZMod 2)) x 0 = x 0 := by
  simp only [square, Circuit.eval_oneGate, arithInterpretation, arithInterpretationWith_mul]
  generalize x 0 = a
  fin_cases a <;> rfl

-- As polynomials, `X ^ 2` and `X` differ.
example : (X 0 ^ 2 : MvPolynomial (Fin 1) (ZMod 2)) ≠ X 0 := fun h => by
  simpa [totalDegree_X_pow, totalDegree_X] using congrArg totalDegree h

-- Evaluation of the computed polynomial is evaluation of the circuit.
example (x : Fin 1 → ZMod 2) :
    aeval x (square.polynomial 0) = square.eval (arithInterpretation (ZMod 2)) x 0 :=
  square.aeval_polynomial x 0

/-! ### Projections -/

example : (genericMatrix ℚ 2).det = X 0 * X 3 - X 1 * X 2 := by
  rw [Matrix.det_fin_two]
  rfl

/-- The product of two variables is a projection of the `2 × 2` determinant. -/
example : IsProjection (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) (genericMatrix ℚ 2).det := by
  refine ⟨![.inl 0, .inr 0, .inr 0, .inl 1], ?_⟩
  rw [Matrix.det_fin_two]
  simp [genericMatrix, finProdFinEquiv]

/-- The products of `n` variables. -/
noncomputable def productFamily : PolynomialFamily ℚ where
  vars n := n
  poly _ := ∏ i, X i

/-- The product of `n` variables is the determinant of the diagonal matrix of variables, a
projection of the generic determinant. -/
theorem productFamily_isPProjection_detFamily : productFamily.IsPProjection (detFamily ℚ) := by
  refine ⟨fun n => n, PolynomiallyBounded.id, fun n => ?_⟩
  let ρ : Fin (n * n) → Fin n ⊕ ℚ := fun k =>
    if (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm k).2 then .inl (finProdFinEquiv.symm k).1
    else .inr 0
  refine ⟨ρ, ?_⟩
  change projection ρ (genericMatrix ℚ n).det = ∏ i : Fin n, X i
  rw [AlgHom.map_det, ← Matrix.det_diagonal]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [genericMatrix, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    projection_X, ρ, Equiv.symm_apply_apply, Matrix.diagonal_apply]
  split_ifs with h <;> simp [h]

example : productFamily ∈ VP ℚ :=
  VP.of_isPProjection detFamily_mem_VP productFamily_isPProjection_detFamily
    PolynomiallyBounded.id

/-! ### Degree bounds are part of VP -/

example (n : ℕ) : ∃ c : Circuit (arithSignature ℚ) 1 1,
    c.polynomial 0 = X 0 ^ 2 ^ n ∧ c.size ≤ n :=
  exists_circuit_pow_two_pow n

example : powTwoPowFamily ℚ ∉ VP ℚ := powTwoPowFamily_not_mem_VP

example : powTwoPowFamily (ZMod 2) ∉ VP (ZMod 2) := powTwoPowFamily_not_mem_VP

/-! ### The determinant -/

-- The determinant circuits evaluate determinants over the coefficient ring itself.
example : ∃ c : Circuit (arithSignature ℚ) (2 * 2) 1, c.size ≤ 52 ∧
    c.eval (arithInterpretation ℚ) ![2, 3, 5, 7] 0 = -1 := by
  obtain ⟨c, hsize, hc⟩ := exists_circuit_det_eval (K := ℚ) 2
  have h := hc (R := ℚ) !![2, 3; 5, 7]
  have hx : (fun k : Fin (2 * 2) => (!![2, 3; 5, 7] : Matrix (Fin 2) (Fin 2) ℚ)
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) = ![2, 3, 5, 7] := by
    funext k
    fin_cases k <;> rfl
  rw [hx, Matrix.det_fin_two_of, Algebra.algebraMap_self, RingHom.coe_id] at h
  exact ⟨c, hsize.trans (by norm_num), h.trans (by norm_num)⟩

-- The same holds in characteristic two and in polynomial rings.
example : detFamily (ZMod 2) ∈ VP (ZMod 2) := detFamily_mem_VP

example : detFamily (MvPolynomial (Fin 3) ℤ) ∈ VP (MvPolynomial (Fin 3) ℤ) := detFamily_mem_VP

/-! ### The permanent -/

example (A : Matrix (Fin 2) (Fin 2) ℤ) :
    A.permanent = ∑ j : Fin 2, A 0 j * (A.submatrix Fin.succ j.succAbove).permanent :=
  Matrix.permanent_succ_row_zero A

example : (permFamily ℚ).IsPFamily := isPFamily_permFamily

/-! ### VNP -/

example : detFamily ℚ ∈ VNP ℚ := VP_subset_VNP detFamily_mem_VP

/-- Summing `X₀ * e` over `e ∈ {0, 1}` gives `X₀`. -/
example : booleanSum 1 (X 0 * X 1 : MvPolynomial (Fin (1 + 1)) ℚ) = X 0 := by
  rw [booleanSum, ← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
  simp [booleanAssignment, Fin.append, Fin.addCases]

example : productFamily ∈ VNP ℚ :=
  VNP.of_isPProjection (VP_subset_VNP detFamily_mem_VP) productFamily_isPProjection_detFamily
    PolynomiallyBounded.id

/-! ### Axiom guards -/

/--
info: 'Cslib.Circuits.Arithmetic.detFamily_mem_VP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms detFamily_mem_VP

/--
info: 'Cslib.Circuits.Arithmetic.exists_circuit_det' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_circuit_det

/--
info: 'Cslib.Circuits.Arithmetic.exists_circuit_det_eval' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_circuit_det_eval

/--
info: 'Cslib.Circuits.Arithmetic.det_eq_birdDetSpec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms det_eq_birdDetSpec

/--
info: 'Cslib.Circuits.Arithmetic.VP.of_isPProjection' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VP.of_isPProjection

/--
info: 'Cslib.Circuits.Arithmetic.VNP.of_isPProjection' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VNP.of_isPProjection

/--
info: 'Cslib.Circuits.Arithmetic.VP_subset_VNP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VP_subset_VNP

/--
info: 'Cslib.Circuits.Arithmetic.IsVNPComplete.mem_VP_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsVNPComplete.mem_VP_iff

/--
info: 'Cslib.Circuits.Arithmetic.powTwoPowFamily_not_mem_VP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms powTwoPowFamily_not_mem_VP

/--
info: 'Matrix.permanent_succ_column_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.permanent_succ_column_zero

/--
info: 'Matrix.permanent_succ_row_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.permanent_succ_row_zero

end ComplexityTests.AlgebraicComplexity
