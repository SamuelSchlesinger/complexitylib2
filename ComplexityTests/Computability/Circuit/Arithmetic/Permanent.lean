/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Arithmetic.Permanent
import Mathlib.Algebra.Field.ZMod

/-!
# Tests for the permanent family, Ryser's formula, VNP membership and projection closure

Concrete checks for `permFamily`, Ryser's inclusion-exclusion formula, `permFamily_mem_VNP`,
block-triangular permanents, multiplicative and rooted permanent projection closure, and
`Formula.isProjection_permanent`, together with `#print axioms` guards.
-/

namespace ComplexityTests.Permanent

open Cslib Cslib.Circuits Cslib.Circuits.Arithmetic MvPolynomial

/-! ### Permanent family and VNP membership -/

example : (permFamily ℚ).IsPFamily := isPFamily_permFamily

example : permFamily ℚ ∈ VNP ℚ := permFamily_mem_VNP

example : permFamily ℤ ∈ VNP ℤ := permFamily_mem_VNP

example : permFamily (ZMod 2) ∈ VNP (ZMod 2) := permFamily_mem_VNP

example : ryserFamily ℚ ∈ VP ℚ := ryserFamily_mem_VP

example : (ryserCircuit ℚ 2).size = 29 := by
  rw [size_ryserCircuit]

/-! ### Ryser's formula and block-triangular permanents -/

example (A : Matrix (Fin 2) (Fin 2) ℤ) :
    A.permanent =
      ∑ S : Finset (Fin 2), (-1 : ℤ) ^ (2 - S.card) * ∏ i : Fin 2, ∑ j ∈ S, A i j :=
  Matrix.permanent_eq_ryser A

example (A : Matrix (Fin 2) (Fin 2) ℚ) (B : Matrix (Fin 2) (Fin 3) ℚ)
    (D : Matrix (Fin 3) (Fin 3) ℚ) :
    (Matrix.fromBlocks A B 0 D).permanent = A.permanent * D.permanent :=
  Matrix.permanent_fromBlocks_zero₂₁ A B D

/-! ### Projection closure and formula universality -/

example : IsProjection (X 0 * X 1 : MvPolynomial (Fin 2) ℚ)
    (genericMatrix ℚ 2).permanent :=
  (isProjection_permanent_X 0).permanent_mul (isProjection_permanent_X 1)

example : IsRootedPermProjection 2
    ((X 0 + X 1) * C 5 : MvPolynomial (Fin 2) ℚ) :=
  ((IsRootedPermProjection.X 0).add (IsRootedPermProjection.X 1)).mul
    (IsRootedPermProjection.C 5)

private def sampleFormula : Formula (arithSignature ℚ) 2 :=
  Formula.gate₂ .mul rfl
    (Formula.gate₂ .add rfl (.input 0) (.input 1))
    (Formula.gate (.const 5) Fin.elim0)

example : sampleFormula.size = 3 := rfl

example : IsProjection (sampleFormula.eval (arithInterpretationWith ℚ C) X)
    (genericMatrix ℚ 4).permanent :=
  sampleFormula.isProjection_permanent

/-! ### Axiom guards -/

/--
info: 'Matrix.permanent_fromBlocks_zero₂₁' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.permanent_fromBlocks_zero₂₁

/--
info: 'Matrix.permanent_fromBlocks_zero₁₂' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.permanent_fromBlocks_zero₁₂

/--
info: 'Matrix.permanent_fromBlocks_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.permanent_fromBlocks_zero

/--
info: 'Matrix.permanent_eq_ryser_bool' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.permanent_eq_ryser_bool

/--
info: 'Matrix.permanent_eq_ryser' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.permanent_eq_ryser

/--
info: 'Cslib.Circuits.Arithmetic.isPFamily_permFamily' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isPFamily_permFamily

/--
info: 'Cslib.Circuits.Arithmetic.ryserFamily_mem_VP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ryserFamily_mem_VP

/--
info: 'Cslib.Circuits.Arithmetic.permFamily_mem_VNP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms permFamily_mem_VNP

/--
info: 'Cslib.Circuits.Arithmetic.IsProjection.permanent_mul' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsProjection.permanent_mul

/--
info: 'Cslib.Circuits.Arithmetic.isProjection_permanent_mono' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isProjection_permanent_mono

/--
info: 'Cslib.Circuits.Arithmetic.isProjection_permanent_finset_prod' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isProjection_permanent_finset_prod

/--
info: 'Cslib.Circuits.Arithmetic.IsRootedPermProjection.add' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsRootedPermProjection.add

/--
info: 'Cslib.Circuits.Arithmetic.IsRootedPermProjection.mul' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsRootedPermProjection.mul

/--
info: 'Cslib.Circuits.Formula.isProjection_permanent' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Formula.isProjection_permanent

end ComplexityTests.Permanent
