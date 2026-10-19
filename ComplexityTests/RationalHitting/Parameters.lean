/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Rational.Runtime.Parameters

/-!
# Polynomial-time parameters of the rational hitting list

Concrete parameter values for small `n` and `s`, computed by the kernel and by evaluation, the
certifiable forms of the ambient dimension and the cyclotomic degree, the parameter and dimension
certificates from unary `(n, s)`, their use by `fun_prop` on shifted inputs, and the axioms of the
headline certificates.
-/

namespace ComplexityTests.RationalHitting.Parameters

open Turing MultiTapeTM
open Cslib.Circuits.Rational Cslib.Circuits.Rational.Runtime

/-! ### Concrete values -/

example : threshold 0 0 = 2 := by decide
example : threshold 1 1 = 144 := by decide
example : parameters 0 0 = (2, 1, 4, 2, 385, 8) := by decide
example : parameters 1 1 = (208, 7, 256, 128, 452984833, 32768) := by decide

/-- info: [(2, 1, 4, 2, 385, 8), (208, 7, 256, 128, 452984833, 32768),
 (350, 8, 512, 256, 3623878657, 131072), (16, 4, 32, 16, 196609, 512)] -/
#guard_msgs (whitespace := lax) in
#eval [parameters 0 0, parameters 1 1, parameters 2 1, parameters 1 0]

-- The last component of the parameters is the common dimension of the hitting list.
example (n s : ℕ) : (parameters n s).2.2.2.2.2 = (hittingList n s).dimension := rfl
example : (hittingList 2 1).dimension = 131072 := by decide

/-! ### Certifiable forms -/

example : Parameters.ambientDimension 1 1 = 2 ^ Nat.clog 2 (threshold 1 1 + 1) :=
  ambientDimension_eq 1 1

example (n s : ℕ) : 2 * CyclotomicRing.degree (Parameters.exponent n s) =
    Parameters.ambientDimension n s := by
  rw [degree_eq, Parameters.ambientDimension, pow_succ, Nat.mul_div_cancel _ two_pos, mul_comm]

/-! ### Certificates -/

example : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => parameters p.1 p.2)
    (encPair encUnary encUnary)
    (encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary
      (encPair encUnary encUnary))))) := parameters_polytime

example : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => (hittingList p.1 p.2).dimension)
    (encPair encUnary encUnary) encUnary := hittingList_dimension_polytime

example : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => (hittingList p.1 p.2).dimension)
    (encPair encUnary encUnary) encNat := hittingList_dimension_polytime_binary

-- The registered certificates compose under `fun_prop`, here on the shifted input of the final
-- generator.
example : ComputableTidilyInPolyTime
    (fun p : ℕ × ℕ => Parameters.gridSize (p.1 + 1) (p.2 + 1)) (encPair encUnary encUnary)
    encUnary := by
  fun_prop

example : ComputableTidilyInPolyTime
    (fun p : ℕ × ℕ => Parameters.truncation (p.1 + 1) (p.2 + 1) *
      CyclotomicRing.degree (Parameters.exponent (p.1 + 1) (p.2 + 1)))
    (encPair encUnary encUnary) encUnary := by
  fun_prop

/-! ### Axioms of the headline certificates -/

/--
info: 'Cslib.Circuits.Rational.Runtime.parameters_polytime' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Rational.Runtime.parameters_polytime

/--
info: 'Cslib.Circuits.Rational.Runtime.hittingList_dimension_polytime' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Rational.Runtime.hittingList_dimension_polytime

/--
info: 'Cslib.Circuits.Rational.Runtime.hittingList_dimension_polytime_binary' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Rational.Runtime.hittingList_dimension_polytime_binary

end ComplexityTests.RationalHitting.Parameters
