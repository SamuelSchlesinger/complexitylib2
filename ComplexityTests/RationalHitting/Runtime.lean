/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

import Complexity.Computability.Circuit.Rational.Runtime

/-!
# Regression tests for the polynomial-time rational hitting-list generator

Concrete checks for `gridPointWords`, `outputWord`, `inputWord`, `parseInput`, and
`hittingGenerator`, agreement with `ExecutableGenerator.output` and
`encodeOutput (hittingList n s)`, polynomial-time certificates, end-to-end hitting specification,
and axiom guards.
-/

namespace ComplexityTests.RationalHitting.Runtime

open Cslib.Circuits Cslib.Circuits.Rational
open Turing MultiTapeTM MultiTapeTM.ComputableTidilyInPolyTime

/-! ### Unary input format and parser -/

example : inputWord 2 3 = [true, true, false, true, true, true] := by decide +kernel
example : (inputWord 2 3).length = 6 := by decide +kernel
example : parseInput (inputWord 2 3) = some (2, 3) := by decide +kernel
example : parseInput (inputWord 1 1) = some (1, 1) := by decide +kernel

-- Malformed inputs (missing separator, `n = 0`, `s = 0`, or extra `false` bits) parse to `none`.
example : parseInput [] = none := by decide +kernel
example : parseInput [true, true] = none := by decide +kernel
example : parseInput (inputWord 0 2) = none := by decide +kernel
example : parseInput (inputWord 2 0) = none := by decide +kernel
example : parseInput [true, false, true, false, true] = none := by decide +kernel

example : hittingGenerator [] = [] := by decide +kernel
example : hittingGenerator (inputWord 0 2) = [] := by decide +kernel
example : hittingGenerator (inputWord 2 0) = [] := by decide +kernel
example : hittingGenerator [true, false, true, false, true] = [] := by decide +kernel

/-! ### Grid enumeration and output encoding on small parameters -/

example : gridPointWords 0 1 2 1 1 = [] := by decide +kernel
example : outputWord 0 1 2 1 1 = encodeNat 2 ++ encodeNat 0 := by decide +kernel

example :
    outputWord 0 1 (CyclotomicRing.dimension 0) (CyclotomicRing.degree 0) 1 =
      encodeOutput (ExecutableGenerator.output 0 1 0 1) :=
  outputWord_eq 0 1 0 1

/-- info: true -/
#guard_msgs in
#eval outputWord 1 2 4 2 1 == encodeOutput (ExecutableGenerator.output 1 2 1 1)

example (n s : ℕ) : hittingListWord n s = encodeOutput (hittingList n s) :=
  hittingListWord_eq n s

example {n s : ℕ} (hn : 1 ≤ n) (hs : 1 ≤ s) :
    hittingGenerator (inputWord n s) = encodeOutput (hittingList n s) :=
  hittingGenerator_inputWord hn hs

/-! ### Polynomial-time certificates and end-to-end specification -/

example :
    ComputableTidilyInPolyTime parseInput encBits (encOption (encPair encUnary encUnary)) :=
  parseInput_polytime

example :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ => encodeOutput (hittingList p.1 p.2))
      (encPair encUnary encUnary) encBits :=
  hittingList_polytime

example : ComputableTidilyInPolyTime hittingGenerator encBits encBits :=
  hittingGenerator_polytime

example :
    ComputableTidilyInPolyTime hittingGenerator encBits encBits ∧
      ∀ n s : ℕ, 1 ≤ n → 1 ≤ s →
        hittingGenerator (inputWord n s) = encodeOutput (hittingList n s) ∧
          (hittingList n s).dimension ≤ 256 * (n + s + 1) ^ 10 ∧
          (encodeOutput (hittingList n s)).length ≤
            PolynomialBounds.outputConstant * (n + s + 1) ^ 104 ∧
          Hits s (hittingList n s) :=
  hittingGenerator_spec

/-! ### Axioms -/

/--
info: 'Cslib.Circuits.Rational.gridPointWords_eq' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gridPointWords_eq

/--
info: 'Cslib.Circuits.Rational.outputWord_eq' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms outputWord_eq

/--
info: 'Cslib.Circuits.Rational.hittingListWord_eq' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hittingListWord_eq

/--
info: 'Cslib.Circuits.Rational.parseInput_eq_some_iff' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms parseInput_eq_some_iff

/--
info: 'Cslib.Circuits.Rational.hittingGenerator_inputWord' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hittingGenerator_inputWord

/--
info: 'Cslib.Circuits.Rational.hittingGenerator_eq_nil' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hittingGenerator_eq_nil

/--
info: 'Cslib.Circuits.Rational.hittingList_polytime' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hittingList_polytime

/--
info: 'Cslib.Circuits.Rational.hittingGenerator_polytime' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hittingGenerator_polytime

/--
info: 'Cslib.Circuits.Rational.hittingGenerator_spec' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hittingGenerator_spec

end ComplexityTests.RationalHitting.Runtime
