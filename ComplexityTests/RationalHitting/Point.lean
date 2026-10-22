/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

import Complexity.Computability.Circuit.Rational.Runtime.Point

/-!
# Regression tests for the per-point normalization and encoding program

Concrete column replacements, normalized matrix entries, matrix words, tuple words, and point
words, checked by the kernel and compiled, agreeing with `ExecutableGenerator.atPoint` and
`encodeTuple` on both singular and nonsingular inputs. Axiom guards cover the headline theorems.
-/

namespace ComplexityTests.RationalHitting.Point

open Cslib.Circuits Cslib.Circuits.Rational
open Turing MultiTapeTM MultiTapeTM.ComputableTidilyInPolyTime

/-! ### Column replacement and Cramer normalization -/

example : cramerRows [[2, 0], [0, 2]] [[4, 2], [0, 6]] 0 1 = [[2, 0], [6, 2]] := by
  decide +kernel

example : cramerRows [[2, 0], [0, 2]] [[4, 2], [0, 6]] 1 0 = [[2, 4], [0, 0]] := by
  decide +kernel

example : matrixEntryWord [[2, 0], [0, 2]] [[4, 2], [0, 6]] 4 0 0 = encodeRat 2 := by
  decide +kernel

example : matrixEntryWord [[2, 0], [0, 2]] [[4, 2], [0, 6]] 4 0 1 = encodeRat 1 := by
  decide +kernel

example : matrixEntryWord [[2, 0], [0, 2]] [[4, 2], [0, 6]] 4 1 0 = encodeRat 0 := by
  decide +kernel

example : matrixEntryWord [[2, 0], [0, 2]] [[4, 2], [0, 6]] 4 1 1 = encodeRat 3 := by
  decide +kernel

example :
    matrixWord [[2, 0], [0, 2]] [[4, 2], [0, 6]] 4 =
      encodeRat 2 ++ encodeRat 1 ++ encodeRat 0 ++ encodeRat 3 := by
  decide +kernel

example :
    pointWordOfTables [[[2, 0], [0, 2]], [[4, 2], [0, 6]]] =
      encodeRat 2 ++ encodeRat 1 ++ encodeRat 0 ++ encodeRat 3 := by
  decide +kernel

example :
    pointWordsOfTables [[[2, 0], [0, 2]], [[4, 2], [0, 6]]] =
      [encodeRat 2 ++ encodeRat 1 ++ encodeRat 0 ++ encodeRat 3] := by
  decide +kernel

-- Singular `U₀` produces `[]` for both `pointWordOfTables` and `pointWordsOfTables`.
example : pointWordOfTables [[[0, 0], [2, 0]], [[4, 2], [0, 6]]] = [] := by
  decide +kernel

example : pointWordsOfTables [[[0, 0], [2, 0]], [[4, 2], [0, 6]]] = [] := by
  decide +kernel

/-! ### Agreement with the executable generator at grid points -/

example : pointWord 0 1 2 1 1 1 1 = [] := by decide +kernel
example : pointWords 0 1 2 1 1 1 1 = [] := by decide +kernel

example :
    pointWord 0 1 (CyclotomicRing.dimension 0) (CyclotomicRing.degree 0) 1 1 1 =
      (ExecutableGenerator.atPoint 0 1 0 ![1, 1, 1]).elim [] encodeTuple :=
  pointWord_eq 0 1 0 ![1, 1, 1]

example :
    pointWords 1 2 (CyclotomicRing.dimension 1) (CyclotomicRing.degree 1) 1 2 3 =
      ((ExecutableGenerator.atPoint 1 2 1 ![1, 2, 3]).map encodeTuple).toList :=
  pointWords_eq 1 2 1 ![1, 2, 3]

/-- info: true -/
#guard_msgs in
#eval pointWord 1 2 4 2 1 2 3 ==
  (ExecutableGenerator.atPoint 1 2 1 ![1, 2, 3]).elim [] encodeTuple

/-! ### Polynomial-time certificates -/

example :
    ComputableTidilyInPolyTime pointWordOfTables
      (encList (encList (encList encIntBin))) encBits :=
  pointWordOfTables_polytime

example :
    ComputableTidilyInPolyTime pointWordsOfTables
      (encList (encList (encList encIntBin))) (encList encBits) :=
  pointWordsOfTables_polytime

example :
    ComputableTidilyInPolyTime
      (fun q : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ =>
        pointWord q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2)
      (encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary
        (encPair encUnary (encPair encUnary encUnary))))))
      encBits :=
  pointWord_polytime

/-! ### Axioms -/

/--
info: 'Cslib.Circuits.Rational.cramerRows_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cramerRows_eq

/--
info: 'Cslib.Circuits.Rational.matrixEntryWord_eq' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms matrixEntryWord_eq

/--
info: 'Cslib.Circuits.Rational.matrixWord_eq' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms matrixWord_eq

/--
info: 'Cslib.Circuits.Rational.tupleWord_eq' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tupleWord_eq

/--
info: 'Cslib.Circuits.Rational.pointWord_eq' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pointWord_eq

/--
info: 'Cslib.Circuits.Rational.pointWords_eq' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pointWords_eq

/--
info: 'Cslib.Circuits.Rational.pointWordOfTables_polytime' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pointWordOfTables_polytime

/--
info: 'Cslib.Circuits.Rational.pointWord_polytime' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pointWord_polytime

end ComplexityTests.RationalHitting.Point
