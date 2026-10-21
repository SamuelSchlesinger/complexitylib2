/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.CodeComposition

/-! Tests of shared-input code append, including original input references, shifted gate
references, repeated outputs, zero-input constants and empty circuits. -/

namespace ComplexityTests.CodeComposition

open Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM ComputableTidilyInPolyTime

private def left : List (Op × List ℕ) × List ℕ := ([(.not, [0])], [2])

private def right : List (Op × List ℕ) × List ℕ :=
  ([(.not, [1]), (.and, [0, 2])], [3, 1, 3])

-- Original inputs 0 and 1 retain their references; right's gate 2 shifts to gate 3.
example : appendCode 2 left right =
    ([(.not, [0]), (.not, [1]), (.and, [0, 3])], [2, 4, 1, 4]) := by decide

example : (appendCode 2 left right).2.map
    (evalOutput [true, false] (appendCode 2 left right).1) = [false, true, false, true] := by decide

-- Two zero-input constant circuits still have disjoint gate namespaces.
example : appendCode 0 ([(.const true, [])], [0]) ([(.const false, [])], [0]) =
    ([(.const true, []), (.const false, [])], [0, 1]) := by decide

-- A zero-gate projection circuit can be appended without changing live inputs.
example : appendCode 2 ([], [1, 0]) right =
    ([(.not, [1]), (.and, [0, 2])], [1, 0, 3, 1, 3]) := by decide

example : appendCode 0 ([], []) ([], []) = ([], []) := by decide

/-- The constructor handles arbitrary raw codes and a binary input count uniformly. -/
theorem constructor_polynomialTime :
    ComputableTidilyInPolyTime
      (fun p : ℕ × (List (Op × List ℕ) × List ℕ) × (List (Op × List ℕ) × List ℕ) =>
        appendCode p.1 p.2.1 p.2.2)
      (encPair encNat (encPair encCode encCode)) encCode :=
  computableTidilyInPolyTime_appendCode (fst _ _) (snd _ _).fst' (snd _ _).snd'

/-- The typed correspondence and resource theorem apply at zero dimensions. -/
example (c d : Circuit signature 0 0) :
    appendCode 0 c.code d.code = (c.append d).code ∧
      (appendCode 0 c.code d.code).1.length = c.size + d.size :=
  ⟨appendCode_code c d, by
    rw [length_appendCode, Circuit.length_code_fst, Circuit.length_code_fst]⟩

-- Every block has one gate, including repeated copies and different output lists.
example : bundleCode 2 1 [left, ([(.and, [0, 1])], [0, 2]), left] =
    ([(.not, [0]), (.and, [0, 1]), (.not, [0])], [2, 0, 3, 4]) := by decide

example : bundleCode 2 1 [left, ([(.and, [0, 1])], [0, 2]), left] =
    [left, ([(.and, [0, 1])], [0, 2]), left].foldl (appendCode 2) ([], []) := by
  apply bundleCode_eq_foldl_appendCode
  decide

example : bundleCode 0 0 [([], []), ([], [])] = ([], []) := by decide

/-- The bundler has no block-size or well-formedness promise in its runtime certificate. -/
theorem bundler_polynomialTime :
    ComputableTidilyInPolyTime
      (fun p : (ℕ × ℕ) × List (List (Op × List ℕ) × List ℕ) =>
        bundleCode p.1.1 p.1.2 p.2)
      (encPair (encPair encNat encNat) (encList encCode)) encCode :=
  computableTidilyInPolyTime_bundleCode (fst _ _).fst' (fst _ _).snd' (snd _ _)

/-- The typed family corollary includes an empty output family at zero input dimension. -/
example (cs : Fin 0 → Circuit signature 0 1) :
    ∃ c : Circuit signature 0 0,
      bundleCode 0 0 (List.ofFn (fun j => (cs j).code)) = c.code ∧
        ∀ x j, c.eval interpretation x j = (cs j).eval interpretation x 0 :=
  exists_circuit_bundleCode cs 0 (fun j => j.elim0)

/-- info: 'Cslib.Circuits.Program.code_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Circuits.Program.code_append

/-- info: 'Cslib.Circuits.Boolean.appendCode_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Circuits.Boolean.appendCode_code

/-- info: 'ComplexityTests.CodeComposition.constructor_polynomialTime' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms constructor_polynomialTime

/-- info: 'Cslib.Circuits.Boolean.bundleCode_eq_foldl_appendCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Circuits.Boolean.bundleCode_eq_foldl_appendCode

/-- info: 'ComplexityTests.CodeComposition.bundler_polynomialTime' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bundler_polynomialTime

/-- info: 'Cslib.Circuits.Boolean.exists_circuit_bundleCode' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Circuits.Boolean.exists_circuit_bundleCode

end ComplexityTests.CodeComposition
