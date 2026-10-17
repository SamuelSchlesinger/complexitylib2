/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Monotone.Basic
public import Mathlib.Data.Set.Basic

/-!
# Monotone circuits constructing sets

The existing monotone signature acts on sets by intersection and union. Its constants denote
the empty and full sets. Native `Program` and `Circuit` supply the syntax, evaluation and costs;
the interpretation does not require decidable membership or a finite ambient type.

## Main definitions

* `Cslib.Circuits.Monotone.setInterpretation`: sets as an interpretation of the monotone basis.

## References

* Adapted from `Basis/AndOr.lean` in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic],
  extending its binary AND/OR interpretation to the existing basis with constants.
-/

@[expose] public section

namespace Cslib.Circuits.Monotone

/-- Interpret conjunction and disjunction as intersection and union, with empty/full constants. -/
def setInterpretation (U : Type*) : Interpretation signature (Set U)
  | .const false, _ => ∅
  | .const true, _ => Set.univ
  | .and, args => args 0 ∩ args 1
  | .or, args => args 0 ∪ args 1

@[simp] theorem setInterpretation_false (U : Type*) (args : Fin 0 → Set U) :
    setInterpretation U (.const false) args = ∅ := rfl

@[simp] theorem setInterpretation_true (U : Type*) (args : Fin 0 → Set U) :
    setInterpretation U (.const true) args = Set.univ := rfl

@[simp] theorem setInterpretation_and {U : Type*} (args : Fin 2 → Set U) :
    setInterpretation U .and args = args 0 ∩ args 1 := rfl

@[simp] theorem setInterpretation_or {U : Type*} (args : Fin 2 → Set U) :
    setInterpretation U .or args = args 0 ∪ args 1 := rfl

end Cslib.Circuits.Monotone
