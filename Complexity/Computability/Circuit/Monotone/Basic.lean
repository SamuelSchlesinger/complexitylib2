/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# Monotone circuits

The monotone basis has the Boolean constants, binary conjunction and binary disjunction: the De
Morgan basis (`Cslib.Circuits.Boolean.signature`) without negation. Each of its operations is
monotone (`interpretation_mono`), and so is every function computed by a monotone circuit.

## Main definitions

* `Cslib.Circuits.Monotone.signature`, `Cslib.Circuits.Monotone.interpretation`.

## Main results

* `Cslib.Circuits.Monotone.interpretation_mono`: the operations are monotone.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Chapter 9][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.Monotone

/-- Operations of the monotone basis. -/
inductive Op where
  /-- A Boolean constant. -/
  | const (b : Bool)
  /-- Binary conjunction. -/
  | and
  /-- Binary disjunction. -/
  | or
  deriving DecidableEq

instance : Fintype Op :=
  ⟨{.const false, .const true, .and, .or}, fun op => by rcases op with (_ | _) | _ | _ <;> simp⟩

/-- The monotone signature: constants, binary conjunction and binary disjunction. -/
abbrev signature : Signature where
  Op := Op
  Arity
    | .const _ => 0
    | .and | .or => 2

/-- The Boolean interpretation of the monotone basis. -/
def interpretation : Interpretation signature Bool
  | .const b, _ => b
  | .and, x => x 0 && x 1
  | .or, x => x 0 || x 1

@[simp] theorem interpretation_const (b : Bool) (x : Fin 0 → Bool) :
    interpretation (.const b) x = b := rfl

@[simp] theorem interpretation_and (x : Fin 2 → Bool) : interpretation .and x = (x 0 && x 1) :=
  rfl

@[simp] theorem interpretation_or (x : Fin 2 → Bool) : interpretation .or x = (x 0 || x 1) :=
  rfl

/-- The operations of the monotone basis are monotone. -/
theorem interpretation_mono (op : Op) {x y : Fin (signature.Arity op) → Bool}
    (h : ∀ i, x i ≤ y i) : interpretation op x ≤ interpretation op y := by
  cases op with
  | const b => exact Bool.le_refl b
  | and | or =>
    have h0 := h 0
    have h1 := h 1
    revert h0 h1
    simp only [interpretation]
    cases x 0 <;> cases x 1 <;> cases y 0 <;> cases y 1 <;> decide

end Cslib.Circuits.Monotone
