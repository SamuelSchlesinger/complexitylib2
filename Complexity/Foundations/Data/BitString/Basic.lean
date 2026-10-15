/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Foundations/Data/BitString.lean`)

public import Cslib.Foundations.Data.BitString
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

/-!
# Counting and adding bit strings

There are `2 ^ n` strings of `n` bits (`BitString.card_eq`), numbered `0, …, 2 ^ n - 1` by reading
their bits as binary digits, least significant first (`BitString.equivFin`).

Bits form the two-element Boolean ring (Mathlib's `BooleanRing Bool`), in which `a + b = (a ^^ b)`
and `a * b = (a && b)`, so bit strings form an additive group under coordinatewise exclusive or:
`(x + y) i = (x i ^^ y i)` holds by definition. Every bit string is its own negative
(`BitString.add_self`). Translating by a fixed string is the permutation `Equiv.addLeft x`.

Throughout the library, bit strings are added with `+`, while single bits, such as the values of
Boolean functions, are combined with `^^`.

## Main definitions

* `Cslib.BitString.equivFin`: the numbering of the strings of `n` bits by `Fin (2 ^ n)`.

## Main results

* `Cslib.BitString.card_eq`: the number of strings of `n` bits.
* `Cslib.BitString.add_self`, `Cslib.BitString.add_cancel_left`,
  `Cslib.BitString.add_cancel_right`: every bit string is its own negative.
-/

@[expose] public section

namespace Cslib.BitString

variable {n : ℕ}

/-- There are `2 ^ n` strings of `n` bits. -/
theorem card_eq : Fintype.card (BitString n) = 2 ^ n := by
  simp

variable (n) in
/-- The strings of `n` bits numbered `0, …, 2 ^ n - 1`, reading the bits as binary digits with
the least significant bit first. -/
def equivFin : BitString n ≃ Fin (2 ^ n) :=
  (Equiv.arrowCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- A bit string added to itself gives zero. -/
@[simp] protected theorem add_self (x : BitString n) : x + x = 0 :=
  funext fun i => Bool.xor_self (x i)

@[simp] protected theorem add_cancel_left (x y : BitString n) : x + (x + y) = y := by
  rw [← add_assoc, BitString.add_self, zero_add]

@[simp] protected theorem add_cancel_right (x y : BitString n) : x + y + y = x := by
  rw [add_assoc, BitString.add_self, add_zero]

end Cslib.BitString
