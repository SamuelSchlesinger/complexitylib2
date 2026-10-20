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
public import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.BigOperators

/-!
# Counting, numbering and adding bit strings

There are `2 ^ n` strings of `n` bits (`BitString.card`), numbered `0, …, 2 ^ n - 1` by reading
their bits as binary digits, least significant first (`BitString.equivFin`).

Bits form the two-element Boolean ring (Mathlib's `BooleanRing Bool`), in which `a + b = (a ^^ b)`
and `a * b = (a && b)`, so bit strings `ι → Bool` form an additive group under coordinatewise
exclusive or, the vector space `𝔽₂ⁿ` of [O'Donnell, Chapter 1][ODonnell2014]:
`(x + y) i = (x i ^^ y i)` holds by definition. Every bit string is its own negative
(`BitString.add_self`). Translating by a fixed string is the permutation `Equiv.addLeft x`.

Throughout the library, bit strings are added with `+`, while single bits, such as the values of
Boolean functions, are combined with `^^`.

## Main definitions

* `Cslib.BitString.equivFin`: the numbering of the strings of `n` bits by `Fin (2 ^ n)`.
* `Cslib.BitString.indexBits`: a finite index represented in `⌈log₂ n⌉` bits.

## Main results

* `Cslib.BitString.card`: the number of strings of `n` bits.
* `Cslib.BitString.val_equivFin_cons`: a new first bit is the least significant binary digit.
* `Cslib.BitString.indexBits_injective`: distinct finite indices have distinct encodings.
* `Cslib.BitString.add_self`, `Cslib.BitString.add_cancel_left`,
  `Cslib.BitString.add_cancel_right`: every bit string is its own negative.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

variable {n : ℕ}

/-- There are `2 ^ n` strings of `n` bits. -/
theorem card : Fintype.card (BitString n) = 2 ^ n := by
  simp

variable (n) in
/-- The strings of `n` bits numbered `0, …, 2 ^ n - 1`, reading the bits as binary digits with
the least significant bit first. -/
def equivFin : BitString n ≃ Fin (2 ^ n) :=
  (Equiv.arrowCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- A new first bit is the least significant digit of the number of a bit string. -/
theorem val_equivFin_cons (b : Bool) (z : BitString n) :
    (equivFin (n + 1) (Fin.cons b z : BitString (n + 1)) : ℕ) = b.toNat + 2 * equivFin n z := by
  have hbit (b : Bool) : ((finTwoEquiv.symm b : Fin 2) : ℕ) = b.toNat := by cases b <;> rfl
  simp only [equivFin, Equiv.trans_apply, finFunctionFinEquiv_apply, Fin.sum_univ_succ,
    Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_symm, Equiv.refl_apply, hbit,
    Fin.val_zero, pow_zero, Nat.mul_one, Fin.val_succ, pow_succ, Fin.cons_zero, Fin.cons_succ,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by
    rw [Nat.mul_comm (2 ^ (i : ℕ)) 2, Nat.mul_left_comm]

/-- The binary numeral of `i : Fin n` in `⌈log₂ n⌉` bits. -/
def indexBits (i : Fin n) : BitString (Nat.clog 2 n) :=
  (equivFin _).symm (Fin.castLE (Nat.le_pow_clog one_lt_two n) i)

/-- Distinct finite indices have distinct binary numerals. -/
theorem indexBits_injective : Function.Injective (indexBits (n := n)) :=
  (equivFin _).symm.injective.comp (Fin.castLE_injective _)

variable {ι : Type*}

/-- A bit string added to itself gives zero. -/
@[simp] protected theorem add_self (x : ι → Bool) : x + x = 0 :=
  funext fun i => Bool.xor_self (x i)

@[simp] protected theorem add_cancel_left (x y : ι → Bool) : x + (x + y) = y := by
  rw [← add_assoc, BitString.add_self, zero_add]

@[simp] protected theorem add_cancel_right (x y : ι → Bool) : x + y + y = x := by
  rw [add_assoc, BitString.add_self, add_zero]

end Cslib.BitString
