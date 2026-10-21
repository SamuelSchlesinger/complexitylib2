/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Nat/Bits.lean`)

public import Complexity.Init
public import Mathlib.Data.Nat.Bits

/-!
# Recovering a natural number from its binary digits

The digits returned by `Nat.bits` are least significant first. Folding `Nat.bit` from the right
with initial value zero reconstructs the original number.

## Main results

* `Nat.foldr_bit_bits`: folding `Nat.bit` over the binary representation of `n` gives `n`.
-/

@[expose] public section

/-- Folding `Nat.bit` over the binary representation of `n` gives back `n`. -/
@[simp]
theorem Nat.foldr_bit_bits (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih => rw [Nat.bits_append_bit n b h, List.foldr_cons, ih]
