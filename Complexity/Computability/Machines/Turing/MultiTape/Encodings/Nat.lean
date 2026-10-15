/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: subset of crei/tidy-universal `Encodings/Nat.lean`;
-- definitions only, delete when it lands

public import Complexity.Init
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Logic.Embedding.Basic

/-!
# The binary encoding of natural numbers

`encNat` encodes a natural number by its binary digits, least significant first (`Nat.bits`).

A verbatim subset of Christian Reitwiessner's `Encodings/Nat.lean` (branch `crei/tidy-universal`),
without the successor machine.

## Main definitions

* `Turing.MultiTapeTM.encNat`: natural numbers encoded by their binary digits.
-/

namespace Turing.MultiTapeTM

/-- Natural numbers encoded by their binary digits, least significant first. -/
@[expose] public def encNat : ℕ ↪ List Bool :=
  ⟨Nat.bits, fun m n h => Nat.eq_of_testBit_eq fun i => by simp [Nat.testBit_eq_inth, h]⟩

@[simp]
public lemma encNat_apply (n : ℕ) : encNat n = n.bits := rfl

end Turing.MultiTapeTM
