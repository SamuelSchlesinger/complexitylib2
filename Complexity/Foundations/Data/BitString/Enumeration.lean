/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Basic

/-!
# Enumerating bit strings

The list `BitString.enum n` enumerates all `n`-bit strings once in binary order, least significant
bit first. This is an executable enumeration; generating its `2 ^ n` entries is not asserted to
be polynomial in `n`.

## Main definitions

* `Cslib.BitString.enum`: enumerate bit strings by prepending both bits to every shorter string.

## Main results

* `Cslib.BitString.mem_enum`, `Cslib.BitString.length_enum`, `Cslib.BitString.nodup_enum`:
  the enumeration contains each bit string exactly once and has `2 ^ n` entries.

## References

Adapted from `Crypto/Computational/GoldreichLevin/Reduction.lean` on the cslib `crypto` branch
at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.BitString

/-- Enumerate bitstrings by prepending each possible bit. This fixes an executable order. -/
def enum : (k : ℕ) → List (BitString k)
  | 0 => [Fin.elim0]
  | k + 1 => (enum k).flatMap (fun guess => [Fin.cons false guess, Fin.cons true guess])

/-- Every bit string is enumerated. -/
@[simp] theorem mem_enum (k : ℕ) (guess : BitString k) : guess ∈ enum k := by
  induction k with
  | zero => simp [enum, Subsingleton.elim guess Fin.elim0]
  | succ k ih =>
    apply List.mem_flatMap.mpr
    refine ⟨Fin.tail guess, ih _, ?_⟩
    have hg := Fin.cons_self_tail guess
    cases hbit : guess 0 <;> simp_all

/-- There are exactly `2 ^ k` strings of `k` bits. -/
@[simp] theorem length_enum (k : ℕ) : (enum k).length = 2 ^ k := by
  induction k with
  | zero => simp [enum]
  | succ k ih =>
    simp [enum, List.length_flatMap, ih, pow_succ, Nat.mul_comm]

/-- Each bit string occurs exactly once. -/
theorem nodup_enum (k : ℕ) : (enum k).Nodup := by
  rw [List.nodup_iff_length_dedup_eq, ← List.card_toFinset]
  have hall : (enum k).toFinset = Finset.univ := by ext; simp
  rw [hall]
  simp [BitString]

end Cslib.BitString
