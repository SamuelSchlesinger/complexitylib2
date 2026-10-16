/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init

/-!
# Saturating binary decoding

Words are read most significant bit first. Saturating at every step keeps a unary accumulator
bounded on arbitrary input words; it agrees with capping the full mathematical binary value.

## Main definitions

* `binaryValue`: the natural represented by a binary word, without a size bound.
* `boundedBinaryValue`: the same fold with a cap at every step.

## Main results

* `boundedBinaryValue_eq`: incremental saturation equals a single final cap.
* `boundedBinaryValue_le`: every output is at most the cap.

## References

Adapted from `Probability/UniformNat.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.BitString

/-- The natural number represented by a word, most significant bit first. -/
def binaryValue (word : List Bool) : ℕ :=
  word.foldl (fun value bit => 2 * value + bit.toNat) 0

/-- Decode binary digits with a saturating accumulator. -/
def boundedBinaryValue (bound : ℕ) (word : List Bool) : ℕ :=
  word.foldl (fun value bit => min bound (2 * value + bit.toNat)) 0

private theorem min_binary_step (bound value : ℕ) (bit : Bool) :
    min bound (2 * min bound value + bit.toNat) = min bound (2 * value + bit.toNat) := by
  by_cases h : value ≤ bound
  · rw [Nat.min_eq_right h]
  · rw [Nat.min_eq_left (by lia), Nat.min_eq_left (by lia)]

/-- Saturating at each step agrees with capping the final mathematical value. -/
theorem boundedBinaryValue_eq (bound : ℕ) (word : List Bool) :
    boundedBinaryValue bound word = min bound (binaryValue word) := by
  have h (word : List Bool) (value : ℕ) :
      word.foldl (fun value bit => min bound (2 * value + bit.toNat)) (min bound value) =
        min bound (word.foldl (fun value bit => 2 * value + bit.toNat) value) := by
    induction word generalizing value with
    | nil => rfl
    | cons bit word ih => simp only [List.foldl_cons, min_binary_step, ih]
  simpa only [boundedBinaryValue, binaryValue, Nat.min_zero] using h word 0

/-- The unary result never exceeds the declared bound. -/
theorem boundedBinaryValue_le (bound : ℕ) (word : List Bool) :
    boundedBinaryValue bound word ≤ bound := by
  rw [boundedBinaryValue_eq]
  exact Nat.min_le_left _ _

/-- Append a low-order bit to a most-significant-first binary word. -/
theorem binaryValue_snoc (word : List Bool) (bit : Bool) :
    binaryValue (word ++ [bit]) = 2 * binaryValue word + bit.toNat := by
  simp [binaryValue, List.foldl_append]

/-- An all-one binary word represents one less than the corresponding power of two. -/
theorem binaryValue_replicate_true (k : ℕ) :
    binaryValue (List.replicate k true) + 1 = 2 ^ k := by
  induction k with
  | zero => simp [binaryValue]
  | succ k ih =>
    rw [List.replicate_succ']
    simp only [binaryValue, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Bool.toNat_true] at *
    rw [Nat.pow_succ]
    lia

end Cslib.BitString
