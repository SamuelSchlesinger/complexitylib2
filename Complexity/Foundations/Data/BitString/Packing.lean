/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Bits
public import Batteries.Data.Nat.Basic
import Mathlib.Tactic.Linarith

/-!
# Fixed-width packed words

A fixed tuple of bounded words stores an initial segment of a bit stream. Reading a field
constrains its entire value, including all bits outside the specified width.

## Main definitions

* `Cslib.BitString.packWords`: split a bit stream into a fixed tuple of words.
* `Cslib.BitString.readPackedField`: read a bounded-width field across word boundaries.

## Main results

* `Cslib.BitString.readPackedField_packWords`: exact field decoding.
* `Cslib.BitString.readPackedField_fields`: decoding fixed-width consecutive fields.
-/

@[expose] public section

namespace Cslib.BitString

/-- Pack a bit stream into `B` words of `h` bits each. -/
def packWords (f : ℕ → Bool) (h B : ℕ) (r : Fin B) : ℕ :=
  Nat.ofBits (fun b : Fin h => f (r.val * h + b.val))

theorem packWords_lt (f : ℕ → Bool) (h B : ℕ) (r : Fin B) :
    packWords f h B r < 2 ^ h := Nat.ofBits_lt_two_pow _

/-- Read one bit of a fixed tuple; unused addresses are false. -/
def readPackedBit {B : ℕ} (h : ℕ) (w : Fin B → ℕ) (a : ℕ) : Bool :=
  decide (∃ r : Fin B, ∃ b : Fin h, r.val * h + b.val = a ∧ (w r).testBit b.val = true)

/-- Decode exactly `s` bits starting at address `a`, with every higher bit zero. -/
def readPackedField {B : ℕ} (h : ℕ) (w : Fin B → ℕ) (a s : ℕ) : ℕ :=
  Nat.ofBits (fun b : Fin s => readPackedBit h w (a + b.val))

theorem readPackedField_lt {B : ℕ} (h : ℕ) (w : Fin B → ℕ) (a s : ℕ) :
    readPackedField h w a s < 2 ^ s := Nat.ofBits_lt_two_pow _

theorem readPackedField_testBit {B : ℕ} (h : ℕ) (w : Fin B → ℕ) (a s b : ℕ) :
    (readPackedField h w a s).testBit b = true ↔
      b < s ∧ ∃ r : Fin B, ∃ t : Fin h, r.val * h + t.val = a + b ∧
        (w r).testBit t.val = true := by
  by_cases hb : b < s <;> simp [readPackedField, Nat.testBit_ofBits, hb, readPackedBit]

/-- Every bit below the total capacity is recovered from the packed tuple. -/
theorem readPackedBit_packWords (f : ℕ → Bool) {h B a : ℕ} (ha : a < B * h) :
    readPackedBit h (packWords f h B) a = f a := by
  apply Bool.eq_iff_iff.mpr
  simp only [readPackedBit, decide_eq_true_eq]
  constructor
  · rintro ⟨r, b, he, hb⟩
    simpa only [packWords, Nat.testBit_ofBits_lt _ _ b.isLt, he] using hb
  · intro hf
    have hh : 0 < h := by nlinarith
    refine ⟨⟨a / h, (Nat.div_lt_iff_lt_mul hh).mpr ha⟩,
      ⟨a % h, Nat.mod_lt _ hh⟩, ?_, ?_⟩
    · simpa only [Nat.mul_comm] using Nat.div_add_mod a h
    · simpa only [packWords, Nat.testBit_ofBits_lt _ _ (Nat.mod_lt a hh),
        Nat.mul_comm (a / h), Nat.div_add_mod] using hf

/-- A fitting field is recovered exactly, including high zero bits. -/
theorem readPackedField_packWords (f : ℕ → Bool) {h B a s z : ℕ}
    (ha : a + s ≤ B * h) (hz : z < 2 ^ s) (hf : ∀ b < s, f (a + b) = z.testBit b) :
    readPackedField h (packWords f h B) a s = z := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < s
  · rw [readPackedField, Nat.testBit_ofBits_lt _ _ hb, readPackedBit_packWords f (by lia)]
    exact hf b hb
  · rw [readPackedField, Nat.testBit_ofBits_ge _ _ (by lia)]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hz
      (Nat.pow_le_pow_right (by decide) (show s ≤ b by lia)))).symm

/-- Consecutive fixed-width fields can be packed and decoded without overlap. -/
theorem readPackedField_fields (v : ℕ → ℕ) {h B q s : ℕ} (hs : 0 < s)
    (ha : q * s + s ≤ B * h) (hv : v q < 2 ^ s) :
    readPackedField h (packWords (fun a => (v (a / s)).testBit (a % s)) h B)
      (q * s) s = v q := by
  apply readPackedField_packWords _ ha hv
  intro b hb
  rw [Nat.mul_comm q s, Nat.mul_add_div hs, Nat.div_eq_of_lt hb, Nat.add_zero,
    Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hb]

end Cslib.BitString
