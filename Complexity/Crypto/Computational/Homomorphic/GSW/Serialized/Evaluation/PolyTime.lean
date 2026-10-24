/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.GSW.Serialized.Evaluation
public import Complexity.Crypto.Computational.Homomorphic.GSW.Serialized.PolyTime

/-!
# Uniform native GSW decryption and NAND

The actual serialized operations have uniform native polynomial-time certificates. Dimensions
and loop indices are unary; modular values and signed differences are binary. Complete input
words, intermediate sums and all output bits are charged. The certificates apply to arbitrary
raw words, without shape, noise, support or security assumptions.

## Main results

* `computableTidilyInPolyTime_decryptSerialized`: the actual total raw-word decryption test.
* `computableTidilyInPolyTime_nandSerialized`: the complete actual NAND ciphertext computation.

## References

* [Gentry, Sahai and Waters, Sections 3.1 and 3.3][GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

variable {α : Type} {input : α ↪ List Bool} {n w i k j : α → ℕ}

/-- Compute the selected phase uniformly from every pair of raw secret and ciphertext words. -/
@[fun_prop]
theorem computableTidilyInPolyTime_decryptResidue {secret ciphertext : α → List Bool}
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hw : ComputableTidilyInPolyTime w input encUnary)
    (hsecret : ComputableTidilyInPolyTime secret input encBits)
    (hciphertext : ComputableTidilyInPolyTime ciphertext input encBits) :
    ComputableTidilyInPolyTime
      (fun a => decryptResidue (n a) (w a) (secret a) (ciphertext a)) input encNat := by
  have hterm : ComputableTidilyInPolyTime
      (fun p : α × ℕ => Matrix.binaryEntry (n p.1 + 1) (w p.1) (ciphertext p.1)
        (w p.1 - 1) (p.2 + 1) * Matrix.binaryEntry (n p.1) (w p.1) (secret p.1) 0 p.2)
      (encPair input encUnary) encNat := by
    apply binary_mul'
    · exact (ComputableInPolyTime.matrixBinaryEntry
        (.of_tidy (by fun_prop)) (.of_tidy (by fun_prop)) (.of_tidy (by fun_prop))
        (.of_tidy (by fun_prop)) (.of_tidy (by fun_prop))).tidy
    · exact (ComputableInPolyTime.matrixBinaryEntry
        (.of_tidy (by fun_prop)) (.of_tidy (by fun_prop)) (.of_tidy (by fun_prop))
        (.of_tidy (const 0)) (.of_tidy (snd input encUnary))).tidy
  have hsum := binary_sum.comp (mapWithInput
    (f := fun a j => Matrix.binaryEntry (n a + 1) (w a) (ciphertext a) (w a - 1) (j + 1) *
      Matrix.binaryEntry (n a) (w a) (secret a) 0 j) (range.comp hn) hterm)
  have hfirst := (ComputableInPolyTime.matrixBinaryEntry
    (.of_tidy (by fun_prop)) (.of_tidy hw) (.of_tidy hciphertext)
    (.of_tidy (by fun_prop)) (.of_tidy (const 0))
    (cols := fun a => n a + 1) (row := fun a => w a - 1)).tidy
  unfold decryptResidue
  simpa only [Function.comp_apply, Nat.cast_pow, Nat.cast_ofNat] using
    intBin_emodNat' (intBin_sub' (intBin_natCast.comp hfirst) (intBin_natCast.comp hsum))
      (binary_pow' (const 2) hw)

/-- The total decoder is polynomial-time on the complete inputs, including malformed words. -/
@[fun_prop]
theorem computableTidilyInPolyTime_decryptSerialized {secret ciphertext : α → List Bool}
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hw : ComputableTidilyInPolyTime w input encUnary)
    (hsecret : ComputableTidilyInPolyTime secret input encBits)
    (hciphertext : ComputableTidilyInPolyTime ciphertext input encBits) :
    ComputableTidilyInPolyTime
      (fun a => decryptSerialized (n a) (w a) (secret a) (ciphertext a)) input encBool := by
  have hvalue := computableTidilyInPolyTime_decryptResidue hn hw hsecret hciphertext
  have hq := binary_pow' (const 2) hw
  have hfour := binary_mul' (const 4) hvalue
  have htest : ComputableTidilyInPolyTime
      (fun a => decide (2 ^ w a ≤ 4 * decryptResidue (n a) (w a) (secret a) (ciphertext a) ∧
        4 * decryptResidue (n a) (w a) (secret a) (ciphertext a) < 3 * 2 ^ w a))
      input encBool :=
    decide_and (binary_le' hq hfour) (binary_lt' hfour (binary_mul' (const 3) hq))
  simpa only [decryptSerialized, beq_iff_eq] using
    (unary_beq hw (const 0)).ite' (const false) htest

/-- Compute one actual NAND residue, keeping the complete binary sum before signed reduction. -/
@[fun_prop]
theorem computableTidilyInPolyTime_nandEntry {left right : α → List Bool}
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hw : ComputableTidilyInPolyTime w input encUnary)
    (hleft : ComputableTidilyInPolyTime left input encBits)
    (hright : ComputableTidilyInPolyTime right input encBits)
    (hi : ComputableTidilyInPolyTime i input encUnary)
    (hk : ComputableTidilyInPolyTime k input encUnary)
    (hj : ComputableTidilyInPolyTime j input encUnary) :
    ComputableTidilyInPolyTime
      (fun a => nandEntry (n a) (w a) (left a) (right a) (i a) (k a) (j a)) input encNat := by
  have hterm : ComputableTidilyInPolyTime
      (fun p : α × ℕ =>
        if (left p.1).getD ((i p.1 * w p.1 + k p.1) * ((n p.1 + 1) * w p.1) + p.2) false
        then Matrix.binaryEntry (n p.1 + 1) (w p.1) (right p.1) p.2 (j p.1) else 0)
      (encPair input encUnary) encNat := by
    apply ((bitsGetD false).comp ((hleft.comp (fst input encUnary)).prod (by fun_prop))).ite'
    · exact (ComputableInPolyTime.matrixBinaryEntry
        (.of_tidy (by fun_prop)) (.of_tidy (by fun_prop)) (.of_tidy (by fun_prop))
        (.of_tidy (snd input encUnary)) (.of_tidy (by fun_prop))).tidy
    · exact const 0
  have hsum := binary_sum.comp (mapWithInput
    (f := fun a r => if (left a).getD ((i a * w a + k a) * ((n a + 1) * w a) + r) false
      then Matrix.binaryEntry (n a + 1) (w a) (right a) r (j a) else 0)
    (range.comp (show ComputableTidilyInPolyTime (fun a => (n a + 1) * w a)
      input encUnary by fun_prop)) hterm)
  have hgadget : ComputableTidilyInPolyTime
      (fun a => if i a = j a then 2 ^ k a else 0) input encNat := by
    simpa only [beq_iff_eq] using
      (unary_beq hi hj).ite' (binary_pow' (const 2) hk) (const 0)
  unfold nandEntry
  simpa only [Function.comp_apply, Nat.cast_pow, Nat.cast_ofNat] using
    intBin_emodNat' (intBin_sub' (intBin_natCast.comp hgadget) (intBin_natCast.comp hsum))
      (binary_pow' (const 2) hw)

/-- Compute the full square ciphertext with a single uniform native polynomial clock. -/
@[fun_prop]
theorem computableTidilyInPolyTime_nandSerialized {left right : α → List Bool}
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hw : ComputableTidilyInPolyTime w input encUnary)
    (hleft : ComputableTidilyInPolyTime left input encBits)
    (hright : ComputableTidilyInPolyTime right input encBits) :
    ComputableTidilyInPolyTime
      (fun a => nandSerialized (n a) (w a) (left a) (right a)) input encBits := by
  unfold nandSerialized
  apply flatMapToBitsWithInput (range.comp (by fun_prop))
  apply flatMapToBitsWithInput (range.comp (by fun_prop))
  apply flatMapToBitsWithInput (range.comp (by fun_prop))
  fun_prop

end Cslib.Crypto.Homomorphic.GSW
