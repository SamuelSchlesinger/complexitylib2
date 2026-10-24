/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.BitString.Basic
import Complexity.Foundations.Data.BitString.Binary
import Complexity.Foundations.Data.BitString.Block
import Complexity.Foundations.Data.BitString.Counter
import Complexity.Foundations.Data.BitString.Enumeration
import Complexity.Foundations.Data.BitString.List
import Complexity.Foundations.Data.BitString.List.Binary
import Complexity.Foundations.Data.BitString.Parity
import Complexity.Foundations.Data.BitString.Threshold

/-! # Checked examples of the core bit-string API

Concrete values of the numberings, weights, parities, thresholds, blocks and list encodings of
`Cslib.BitString`, evaluated on small words. Each example fixes a convention a client relies on:
`equivFin` and `lsbValue` read the first bit as the least significant one, `binaryValue` reads it
as the most significant one, `ofList` pads with `false`, and blocks are consecutive runs of bits.
-/

namespace ComplexityTests.BitString

open Cslib Cslib.BitString Finset

/-! ### Reading bits as numbers -/

-- `equivFin` reads the first bit as the least significant digit: `1 + 0 * 2 + 1 * 4 = 5`.
example : (equivFin 3 ![true, false, true] : ℕ) = 5 := by decide

example : (equivFin 3 ![false, true, true] : ℕ) = 6 := by decide

-- The same word, read by the list readings: least significant first, and most significant first.
example : lsbValue [false, true, true] = 6 := by decide

example : binaryValue [false, true, true] = 3 := by decide

example : binaryValue [true, true, false] = 6 := by decide

-- `lowBits` writes a value least significant bit first, padded to the requested width.
example : lowBits 4 6 = [false, true, true, false] := by decide

-- Numeral bridges between `equivFin`, `lsbValue`, `binaryValue`, `Nat.ofBits` and `Nat.testBit`.
example : lsbValue [true, false, true] = [true, false, true].foldr Nat.bit 0 :=
  lsbValue_eq_foldr_bit [true, false, true]

example : lsbValue (List.ofFn ![true, false, true]) = equivFin 3 ![true, false, true] :=
  lsbValue_ofFn ![true, false, true]

example : (equivFin 3 ![true, false, true] : ℕ) = Nat.ofBits ![true, false, true] :=
  val_equivFin_eq_ofBits ![true, false, true]

example : (equivFin 3).symm 5 2 = (5 : ℕ).testBit 2 :=
  equivFin_symm_apply 5 2

example : binaryValue (List.ofFn ![true, false, true]).reverse = equivFin 3 ![true, false, true] :=
  binaryValue_reverse_ofFn ![true, false, true]

-- There are `2 ^ n` words of `n` bits.
example : Fintype.card (BitString 5) = 32 := by rw [BitString.card]; rfl

/-! ### Weight, parity and thresholds -/

example : weight ![true, false, true, true] = 3 := by decide

example : parity 4 ![true, false, true, true] = true := by decide

example : parity 4 ![true, false, true, false] = false := by decide

example : threshold 4 3 ![true, false, true, true] = true := by decide

example : threshold 4 4 ![true, false, true, true] = false := by decide

example : majority 3 ![true, false, true] = true := by decide

example : strictMajority 4 ![true, false, true, false] = false := by decide

-- Every layer of weight at most `n` is inhabited, so statements about layers are not vacuous.
example : (weightLayer 5 2).Nonempty := weightLayer_nonempty (by decide)

example : (weightLayer 5 2).card = 10 := by rw [card_weightLayer]; rfl

-- Half of the words of a nonempty length have odd parity.
example : #{x : BitString 4 | parity 4 x = true} = 8 := card_filter_parity_eq_true (by decide)

/-! ### Blocks and list encodings -/

-- Blocks are consecutive runs: the second block of length `2` of `1011 0110` is `0110`.
example : List.ofFn (block (m := 2) (k := 4)
    ![true, false, true, true, false, true, true, false] 1) = [false, true, true, false] := by
  decide

-- `ofList` pads a short word with `false` and truncates a long one.
example : List.ofFn (ofList 4 [true, true]) = [true, true, false, false] := by decide

example : List.ofFn (ofList 2 [true, false, true]) = [true, false] := by decide

-- `listRow` reads a padded row of a flattened word.
example : listRow 2 1 [true, false, false, true, true] = [false, true] := by decide

example : listRow 2 2 [true, false, false, true, true] = [true, false] := by decide

-- `enum k` lists every word of `k` bits exactly once.
example : (enum 3).length = 8 := by decide

example : (enumList 2).Nodup := by decide

end ComplexityTests.BitString
