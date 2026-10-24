/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-! Ordinary topic imports provide binary arithmetic and captured raw-bit operations, with
plain premises and no sidecar calculus import. Edge cases keep their total semantics. -/

open Turing.MultiTapeTM

example : ComputableInPolyTime (fun p : ℕ × ℕ =>
    ((p.1 + 1) / p.2, (p.1 + 1) % p.2)) (encPair encNat encNat)
      (encPair encNat encNat) := by fun_prop

example : ComputableInPolyTime (fun k : ℕ => 2 ^ k) encUnary encNat := by fun_prop

example {α : Type} {input : α ↪ List Bool} {base exponent : α → ℕ}
    (hbase : ComputableInPolyTime base input encNat)
    (hexponent : ComputableInPolyTime exponent input encUnary) :
    ComputableInPolyTime (fun x => base x ^ exponent x) input encNat := by fun_prop

example {α : Type} {input : α ↪ List Bool} {value : α → ℤ} {modulus : α → ℕ}
    (hvalue : ComputableInPolyTime value input encIntBin)
    (hmodulus : ComputableInPolyTime modulus input encNat) :
    ComputableInPolyTime (fun x => ((value x - 1) % (modulus x : ℤ)).toNat)
      input encNat := by fun_prop

example : ComputableInPolyTime (fun p : ℕ × List Bool =>
    Cslib.BitString.listRow p.1 p.1 p.2) (encPair encUnary encBits) encBits := by fun_prop

example : ComputableInPolyTime (fun p : List ℤ × ℤ => p.1.sum * p.2)
    (encPair (encList encIntBin) encIntBin) encIntBin := by fun_prop

example : (37 / 0, 37 % 0) = (0, 37) ∧ (37 / 1, 37 % 1) = (37, 0) := by
  decide +kernel

example : ((-65 : ℤ) % 64).toNat = 63 ∧ ((-64 : ℤ) % 64).toNat = 0 ∧
    ((-7 : ℤ) % 0).toNat = 0 ∧ ((7 : ℤ) % 0).toNat = 7 := by decide +kernel

example : Cslib.BitString.listRow 0 100 [true] = [] := by decide +kernel

run_meta do
  let retired : List Lean.Name := [
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsToNat,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.natBits,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_add,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_mul,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_add',
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_sum,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_two_pow,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_lt,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_le,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_lt',
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_le',
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_mul',
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_pow,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_pow',
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_sub,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_sub',
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_testBit,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_divMod,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_div,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_mod,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_div',
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_mod',
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsFrame,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsBoundedBinaryValue,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsBoundedBinaryValueWithInput,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_to_unary_bounded,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsToList,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsGetElem?,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listToBits,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsReplicate,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsFlatten,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsPadWord,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapToBitsWithInput,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.flatMapToBitsWithInput,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsLow,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsMapWithInput,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsFilterWithInput,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsCountPWithInput,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsCountWithInput,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsAnyWithInput,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsAllWithInput,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsFoldlWithInput,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsZipWith,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsZipWithInput,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsStrictMajority,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsStrictMajorityWithInput,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsNonpositiveMarginWithInput,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsSingle,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsSingles,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsXorSelected,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsEnumList,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsRowWithInput,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsRowsWithInput,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsXorWithInput,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsWordLt,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsBinaryValue,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_isNeg,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_natAbs,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_signMagnitude,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_natCast,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_neg,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_add,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_mul,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_sub,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_isZero,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_isPos,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_sign,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_toNat,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_lt,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_le,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_pow,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_sum,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_prod,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_add',
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_sub',
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_mul',
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_pow',
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_lt',
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_le',
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_prod_range,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_emodNat,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_emodNat']
  let env ← Lean.getEnv
  for name in retired do
    if env.contains name then
      throwError "superseded binary construction export remains: {name}"

/-- info: 'Turing.MultiTapeTM.ComputableInPolyTime.binary_div' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputableInPolyTime.binary_div

/-- info: 'Turing.MultiTapeTM.ComputableInPolyTime.intBin_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputableInPolyTime.intBin_mul
