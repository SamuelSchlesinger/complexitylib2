/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, Erik Demaine, Karn Seth, OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Factorial
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Fin
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Prime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Search

/-!
# Plain polynomial-time structural and primitive rules

These ordinary declarations preserve the encodings, captured parameters and quantitative premises
of the construction certificates used in their proofs. Public clients use the plain statements.

The existing construction exports and registrations are retired during the coordinated #456
client migration; this source package does not add an internal-layer exemption.
-/

public section

open _root_.Turing.MultiTapeTM

namespace Turing.MultiTapeTM

end Turing.MultiTapeTM

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Addition of binary naturals. -/
theorem binary_add :
    ComputableInPolyTime (fun (p : ℕ × ℕ) => p.1 + p.2)
      (encPair encNat encNat)
      encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_add

/-- Add computed binary values, fixing their intermediate encodings for proof search. -/
theorem binary_add'
    {α : Type}
    {input : α ↪ List Bool}
    {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun (a : α) => left a + right a) input
      encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_add' α input left right hleft hright

/-- Division of binary naturals. -/
theorem binary_div :
    ComputableInPolyTime (fun (p : ℕ × ℕ) => p.1 / p.2)
      (encPair encNat encNat)
      encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_div

/-- Divide computed binary values, fixing their intermediate encodings for proof search. -/
theorem binary_div'
    {α : Type}
    {input : α ↪ List Bool}
    {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun (a : α) => left a / right a) input
      encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_div' α input left right hleft hright

/-- Compute both quotient and remainder of binary naturals by shift-and-subtract long division. -/
theorem binary_divMod :
    ComputableInPolyTime (fun (p : ℕ × ℕ) => (p.1 / p.2, p.1 % p.2))
      (encPair encNat encNat)
      (encPair encNat encNat) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_divMod

/-- `n !` in binary, from `n` in unary, by multiplying `1, 2, …, n`. -/
theorem binary_factorial :
    ComputableInPolyTime Nat.factorial encUnary
      encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_factorial

/-- Greatest common divisor of binary naturals via Euclid's algorithm. -/
theorem binary_gcd :
    ComputableInPolyTime (fun (p : ℕ × ℕ) => p.1.gcd p.2)
      (encPair encNat encNat)
      encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_gcd

/-- Greatest common divisor of computed binary values, fixing their intermediate encodings for
proof search. -/
theorem binary_gcd'
    {α : Type}
    {input : α ↪ List Bool}
    {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun (a : α) => (left a).gcd (right a)) input
      encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_gcd' α input left right hleft hright

/-- Comparison of binary naturals. -/
theorem binary_le :
    ComputableInPolyTime
      (fun (p : ℕ × ℕ) => Decidable.decide (p.1 ≤ p.2))
      (encPair encNat encNat)
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_le

/-- Compare computed binary values, fixing their intermediate encodings. -/
theorem binary_le'
    {α : Type}
    {input : α ↪ List Bool}
    {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime
      (fun (a : α) => Decidable.decide (left a ≤ right a)) input encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_le' α input left right hleft hright

/-- The base-two logarithm is polynomial-time on binary naturals, with its result in unary. -/
theorem binary_log_two :
    ComputableInPolyTime (Nat.log 2) encNat
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_log_two

/-- Strict comparison of binary naturals by scanning bit positions. -/
theorem binary_lt :
    ComputableInPolyTime
      (fun (p : ℕ × ℕ) => Decidable.decide (p.1 < p.2))
      (encPair encNat encNat)
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_lt

/-- Strictly compare computed binary values, fixing their intermediate encodings. -/
theorem binary_lt'
    {α : Type}
    {input : α ↪ List Bool}
    {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime
      (fun (a : α) => Decidable.decide (left a < right a)) input encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_lt' α input left right hleft hright

/-- Remainder of binary naturals. -/
theorem binary_mod :
    ComputableInPolyTime (fun (p : ℕ × ℕ) => p.1 % p.2)
      (encPair encNat encNat)
      encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_mod

/-- Remainder of computed binary values, fixing their intermediate encodings for proof search. -/
theorem binary_mod'
    {α : Type}
    {input : α ↪ List Bool}
    {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun (a : α) => left a % right a) input
      encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_mod' α input left right hleft hright

/-- Multiplication of binary naturals. -/
theorem binary_mul :
    ComputableInPolyTime (fun (p : ℕ × ℕ) => p.1 * p.2)
      (encPair encNat encNat)
      encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_mul

/-- Multiply computed binary values, fixing their intermediate encodings for proof search. -/
theorem binary_mul'
    {α : Type}
    {input : α ↪ List Bool}
    {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun (a : α) => left a * right a) input
      encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_mul' α input left right hleft hright

/-- A power of a binary natural to a unary exponent, by repeated multiplication. -/
theorem binary_pow :
    ComputableInPolyTime (fun (p : ℕ × ℕ) => p.1 ^ p.2)
      (encPair encNat encUnary)
      encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_pow

/-- Raise a computed binary value to a computed unary exponent, fixing the intermediate
encodings. -/
theorem binary_pow'
    {α : Type}
    {input : α ↪ List Bool}
    {base exponent : α → ℕ}
    (hbase : ComputableInPolyTime base input encNat)
    (hexponent : ComputableInPolyTime exponent input encUnary) :
    ComputableInPolyTime (fun (a : α) => base a ^ exponent a) input
      encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_pow' α input base exponent hbase hexponent

/-- Truncated subtraction of binary naturals, by schoolbook subtraction with a borrow. -/
theorem binary_sub :
    ComputableInPolyTime (fun (p : ℕ × ℕ) => p.1 - p.2)
      (encPair encNat encNat)
      encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_sub

/-- Subtract computed binary values, truncating at zero and fixing their intermediate
encodings. -/
theorem binary_sub'
    {α : Type}
    {input : α ↪ List Bool}
    {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun (a : α) => left a - right a) input
      encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_sub' α input left right hleft hright

/-- The sum of a list of binary naturals, by a left fold of binary additions. -/
theorem binary_sum :
    ComputableInPolyTime List.sum
      (encList encNat) encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_sum

/-- Read the bit of a computed binary number at a computed unary position. -/
theorem binary_testBit
    {α : Type}
    {input : α ↪ List Bool}
    {n i : α → ℕ}
    (hn : ComputableInPolyTime n input encNat)
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun (a : α) => (n a).testBit (i a)) input
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_testBit α input n i hn hi

/-- Convert a binary value to unary under a computed unary bound. -/
theorem binary_to_unary_bounded
    {α : Type}
    {input : α ↪ List Bool}
    {value bound : α → ℕ}
    (hvalue : ComputableInPolyTime value input encNat)
    (hbound : ComputableInPolyTime bound input encUnary)
    (hle : ∀ (a : α), value a ≤ bound a) :
    ComputableInPolyTime value input encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_to_unary_bounded α input value bound hvalue hbound
    hle

/-- `2 ^ k` in binary, from `k` in unary, by doubling. -/
theorem binary_two_pow :
    ComputableInPolyTime (fun (k : ℕ) => 2 ^ k)
      encUnary encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_two_pow

/-- Test whether every bit satisfies a captured predicate. -/
theorem bitsAllWithInput
    {α : Type}
    {input : α ↪ List Bool}
    {list : α → List Bool}
    {test : α → Bool → Bool}
    (hlist : ComputableInPolyTime list input encBits)
    (htest : ComputableInPolyTime (fun (p : α × Bool) => test p.1 p.2)
  (encPair input encBool)
  encBool) :
    ComputableInPolyTime (fun (a : α) => (list a).all (test a)) input
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsAllWithInput α input list test hlist htest

/-- Test whether any bit satisfies a captured predicate. -/
theorem bitsAnyWithInput
    {α : Type}
    {input : α ↪ List Bool}
    {list : α → List Bool}
    {test : α → Bool → Bool}
    (hlist : ComputableInPolyTime list input encBits)
    (htest : ComputableInPolyTime (fun (p : α × Bool) => test p.1 p.2)
  (encPair input encBool)
  encBool) :
    ComputableInPolyTime (fun (a : α) => (list a).any (test a)) input
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsAnyWithInput α input list test hlist htest

/-- Decode arbitrary most-significant-first bit words to binary naturals. -/
theorem bitsBinaryValue :
    ComputableInPolyTime Cslib.BitString.binaryValue
      encBits encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsBinaryValue

/-- Saturating binary decoding to unary is polynomial time on arbitrary input words. -/
theorem bitsBoundedBinaryValue :
    ComputableInPolyTime
      (fun (p : ℕ × List Bool) => Cslib.BitString.boundedBinaryValue p.1 p.2)
      (encPair encUnary encBits)
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsBoundedBinaryValue

/-- Decode computed bits under a computed unary cap, fixing both intermediate encodings. -/
theorem bitsBoundedBinaryValueWithInput
    {α : Type}
    {input : α ↪ List Bool}
    {cap : α → ℕ}
    {word : α → List Bool}
    (hcap : ComputableInPolyTime cap input encUnary)
    (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime
      (fun (a : α) => Cslib.BitString.boundedBinaryValue (cap a) (word a)) input
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsBoundedBinaryValueWithInput α input cap word hcap hword

/-- Count predicate matches in a raw bit string, including a captured input. -/
theorem bitsCountPWithInput
    {α : Type}
    {input : α ↪ List Bool}
    {list : α → List Bool}
    {test : α → Bool → Bool}
    (hlist : ComputableInPolyTime list input encBits)
    (htest : ComputableInPolyTime (fun (p : α × Bool) => test p.1 p.2)
  (encPair input encBool)
  encBool) :
    ComputableInPolyTime (fun (x : α) => List.countP (test x) (list x))
      input encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsCountPWithInput α input list test hlist htest

/-- Count occurrences of a computed bit in a raw bit string. -/
theorem bitsCountWithInput
    {α : Type}
    {input : α ↪ List Bool}
    {list : α → List Bool}
    {value : α → Bool}
    (hlist : ComputableInPolyTime list input encBits)
    (hvalue : ComputableInPolyTime value input encBool) :
    ComputableInPolyTime (fun (x : α) => List.count (value x) (list x))
      input encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsCountWithInput α input list value hlist hvalue

/-- Enumerate words only when their complete encoded size is polynomially bounded.
This does not claim polynomial time in the number of enumerated bits. -/
theorem bitsEnumList
    {α : Type}
    {input : α ↪ List Bool}
    {count : α → ℕ}
    (hcount : ComputableInPolyTime count input encUnary)
    {size : ℕ → ℕ}
    (hsize : Cslib.PolynomiallyBounded size)
    (hbudget :
      ∀ (a : α), 2 ^ count a * (2 * count a + 1) ≤ size ((input : α → List Bool) a).length) :
    ComputableInPolyTime
      (fun (a : α) => Cslib.BitString.enumList (count a)) input
      (encList encBits) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsEnumList α input count hcount size hsize hbudget

/-- Filter a raw bit string with a predicate that may capture its original input. -/
theorem bitsFilterWithInput
    {α : Type}
    {input : α ↪ List Bool}
    {list : α → List Bool}
    {test : α → Bool → Bool}
    (hlist : ComputableInPolyTime list input encBits)
    (htest : ComputableInPolyTime (fun (p : α × Bool) => test p.1 p.2)
  (encPair input encBool)
  encBool) :
    ComputableInPolyTime (fun (a : α) => List.filter (test a) (list a))
      input encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsFilterWithInput α input list test hlist htest

/-- Concatenate computed raw words, fixing the intermediate list encoding before proof search. -/
theorem bitsFlatten
    {α : Type}
    {input : α ↪ List Bool}
    {words : α → List (List Bool)}
    (hwords : ComputableInPolyTime words input
  (encList encBits)) :
    ComputableInPolyTime (fun (a : α) => (words a).flatten) input
      encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsFlatten α input words hwords

/-- A Boolean fold has constant-sized state, so no separate state bound is needed. -/
theorem bitsFoldlWithInput
    {α : Type}
    {input : α ↪ List Bool}
    (op : Bool → Bool → Bool)
    {list : α → List Bool}
    {init : α → Bool}
    (hlist : ComputableInPolyTime list input encBits)
    (hinit : ComputableInPolyTime init input encBool) :
    ComputableInPolyTime (fun (a : α) => List.foldl op (init a) (list a))
      input encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsFoldlWithInput α input op list init hlist hinit

/-- Frame the existing input encoding, charging every delimiter. -/
theorem bitsFrame
    {α : Type}
    (enc : α ↪ List Bool) :
    ComputableInPolyTime
      (fun (a : α) => frame ((enc : α → List Bool) a)) enc
      encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsFrame α enc

/-- Optional lookup in a raw bit string, fixing the representation of the returned bit. -/
theorem bitsGetElem?
    {α : Type}
    {input : α ↪ List Bool}
    {list : α → List Bool}
    {index : α → ℕ}
    (hlist : ComputableInPolyTime list input encBits)
    (hindex : ComputableInPolyTime index input encUnary) :
    ComputableInPolyTime (fun (x : α) => (list x)[index x]?) input
      (encOption encBool) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsGetElem? α input list index hlist hindex

/-- Emit a computed unary number of low-order digits of a computed binary natural. The width
charges every output bit, including leading zero digits. -/
theorem bitsLow
    {α : Type}
    {input : α ↪ List Bool}
    {width value : α → ℕ}
    (hwidth : ComputableInPolyTime width input encUnary)
    (hvalue : ComputableInPolyTime value input encNat) :
    ComputableInPolyTime
      (fun (a : α) => Cslib.BitString.lowBits (width a) (value a)) input
      encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsLow α input width value hwidth hvalue

/-- Map a captured Boolean operation over a raw bit string. -/
theorem bitsMapWithInput
    {α : Type}
    {input : α ↪ List Bool}
    {list : α → List Bool}
    {f : α → Bool → Bool}
    (hlist : ComputableInPolyTime list input encBits)
    (hf : ComputableInPolyTime (fun (p : α × Bool) => f p.1 p.2)
  (encPair input encBool)
  encBool) :
    ComputableInPolyTime (fun (a : α) => List.map (f a) (list a)) input
      encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsMapWithInput α input list f hlist hf

/-- The training test is polynomial time in the vote list and its supplied label. -/
theorem bitsNonpositiveMarginWithInput
    {α : Type}
    {input : α ↪ List Bool}
    {votes : α → List Bool}
    {truth : α → Bool}
    (hvotes : ComputableInPolyTime votes input encBits)
    (htruth : ComputableInPolyTime truth input encBool) :
    ComputableInPolyTime
      (fun (a : α) => Cslib.BitString.listNonpositiveMargin (votes a) (truth a)) input
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsNonpositiveMarginWithInput α input votes truth hvotes
    htruth

/-- Self-delimiting padding uses ordinary framing and unary arithmetic. -/
theorem bitsPadWord
    {α : Type}
    {input : α ↪ List Bool}
    {bound : α → ℕ}
    {word : α → List Bool}
    (hbound : ComputableInPolyTime bound input encUnary)
    (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime
      (fun (a : α) => Cslib.BitString.padWord (bound a) (word a)) input
      encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsPadWord α input bound word hbound hword

/-- Repeat a fixed bit a unary number of times. -/
theorem bitsReplicate
    (bit : Bool) :
    ComputableInPolyTime (fun (n : ℕ) => List.replicate n bit)
      encUnary encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsReplicate bit

/-- Read a row of a computed word, including the cost of padding a short word. -/
theorem bitsRowWithInput
    {α : Type}
    {input : α ↪ List Bool}
    {width row : α → ℕ}
    {word : α → List Bool}
    (hwidth : ComputableInPolyTime width input encUnary)
    (hrow : ComputableInPolyTime row input encUnary)
    (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime
      (fun (a : α) => Cslib.BitString.listRow (width a) (row a) (word a)) input
      encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsRowWithInput α input width row word hwidth hrow hword

/-- Extract rows from a word with polynomial-time unary dimensions. -/
theorem bitsRowsWithInput
    {α : Type}
    {input : α ↪ List Bool}
    {count width : α → ℕ}
    {word : α → List Bool}
    (hcount : ComputableInPolyTime count input encUnary)
    (hwidth : ComputableInPolyTime width input encUnary)
    (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime
      (fun (a : α) => Cslib.BitString.listRows (count a) (width a) (word a)) input
      (encList encBits) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsRowsWithInput α input count width word hcount hwidth
    hword

/-- Generate one coordinate mask from its unary width and index. -/
theorem bitsSingle :
    ComputableInPolyTime
      (fun (p : ℕ × ℕ) => Cslib.BitString.listSingle p.1 p.2)
      (encPair encUnary encUnary)
      encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsSingle

/-- Generate all coordinate masks, charging for their quadratic total size. -/
theorem bitsSingles :
    ComputableInPolyTime Cslib.BitString.listSingles
      encUnary (encList encBits) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsSingles

/-- Strict majority uses filtering, length, unary multiplication and comparison. -/
theorem bitsStrictMajority :
    ComputableInPolyTime Cslib.BitString.listStrictMajority
      encBits encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsStrictMajority

/-- Strict majority of computed votes fixes the intermediate raw-word encoding. -/
theorem bitsStrictMajorityWithInput
    {α : Type}
    {input : α ↪ List Bool}
    {votes : α → List Bool}
    (hvotes : ComputableInPolyTime votes input encBits) :
    ComputableInPolyTime
      (fun (a : α) => Cslib.BitString.listStrictMajority (votes a)) input
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsStrictMajorityWithInput α input votes hvotes

/-- Convert a raw bit string to the framed list encoding. -/
theorem bitsToList :
    ComputableInPolyTime (fun (l : List Bool) => l)
      encBits (encList encBool) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsToList

/-- Decode arbitrary little-endian bit words to binary naturals. -/
theorem bitsToNat :
    ComputableInPolyTime ofBits
      encBits encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsToNat

/-- Lexicographic comparison of equal-length words is polynomial-time. -/
theorem bitsWordLt
    {α : Type}
    {input : α ↪ List Bool}
    {x y : α → List Bool}
    (hx : ComputableInPolyTime x input encBits)
    (hy : ComputableInPolyTime y input encBits) :
    ComputableInPolyTime
      (fun (c : α) => Cslib.BitString.wordLt (x c) (y c)) input encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsWordLt α input x y hx hy

/-- Sum selected rows with a shrinking selector and an accumulator that never grows. -/
theorem bitsXorSelected :
    ComputableInPolyTime
      (fun (p : ℕ × List Bool × List (List Bool)) =>
        Cslib.BitString.listXorSelected p.1 p.2.1 p.2.2)
      (encPair encUnary
        (encPair encBits
          (encList encBits)))
      encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsXorSelected

/-- Variable-width XOR uses runtime lookup and ordinary Boolean folds. -/
theorem bitsXorWithInput
    {α : Type}
    {input : α ↪ List Bool}
    {width : α → ℕ}
    {words : α → List (List Bool)}
    (hwidth : ComputableInPolyTime width input encUnary)
    (hwords : ComputableInPolyTime words input
  (encList encBits)) :
    ComputableInPolyTime
      (fun (a : α) => Cslib.BitString.listXor (width a) (words a)) input
      encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsXorWithInput α input width words hwidth hwords

/-- Apply a fixed Boolean operation pointwise, stopping at the shorter word. -/
theorem bitsZipWith
    (op : Bool → Bool → Bool) :
    ComputableInPolyTime
      (fun (p : List Bool × List Bool) => List.zipWith op p.1 p.2)
      (encPair encBits encBits)
      encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsZipWith op

/-- Pointwise operations on computed words, with both intermediate encodings fixed. -/
theorem bitsZipWithInput
    {α : Type}
    {input : α ↪ List Bool}
    (op : Bool → Bool → Bool)
    {left right : α → List Bool}
    (hleft : ComputableInPolyTime left input encBits)
    (hright : ComputableInPolyTime right input encBits) :
    ComputableInPolyTime
      (fun (a : α) => List.zipWith op (left a) (right a)) input encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsZipWithInput α input op left right hleft hright

/-- Membership of a computed value in a computed list is decided by scanning the list for an equal
element. -/
theorem decide_mem
    {γ α : Type}
    {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool}
    {list : γ → List α}
    {value : γ → α}
    [inst_1 : (x : γ) → Decidable (value x ∈ list x)]
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hvalue : ComputableInPolyTime value encIn encA) :
    ComputableInPolyTime
      (fun (x : γ) => Decidable.decide (value x ∈ list x)) encIn encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.decide_mem γ α encIn encA list value inst_1 hlist hvalue

/-- Negation of an efficiently decidable proposition uses the standard Boolean encoding. -/
theorem decide_not
    {γ : Type}
    {encIn : γ ↪ List Bool}
    {p : γ → Prop}
    [inst_1 : (x : γ) → Decidable (p x)]
    (h : ComputableInPolyTime (fun (x : γ) => Decidable.decide (p x)) encIn
  encBool) :
    ComputableInPolyTime (fun (x : γ) => Decidable.decide ¬p x) encIn
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.decide_not γ encIn p inst_1 h

/-- Search every index up to the supplied unary bound, returning the greatest match or zero.
Both the bound and the predicate are certified uniformly in the original input. -/
theorem findGreatest
    {α : Type}
    {input : α ↪ List Bool}
    {bound : α → ℕ}
    {predicate : α → ℕ → Prop}
    [inst_1 : (a : α) → DecidablePred (predicate a)]
    (hbound : ComputableInPolyTime bound input encUnary)
    (hpredicate : ComputableInPolyTime
  (fun (p : α × ℕ) => Decidable.decide (predicate p.1 p.2))
  (encPair input encUnary)
  encBool) :
    ComputableInPolyTime
      (fun (a : α) => Nat.findGreatest (predicate a) (bound a)) input
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.findGreatest α input bound predicate inst_1 hbound
    hpredicate

/-- Concatenate captured raw bit strings over a framed list. The complete intermediate words
and their framing are charged before concatenation. Apply this rule explicitly: registering both
raw and framed `flatMap` outputs makes existing enumeration proof search exceed its limit. -/
theorem flatMapToBitsWithInput
    {α : Type}
    {input : α ↪ List Bool}
    {β : Type}
    {enc : β ↪ List Bool}
    {list : α → List β}
    {f : α → β → List Bool}
    (hlist : ComputableInPolyTime list input (encList enc))
    (hf : ComputableInPolyTime (fun (p : α × β) => f p.1 p.2)
  (encPair input enc) encBits) :
    ComputableInPolyTime (fun (a : α) => List.flatMap (f a) (list a))
      input encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.flatMapToBitsWithInput α input β enc list f hlist hf

/-- Addition of binary integers, by cases on the signs of the summands. -/
theorem intBin_add :
    ComputableInPolyTime (fun (p : ℤ × ℤ) => p.1 + p.2)
      (encPair encIntBin encIntBin)
      encIntBin := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_add

/-- Add computed binary integers, fixing their intermediate encodings for proof search. -/
theorem intBin_add'
    {α : Type}
    {input : α ↪ List Bool}
    {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun (a : α) => left a + right a) input
      encIntBin := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_add' α input left right hleft hright

/-- Reduce a signed binary integer modulo a binary natural. At modulus zero the result is
the integer truncated at zero; no positive-modulus hypothesis is required. -/
theorem intBin_emodNat :
    ComputableInPolyTime (fun (p : ℤ × ℕ) => (p.1 % (↑p.2 : ℤ)).toNat)
      (encPair encIntBin encNat)
      encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_emodNat

/-- Reduce computed signed integers by computed binary natural moduli, fixing the intermediate
encodings for proof search. -/
theorem intBin_emodNat'
    {α : Type}
    {input : α ↪ List Bool}
    {value : α → ℤ}
    {modulus : α → ℕ}
    (hvalue : ComputableInPolyTime value input encIntBin)
    (hmodulus : ComputableInPolyTime modulus input encNat) :
    ComputableInPolyTime
      (fun (a : α) => (value a % (↑(modulus a) : ℤ)).toNat) input encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_emodNat' α input value modulus hvalue hmodulus

/-- The sign of a binary integer: whether it is negative. -/
theorem intBin_isNeg :
    ComputableInPolyTime (fun (z : ℤ) => Decidable.decide (z < 0))
      encIntBin encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_isNeg

/-- Test whether a binary integer is positive. -/
theorem intBin_isPos :
    ComputableInPolyTime (fun (z : ℤ) => Decidable.decide (0 < z))
      encIntBin encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_isPos

/-- Test whether a binary integer is zero: its magnitude has no digits. -/
theorem intBin_isZero :
    ComputableInPolyTime (fun (z : ℤ) => Decidable.decide (z = 0))
      encIntBin encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_isZero

/-- Comparison of binary integers. -/
theorem intBin_le :
    ComputableInPolyTime
      (fun (p : ℤ × ℤ) => Decidable.decide (p.1 ≤ p.2))
      (encPair encIntBin encIntBin)
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_le

/-- Compare computed binary integers, fixing their intermediate encodings. -/
theorem intBin_le'
    {α : Type}
    {input : α ↪ List Bool}
    {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime
      (fun (a : α) => Decidable.decide (left a ≤ right a)) input encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_le' α input left right hleft hright

/-- Strict comparison of binary integers, through the sign of their difference. -/
theorem intBin_lt :
    ComputableInPolyTime
      (fun (p : ℤ × ℤ) => Decidable.decide (p.1 < p.2))
      (encPair encIntBin encIntBin)
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_lt

/-- Strictly compare computed binary integers, fixing their intermediate encodings. -/
theorem intBin_lt'
    {α : Type}
    {input : α ↪ List Bool}
    {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime
      (fun (a : α) => Decidable.decide (left a < right a)) input encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_lt' α input left right hleft hright

/-- Multiplication of binary integers: the magnitudes multiply, and the product is negative when
exactly one factor is. -/
theorem intBin_mul :
    ComputableInPolyTime (fun (p : ℤ × ℤ) => p.1 * p.2)
      (encPair encIntBin encIntBin)
      encIntBin := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_mul

/-- Multiply computed binary integers, fixing their intermediate encodings. -/
theorem intBin_mul'
    {α : Type}
    {input : α ↪ List Bool}
    {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun (a : α) => left a * right a) input
      encIntBin := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_mul' α input left right hleft hright

/-- The magnitude of a binary integer, as a binary natural. -/
theorem intBin_natAbs :
    ComputableInPolyTime Int.natAbs encIntBin
      encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_natAbs

/-- A binary natural as a binary integer. -/
theorem intBin_natCast :
    ComputableInPolyTime (fun (n : ℕ) => (↑n : ℤ))
      encNat encIntBin := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_natCast

/-- Negation of binary integers flips the sign of a nonzero magnitude. -/
theorem intBin_neg :
    ComputableInPolyTime (fun (z : ℤ) => -z) encIntBin
      encIntBin := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_neg

/-- A power of a binary integer to a unary exponent, by repeated multiplication. -/
theorem intBin_pow :
    ComputableInPolyTime (fun (p : ℤ × ℕ) => p.1 ^ p.2)
      (encPair encIntBin encUnary)
      encIntBin := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_pow

/-- Raise a computed binary integer to a computed unary exponent, fixing the intermediate
encodings. -/
theorem intBin_pow'
    {α : Type}
    {input : α ↪ List Bool}
    {base : α → ℤ}
    {exponent : α → ℕ}
    (hbase : ComputableInPolyTime base input encIntBin)
    (hexponent : ComputableInPolyTime exponent input encUnary) :
    ComputableInPolyTime (fun (a : α) => base a ^ exponent a) input
      encIntBin := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_pow' α input base exponent hbase hexponent

/-- The product of a list of binary integers, by a left fold of binary multiplications. -/
theorem intBin_prod :
    ComputableInPolyTime List.prod
      (encList encIntBin) encIntBin := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_prod

/-- Multiply a uniformly computed family of binary integers over a computed unary range. -/
theorem intBin_prod_range
    {α : Type}
    {enc : α ↪ List Bool}
    {f : α × ℕ → ℤ}
    {r : α → ℕ}
    (hf : ComputableInPolyTime f
  (encPair enc encUnary)
  encIntBin)
    (hr : ComputableInPolyTime r enc encUnary) :
    ComputableInPolyTime
      (fun (a : α) => ∏ i ∈ Finset.range (r a), f (a, i)) enc encIntBin := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_prod_range α enc f r hf hr

/-- The sign of a binary integer, as a binary integer. -/
theorem intBin_sign :
    ComputableInPolyTime Int.sign encIntBin
      encIntBin := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_sign

/-- Assemble a binary integer from a sign and a binary magnitude. A negative sign on a zero
magnitude is dropped, so the code stays unique. -/
theorem intBin_signMagnitude :
    ComputableInPolyTime
      (fun (p : Bool × ℕ) => if p.1 = Bool.true then -(↑p.2 : ℤ) else (↑p.2 : ℤ))
      (encPair encBool encNat)
      encIntBin := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_signMagnitude

/-- Subtraction of binary integers, as addition of the negation. -/
theorem intBin_sub :
    ComputableInPolyTime (fun (p : ℤ × ℤ) => p.1 - p.2)
      (encPair encIntBin encIntBin)
      encIntBin := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_sub

/-- Subtract computed binary integers, fixing their intermediate encodings. -/
theorem intBin_sub'
    {α : Type}
    {input : α ↪ List Bool}
    {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun (a : α) => left a - right a) input
      encIntBin := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_sub' α input left right hleft hright

/-- The sum of a list of binary integers, by a left fold of binary additions. -/
theorem intBin_sum :
    ComputableInPolyTime List.sum
      (encList encIntBin) encIntBin := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_sum

/-- Truncate a binary integer at zero, as a binary natural. -/
theorem intBin_toNat :
    ComputableInPolyTime Int.toNat encIntBin
      encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.intBin_toNat

/-- Compare a signed unary position's magnitude with a unary window bound. -/
theorem int_abs_le_nat :
    ComputableInPolyTime
      (fun (p : ℤ × ℕ) => Decidable.decide (|p.1| ≤ (↑p.2 : ℤ)))
      (encPair encInt encUnary)
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.int_abs_le_nat

/-- Test window membership after computing the signed position and unary bound. -/
theorem int_abs_le_nat'
    {α : Type}
    {input : α ↪ List Bool}
    {position : α → ℤ}
    {bound : α → ℕ}
    (hposition : ComputableInPolyTime position input encInt)
    (hbound : ComputableInPolyTime bound input encUnary) :
    ComputableInPolyTime
      (fun (a : α) => Decidable.decide (|position a| ≤ (↑(bound a) : ℤ))) input
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.int_abs_le_nat' α input position bound hposition hbound

/-- Number signed integers by `0, -1, 1, -2, …`, returning the index in unary. -/
theorem int_equivNat :
    ComputableInPolyTime (⇑Equiv.intEquivNat : ℤ → ℕ)
      encInt encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.int_equivNat

/-- Return the magnitude in unary, accounting for the offset in negative encodings. -/
theorem int_natAbs :
    ComputableInPolyTime Int.natAbs encInt
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.int_natAbs

/-- Interpret a unary natural as a nonnegative signed integer. -/
theorem int_natCast :
    ComputableInPolyTime (fun (n : ℕ) => (↑n : ℤ))
      encUnary encInt := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.int_natCast

/-- Subtract unary naturals without truncating at zero. -/
theorem int_natCast_sub :
    ComputableInPolyTime (fun (p : ℕ × ℕ) => (↑p.1 : ℤ) - (↑p.2 : ℤ))
      (encPair encUnary encUnary)
      encInt := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.int_natCast_sub

/-- Test whether a signed unary integer is negative. -/
theorem int_neg :
    ComputableInPolyTime (fun (z : ℤ) => Decidable.decide (z < 0))
      encInt encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.int_neg

/-- Construct `-(n + 1)` from a unary natural `n`. -/
theorem int_negSucc :
    ComputableInPolyTime Int.negSucc encUnary
      encInt := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.int_negSucc

/-- Test whether a signed unary integer is positive. -/
theorem int_pos :
    ComputableInPolyTime (fun (z : ℤ) => Decidable.decide (0 < z))
      encInt encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.int_pos

/-- Shift a signed unary integer one cell to the left. -/
theorem int_pred :
    ComputableInPolyTime (fun (z : ℤ) => z - 1) encInt
      encInt := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.int_pred

/-- Subtract a fixed tape direction from a signed unary position. -/
theorem int_sub_sign
    (direction : SignType) :
    ComputableInPolyTime (fun (z : ℤ) => z - (↑direction : ℤ))
      encInt encInt := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.int_sub_sign direction

/-- Shift a signed unary integer one cell to the right. -/
theorem int_succ :
    ComputableInPolyTime (fun (z : ℤ) => z + 1) encInt
      encInt := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.int_succ

/-- Truncate a signed integer at zero and return the result in unary. -/
theorem int_toNat :
    ComputableInPolyTime Int.toNat encInt
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.int_toNat

/-- Remove the framing from a list of bits. -/
theorem listToBits :
    ComputableInPolyTime (fun (l : List Bool) => l)
      (encList encBool) encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.listToBits

/-- Map a captured Boolean-valued function over a framed list, emitting a raw bit string. -/
theorem mapToBitsWithInput
    {α : Type}
    {input : α ↪ List Bool}
    {β : Type}
    {enc : β ↪ List Bool}
    {list : α → List β}
    {f : α → β → Bool}
    (hlist : ComputableInPolyTime list input (encList enc))
    (hf : ComputableInPolyTime (fun (p : α × β) => f p.1 p.2)
  (encPair input enc) encBool) :
    ComputableInPolyTime (fun (a : α) => List.map (f a) (list a)) input
      encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.mapToBitsWithInput α input β enc list f hlist hf

/-- The binary digits of a natural number, as a raw bit string. -/
theorem natBits :
    ComputableInPolyTime Nat.bits encNat
      encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.natBits

/-- Ceiling logarithms in any fixed base are polynomial-time on unary counters. -/
theorem unary_clog_const
    (base : ℕ) :
    ComputableInPolyTime (Nat.clog base) encUnary
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_clog_const base

/-- Primality of a unary natural, by trial division. -/
theorem unary_decide_prime :
    ComputableInPolyTime (fun (p : ℕ) => Decidable.decide (Nat.Prime p))
      encUnary encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_decide_prime

/-- Division of two unary counters. -/
theorem unary_div :
    ComputableInPolyTime (fun (p : ℕ × ℕ) => p.1 / p.2)
      (encPair encUnary encUnary)
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_div

/-- Compute both quotient and remainder with a runtime unary divisor. Division by zero returns
`(0, dividend)`, matching Lean's conventions. All intermediate counters have linear size. -/
theorem unary_divMod :
    ComputableInPolyTime (fun (p : ℕ × ℕ) => (p.1 / p.2, p.1 % p.2))
      (encPair encUnary encUnary)
      (encPair encUnary encUnary) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_divMod

/-- Division by a fixed natural is a special case of runtime unary division. -/
theorem unary_div_const
    (divisor : ℕ) :
    ComputableInPolyTime (fun (n : ℕ) => n / divisor)
      encUnary encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_div_const divisor

/-- Normalize a unary index into a fixed positive finite range, using any fixed output encoding. -/
theorem unary_finMod
    {bound : ℕ}
    (hbound : 0 < bound)
    (output : Fin bound ↪ List Bool) :
    ComputableInPolyTime
      (fun (index : ℕ) => ⟨index % bound, Nat.mod_lt index hbound⟩)
      encUnary output := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_finMod bound hbound output

/-- Fixed-base logarithms are polynomial-time on unary counters, including bases zero and one.
The division loop maintains the logarithm identity and a linear bound on its complete state. -/
theorem unary_log_const
    (base : ℕ) :
    ComputableInPolyTime (Nat.log base) encUnary
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_log_const base

/-- The base-two logarithm is polynomial-time with both input and output in unary. -/
theorem unary_log_two :
    ComputableInPolyTime (Nat.log 2) encUnary
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_log_two

/-- Remainder of two unary counters. -/
theorem unary_mod :
    ComputableInPolyTime (fun (p : ℕ × ℕ) => p.1 % p.2)
      (encPair encUnary encUnary)
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_mod

/-- Given an efficient unary size function, a fixed factor raised to its fixed-base ceiling
logarithm has a polynomial-time unary output in the caller's original encoding. The bound
charges
every intermediate power, including the initial one when the factor is zero. -/
theorem unary_pow_clog_const
    {α : Type}
    {input : α ↪ List Bool}
    {size : α → ℕ}
    (hsize : ComputableInPolyTime size input encUnary)
    (factor base : ℕ) :
    ComputableInPolyTime (fun (x : α) => factor ^ Nat.clog base (size x))
      input encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_pow_clog_const α input size hsize factor base

end Turing.MultiTapeTM.ComputableInPolyTime



attribute [fun_prop] ComputableInPolyTime.bitsFrame
attribute [fun_prop] ComputableInPolyTime.bitsBoundedBinaryValue
attribute [fun_prop] ComputableInPolyTime.bitsBoundedBinaryValueWithInput
attribute [fun_prop] ComputableInPolyTime.bitsGetElem?
attribute [fun_prop] ComputableInPolyTime.bitsReplicate
attribute [fun_prop] ComputableInPolyTime.bitsFlatten
attribute [fun_prop] ComputableInPolyTime.bitsPadWord
attribute [fun_prop] ComputableInPolyTime.mapToBitsWithInput
attribute [fun_prop] ComputableInPolyTime.bitsLow
attribute [fun_prop] ComputableInPolyTime.bitsMapWithInput
attribute [fun_prop] ComputableInPolyTime.bitsFilterWithInput
attribute [fun_prop] ComputableInPolyTime.bitsCountPWithInput
attribute [fun_prop] ComputableInPolyTime.bitsCountWithInput
attribute [fun_prop] ComputableInPolyTime.bitsAnyWithInput
attribute [fun_prop] ComputableInPolyTime.bitsAllWithInput
attribute [fun_prop] ComputableInPolyTime.bitsFoldlWithInput
attribute [fun_prop] ComputableInPolyTime.bitsZipWith
attribute [fun_prop] ComputableInPolyTime.bitsZipWithInput
attribute [fun_prop] ComputableInPolyTime.bitsStrictMajority
attribute [fun_prop] ComputableInPolyTime.bitsStrictMajorityWithInput
attribute [fun_prop] ComputableInPolyTime.bitsNonpositiveMarginWithInput
attribute [fun_prop] ComputableInPolyTime.bitsSingle
attribute [fun_prop] ComputableInPolyTime.bitsSingles
attribute [fun_prop] ComputableInPolyTime.bitsXorSelected
attribute [fun_prop] ComputableInPolyTime.bitsRowWithInput
attribute [fun_prop] ComputableInPolyTime.bitsRowsWithInput
attribute [fun_prop] ComputableInPolyTime.bitsXorWithInput
attribute [fun_prop] ComputableInPolyTime.bitsWordLt
attribute [fun_prop] ComputableInPolyTime.bitsBinaryValue
attribute [fun_prop] ComputableInPolyTime.int_natCast
attribute [fun_prop] ComputableInPolyTime.int_negSucc
attribute [fun_prop] ComputableInPolyTime.int_natCast_sub
attribute [fun_prop] ComputableInPolyTime.int_succ
attribute [fun_prop] ComputableInPolyTime.int_pred
attribute [fun_prop] ComputableInPolyTime.int_pos
attribute [fun_prop] ComputableInPolyTime.int_neg
attribute [fun_prop] ComputableInPolyTime.int_toNat
attribute [fun_prop] ComputableInPolyTime.int_natAbs
attribute [fun_prop] ComputableInPolyTime.int_sub_sign
attribute [fun_prop] ComputableInPolyTime.int_abs_le_nat
attribute [fun_prop] ComputableInPolyTime.int_abs_le_nat'
attribute [fun_prop] ComputableInPolyTime.int_equivNat
attribute [fun_prop] ComputableInPolyTime.decide_not
attribute [fun_prop] ComputableInPolyTime.decide_mem
attribute [fun_prop] ComputableInPolyTime.bitsToNat
attribute [fun_prop] ComputableInPolyTime.natBits
attribute [fun_prop] ComputableInPolyTime.binary_add
attribute [fun_prop] ComputableInPolyTime.binary_mul
attribute [fun_prop] ComputableInPolyTime.binary_add'
attribute [fun_prop] ComputableInPolyTime.binary_sum
attribute [fun_prop] ComputableInPolyTime.binary_two_pow
attribute [fun_prop] ComputableInPolyTime.binary_lt
attribute [fun_prop] ComputableInPolyTime.binary_le
attribute [fun_prop] ComputableInPolyTime.binary_lt'
attribute [fun_prop] ComputableInPolyTime.binary_le'
attribute [fun_prop] ComputableInPolyTime.binary_mul'
attribute [fun_prop] ComputableInPolyTime.binary_pow
attribute [fun_prop] ComputableInPolyTime.binary_pow'
attribute [fun_prop] ComputableInPolyTime.binary_sub
attribute [fun_prop] ComputableInPolyTime.binary_sub'
attribute [fun_prop] ComputableInPolyTime.binary_testBit
attribute [fun_prop] ComputableInPolyTime.intBin_isNeg
attribute [fun_prop] ComputableInPolyTime.intBin_natAbs
attribute [fun_prop] ComputableInPolyTime.intBin_signMagnitude
attribute [fun_prop] ComputableInPolyTime.intBin_natCast
attribute [fun_prop] ComputableInPolyTime.intBin_neg
attribute [fun_prop] ComputableInPolyTime.intBin_add
attribute [fun_prop] ComputableInPolyTime.intBin_mul
attribute [fun_prop] ComputableInPolyTime.intBin_sub
attribute [fun_prop] ComputableInPolyTime.intBin_isZero
attribute [fun_prop] ComputableInPolyTime.intBin_isPos
attribute [fun_prop] ComputableInPolyTime.intBin_sign
attribute [fun_prop] ComputableInPolyTime.intBin_toNat
attribute [fun_prop] ComputableInPolyTime.intBin_lt
attribute [fun_prop] ComputableInPolyTime.intBin_le
attribute [fun_prop] ComputableInPolyTime.intBin_pow
attribute [fun_prop] ComputableInPolyTime.intBin_sum
attribute [fun_prop] ComputableInPolyTime.intBin_prod
attribute [fun_prop] ComputableInPolyTime.intBin_add'
attribute [fun_prop] ComputableInPolyTime.intBin_sub'
attribute [fun_prop] ComputableInPolyTime.intBin_mul'
attribute [fun_prop] ComputableInPolyTime.intBin_pow'
attribute [fun_prop] ComputableInPolyTime.intBin_lt'
attribute [fun_prop] ComputableInPolyTime.intBin_le'
attribute [fun_prop] ComputableInPolyTime.intBin_prod_range
attribute [fun_prop] ComputableInPolyTime.binary_div
attribute [fun_prop] ComputableInPolyTime.binary_mod
attribute [fun_prop] ComputableInPolyTime.binary_div'
attribute [fun_prop] ComputableInPolyTime.binary_mod'
attribute [fun_prop] ComputableInPolyTime.intBin_emodNat
attribute [fun_prop] ComputableInPolyTime.intBin_emodNat'
attribute [fun_prop] ComputableInPolyTime.unary_div
attribute [fun_prop] ComputableInPolyTime.unary_mod
attribute [fun_prop] ComputableInPolyTime.unary_div_const
attribute [fun_prop] ComputableInPolyTime.binary_factorial
attribute [fun_prop] ComputableInPolyTime.unary_finMod
attribute [fun_prop] ComputableInPolyTime.binary_gcd
attribute [fun_prop] ComputableInPolyTime.binary_gcd'
attribute [fun_prop] ComputableInPolyTime.binary_log_two
attribute [fun_prop] ComputableInPolyTime.unary_log_two
attribute [fun_prop] ComputableInPolyTime.unary_log_const
attribute [fun_prop] ComputableInPolyTime.unary_clog_const
attribute [fun_prop] ComputableInPolyTime.unary_pow_clog_const
attribute [fun_prop] ComputableInPolyTime.unary_decide_prime
attribute [fun_prop] ComputableInPolyTime.findGreatest
attribute [fun_prop] ComputableInPolyTime.bitsToList
attribute [fun_prop] ComputableInPolyTime.listToBits
