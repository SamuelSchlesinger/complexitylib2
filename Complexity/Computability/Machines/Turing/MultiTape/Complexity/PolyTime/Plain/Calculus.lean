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

/-- Test every element of a fixed list. Only its members need certificates; the list and its
elements are fixed before the computational input and require no encoding. -/
theorem allConst.{u_1}
    {γ : Type}
    {encIn : γ ↪ List Bool}
    {ι : Type u_1}
    (l : List ι)
    {test : γ → ι → Bool}
    (htest : ∀ i ∈ l,
  ComputableInPolyTime (fun (x : γ) => test x i) encIn
    encBool) :
    ComputableInPolyTime (fun (x : γ) => l.all (test x)) encIn
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.allConst γ encIn ι l test htest

/-- Test whether every element satisfies a polynomial-time predicate with a fixed parameter. -/
theorem allWith
    {α γ π : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {encP : π ↪ List Bool}
    {test : π × α → Bool}
    {par : γ → π}
    {list : γ → List α}
    (htest : ComputableInPolyTime test (encPair encP encA)
  encBool)
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime
      (fun (x : γ) => (list x).all fun (a : α) => test (par x, a)) encIn
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.allWith α γ π encA encIn encP test par list htest hpar hlist

/-- Test every element of any readable, size-bounded list encoding. -/
theorem allWithEncoding
    {α γ π : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {encP : π ↪ List Bool}
    {encL : List α ↪ List Bool}
    [inst_1 : ListEncoding encA encL]
    [inst_2 : SizedListEncoding encA encL]
    {test : π × α → Bool}
    {par : γ → π}
    {list : γ → List α}
    (htest : ComputableInPolyTime test (encPair encP encA)
  encBool)
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn encL) :
    ComputableInPolyTime
      (fun (x : γ) => (list x).all fun (a : α) => test (par x, a)) encIn
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.allWithEncoding α γ π encA encIn encP encL inst_1 inst_2
    test par list htest hpar hlist

/-- Test whether every list element satisfies a predicate that captures the original input. -/
theorem allWithInput
    {α γ : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {test : γ → α → Bool}
    {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (htest : ComputableInPolyTime (fun (p : γ × α) => test p.1 p.2)
  (encPair encIn encA) encBool) :
    ComputableInPolyTime (fun (x : γ) => (list x).all (test x)) encIn
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.allWithInput α γ encA encIn test list hlist htest

/-- Test whether any element of a fixed list satisfies its input-dependent predicate.
The fixed list needs no element encoding or uniform certificate over all possible elements. -/
theorem anyConst.{u_1}
    {γ : Type}
    {encIn : γ ↪ List Bool}
    {ι : Type u_1}
    (l : List ι)
    {test : γ → ι → Bool}
    (htest : ∀ i ∈ l,
  ComputableInPolyTime (fun (x : γ) => test x i) encIn
    encBool) :
    ComputableInPolyTime (fun (x : γ) => l.any (test x)) encIn
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.anyConst γ encIn ι l test htest

/-- Test whether any element satisfies a polynomial-time predicate with a fixed parameter. -/
theorem anyWith
    {α γ π : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {encP : π ↪ List Bool}
    {test : π × α → Bool}
    {par : γ → π}
    {list : γ → List α}
    (htest : ComputableInPolyTime test (encPair encP encA)
  encBool)
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime
      (fun (x : γ) => (list x).any fun (a : α) => test (par x, a)) encIn
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.anyWith α γ π encA encIn encP test par list htest hpar hlist

/-- Scan any readable, size-bounded list encoding for a predicate match. -/
theorem anyWithEncoding
    {α γ π : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {encP : π ↪ List Bool}
    {encL : List α ↪ List Bool}
    [inst_1 : ListEncoding encA encL]
    [inst_2 : SizedListEncoding encA encL]
    {test : π × α → Bool}
    {par : γ → π}
    {list : γ → List α}
    (htest : ComputableInPolyTime test (encPair encP encA)
  encBool)
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn encL) :
    ComputableInPolyTime
      (fun (x : γ) => (list x).any fun (a : α) => test (par x, a)) encIn
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.anyWithEncoding α γ π encA encIn encP encL inst_1 inst_2
    test par list htest hpar hlist

/-- Test whether any list element satisfies a predicate that captures the original input. -/
theorem anyWithInput
    {α γ : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {test : γ → α → Bool}
    {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (htest : ComputableInPolyTime (fun (p : γ × α) => test p.1 p.2)
  (encPair encIn encA) encBool) :
    ComputableInPolyTime (fun (x : γ) => (list x).any (test x)) encIn
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.anyWithInput α γ encA encIn test list hlist htest

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

/-- Concatenate raw bit strings, charging for both computed words. -/
theorem bitsAppend
    {γ : Type}
    {encIn : γ ↪ List Bool}
    {left right : γ → List Bool}
    (hleft : ComputableInPolyTime left encIn encBits)
    (hright : ComputableInPolyTime right encIn encBits) :
    ComputableInPolyTime (fun (x : γ) => left x ++ right x) encIn
      encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsAppend γ encIn left right hleft hright

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

/-- Prepend a computed bit to a raw bit string. -/
theorem bitsCons
    {γ : Type}
    {encIn : γ ↪ List Bool}
    {head : γ → Bool}
    {tail : γ → List Bool}
    (hhead : ComputableInPolyTime head encIn encBool)
    (htail : ComputableInPolyTime tail encIn encBits) :
    ComputableInPolyTime (fun (x : γ) => head x :: tail x) encIn
      encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsCons γ encIn head tail hhead htail

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

/-- Drop a computed unary number of bits from a computed bit string. -/
theorem bitsDropWithInput
    {γ : Type}
    {encIn : γ ↪ List Bool}
    {list : γ → List Bool}
    {count : γ → ℕ}
    (hlist : ComputableInPolyTime list encIn encBits)
    (hcount : ComputableInPolyTime count encIn encUnary) :
    ComputableInPolyTime (fun (x : γ) => List.drop (count x) (list x))
      encIn encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsDropWithInput γ encIn list count hlist hcount

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

/-- Read a bit at a unary index with a fixed fallback. Fixing the raw encoding avoids
guessing a list-encoding instance during compositional proof search. -/
theorem bitsGetD
    (fallback : Bool) :
    ComputableInPolyTime
      (fun (p : List Bool × ℕ) => p.1.getD p.2 fallback)
      (encPair encBits encUnary)
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsGetD fallback

/-- Read a computed bit string at a computed unary index. -/
theorem bitsGetDWithInput
    {γ : Type}
    {encIn : γ ↪ List Bool}
    {list : γ → List Bool}
    {index : γ → ℕ}
    (hlist : ComputableInPolyTime list encIn encBits)
    (hindex : ComputableInPolyTime index encIn encUnary)
    (fallback : Bool) :
    ComputableInPolyTime
      (fun (x : γ) => (list x).getD (index x) fallback) encIn encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsGetDWithInput γ encIn list index hlist hindex fallback

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

/-- Test a raw bit string's emptiness using the standard Boolean element encoding. -/
theorem bitsIsEmpty :
    ComputableInPolyTime List.isEmpty encBits
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsIsEmpty

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

/-- Reverse a raw bit string using an accumulator that grows by one bit per step. -/
theorem bitsReverse :
    ComputableInPolyTime List.reverse encBits
      encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsReverse

/-- Reverse a computed word, fixing its raw intermediate encoding before proof search.
The input certificate may itself convert from another representation. -/
theorem bitsReverseWithInput
    {γ : Type}
    {encIn : γ ↪ List Bool}
    {word : γ → List Bool}
    (hword : ComputableInPolyTime word encIn encBits) :
    ComputableInPolyTime (fun (a : γ) => (word a).reverse) encIn
      encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsReverseWithInput γ encIn word hword

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

/-- Drop the first raw bit. The raw encoding fixes the otherwise undetermined element encoding. -/
theorem bitsTail :
    ComputableInPolyTime List.tail encBits
      encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsTail

/-- Take a unary number of bits. Reversing and dropping reuses the certified list operations. -/
theorem bitsTake :
    ComputableInPolyTime (fun (p : List Bool × ℕ) => List.take p.2 p.1)
      (encPair encBits encUnary)
      encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsTake

/-- Take a computed unary number of bits from a computed bit string. -/
theorem bitsTakeWithInput
    {γ : Type}
    {encIn : γ ↪ List Bool}
    {list : γ → List Bool}
    {count : γ → ℕ}
    (hlist : ComputableInPolyTime list encIn encBits)
    (hcount : ComputableInPolyTime count encIn encUnary) :
    ComputableInPolyTime (fun (x : γ) => List.take (count x) (list x))
      encIn encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bitsTakeWithInput γ encIn list count hlist hcount

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

/-- Interpret one Boolean as a unary zero or one. -/
theorem bool_toUnary :
    ComputableInPolyTime Bool.toNat encBool
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.bool_toUnary

/-- Prepending an element to a framed list is polynomial-time. -/
theorem cons
    {α : Type}
    (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun (p : α × List α) => p.1 :: p.2)
      (encPair enc (encList enc))
      (encList enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.cons α enc

/-- Prepend computed data. The result encoding determines the element encoding before
`fun_prop` searches for the two component certificates. -/
theorem cons'
    {α γ : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {head : γ → α}
    {tail : γ → List α}
    (hhead : ComputableInPolyTime head encIn encA)
    (htail : ComputableInPolyTime tail encIn (encList encA)) :
    ComputableInPolyTime (fun (x : γ) => head x :: tail x) encIn
      (encList encA) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.cons' α γ encA encIn head tail hhead htail

/-- Count predicate matches directly over any readable, size-bounded list encoding.
The accumulator is a unary counter; the certificate does not construct a list of matches. -/
theorem countPWith
    {α γ π : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {encP : π ↪ List Bool}
    {encL : List α ↪ List Bool}
    [inst_1 : ListEncoding encA encL]
    [inst_2 : SizedListEncoding encA encL]
    {test : π × α → Bool}
    {par : γ → π}
    {list : γ → List α}
    (htest : ComputableInPolyTime test (encPair encP encA)
  encBool)
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn encL) :
    ComputableInPolyTime
      (fun (x : γ) => List.countP (fun (a : α) => test (par x, a)) (list x)) encIn
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.countPWith α γ π encA encIn encP encL inst_1 inst_2 test par
    list htest hpar hlist

/-- Count matches of a predicate that captures the original input. The count is in unary. -/
theorem countPWithInput
    {α γ : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {test : γ → α → Bool}
    {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (htest : ComputableInPolyTime (fun (p : γ × α) => test p.1 p.2)
  (encPair encIn encA) encBool) :
    ComputableInPolyTime (fun (x : γ) => List.countP (test x) (list x))
      encIn encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.countPWithInput α γ encA encIn test list hlist htest

/-- Count occurrences of a computed value using lawful Boolean equality. -/
theorem countWithInput
    {α γ : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    [inst_1 : BEq α]
    [inst_2 : LawfulBEq α]
    {list : γ → List α}
    {value : γ → α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hvalue : ComputableInPolyTime value encIn encA) :
    ComputableInPolyTime (fun (x : γ) => List.count (value x) (list x))
      encIn encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.countWithInput α γ encA encIn inst_1 inst_2 list value hlist
    hvalue

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

/-- Construct a fixed dependent family, retaining the original input for each entry. -/
theorem dpi
    {α Index : Type}
    {Value : Index → Type}
    [inst_1 : Fintype Index]
    {input : α ↪ List Bool}
    {enc : (i : Index) → Value i ↪ List Bool}
    {values : α → (i : Index) → Value i}
    (hvalues : ∀ (i : Index),
  ComputableInPolyTime (fun (a : α) => values a i) input (enc i)) :
    ComputableInPolyTime values input (encDPi enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.dpi α Index Value inst_1 input enc values hvalues

/-- Read a fixed dependent-table entry, charging the stored prefix and requiring no default. -/
theorem dpi_apply
    {Index : Type}
    {Value : Index → Type}
    [inst_1 : Fintype Index]
    (enc : (i : Index) → Value i ↪ List Bool)
    (i : Index) :
    ComputableInPolyTime
      (fun (values : (j : Index) → Value j) => values i) (encDPi enc)
      (enc i) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.dpi_apply Index Value inst_1 enc i

/-- Update one dependent-table entry while retaining and charging all other entries. -/
theorem dpi_update
    {α Index : Type}
    {Value : Index → Type}
    [inst_1 : Fintype Index]
    {input : α ↪ List Bool}
    {enc : (i : Index) → Value i ↪ List Bool}
    [inst_2 : DecidableEq Index]
    {values : α → (i : Index) → Value i}
    {i : Index}
    {value : α → Value i}
    (hvalues : ComputableInPolyTime values input (encDPi enc))
    (hvalue : ComputableInPolyTime value input (enc i)) :
    ComputableInPolyTime
      (fun (a : α) => Function.update (values a) i (value a)) input
      (encDPi enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.dpi_update α Index Value inst_1 input enc inst_2 values i
    value hvalues hvalue

/-- Drop a unary number of elements from a sized list encoding, including raw bit strings. -/
theorem dropUnary
    {α : Type}
    {encA : α ↪ List Bool}
    {encL : List α ↪ List Bool}
    [inst_1 : ListEncoding encA encL]
    [inst_2 : SizedListEncoding encA encL] :
    ComputableInPolyTime (fun (p : List α × ℕ) => List.drop p.2 p.1)
      (encPair encL encUnary) encL := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.dropUnary α encA encL inst_1 inst_2

/-- The encoded input length, computed in unary by reading the input word. -/
theorem encoding_length
    {α : Type}
    (enc : α ↪ List Bool) :
    ComputableInPolyTime
      (fun (a : α) => ((enc : α → List Bool) a).length) enc encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.encoding_length α enc

/-- Filtering a list by a polynomial-time test is polynomial-time. -/
theorem filter
    {α : Type}
    {encA : α ↪ List Bool}
    {test : α → Bool}
    (htest : ComputableInPolyTime test encA encBool) :
    ComputableInPolyTime (List.filter test)
      (encList encA) (encList encA) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.filter α encA test htest

/-- Keep the elements passing a polynomial-time test with a fixed parameter.
The input list may have any polynomial encoded length. -/
theorem filterWith
    {α γ π : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {encP : π ↪ List Bool}
    {test : π × α → Bool}
    {par : γ → π}
    {list : γ → List α}
    (htest : ComputableInPolyTime test (encPair encP encA)
  encBool)
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime
      (fun (x : γ) => List.filter (fun (a : α) => test (par x, a)) (list x)) encIn
      (encList encA) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.filterWith α γ π encA encIn encP test par list htest hpar
    hlist

/-- Filter with a predicate that captures the original input. -/
theorem filterWithInput
    {α γ : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {test : γ → α → Bool}
    {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (htest : ComputableInPolyTime (fun (p : γ × α) => test p.1 p.2)
  (encPair encIn encA) encBool) :
    ComputableInPolyTime (fun (x : γ) => List.filter (test x) (list x))
      encIn (encList encA) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.filterWithInput α γ encA encIn test list hlist htest

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

/-- Find the first element passing a polynomial-time test with a fixed parameter.
The list may have any polynomial encoded length. -/
theorem findWith
    {α γ π : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {encP : π ↪ List Bool}
    {test : π × α → Bool}
    {par : γ → π}
    {list : γ → List α}
    (htest : ComputableInPolyTime test (encPair encP encA)
  encBool)
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime
      (fun (x : γ) => List.find? (fun (a : α) => test (par x, a)) (list x)) encIn
      (encOption encA) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.findWith α γ π encA encIn encP test par list htest hpar
    hlist

/-- Search with a predicate that captures the original input. -/
theorem findWithInput
    {α γ : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {test : γ → α → Bool}
    {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (htest : ComputableInPolyTime (fun (p : γ × α) => test p.1 p.2)
  (encPair encIn encA) encBool) :
    ComputableInPolyTime (fun (x : γ) => List.find? (test x) (list x))
      encIn (encOption encA) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.findWithInput α γ encA encIn test list hlist htest

/-- A fixed finite tag selects a certified branch, charging the tag and captured input.
Neither the tag nor the result type requires a default inhabitant. -/
theorem finite_cases
    {α β Tag : Type}
    [inst_1 : Finite Tag]
    {input : α ↪ List Bool}
    {output : β ↪ List Bool}
    {tagEncoding : Tag ↪ List Bool}
    {tag : α → Tag}
    {branch : Tag → α → β}
    (htag : ComputableInPolyTime tag input tagEncoding)
    (hbranch : ∀ (choice : Tag), ComputableInPolyTime (branch choice) input output) :
    ComputableInPolyTime (fun (a : α) => branch (tag a) a) input output := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.finite_cases α β Tag inst_1 input output tagEncoding tag
    branch htag hbranch

/-- Concatenate input-dependent lists indexed by a fixed list of parameters.
No encoding of the fixed parameters is required. -/
theorem flatMapConst.{u_1}
    {β γ : Type}
    {encB : β ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {ι : Type u_1}
    (l : List ι)
    {f : γ → ι → List β}
    (hf : ∀ i ∈ l,
  ComputableInPolyTime (fun (x : γ) => f x i) encIn
    (encList encB)) :
    ComputableInPolyTime (fun (x : γ) => List.flatMap (f x) l) encIn
      (encList encB) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.flatMapConst β γ encB encIn ι l f hf

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

/-- Concatenate polynomial-time lists computed from each element and a fixed parameter. -/
theorem flatMapWith
    {α β γ π : Type}
    {encA : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {encP : π ↪ List Bool}
    {f : π × α → List β}
    {par : γ → π}
    {list : γ → List α}
    (hf : ComputableInPolyTime f (encPair encP encA)
  (encList encB))
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime
      (fun (x : γ) => List.flatMap (fun (a : α) => f (par x, a)) (list x)) encIn
      (encList encB) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.flatMapWith α β γ π encA encB encIn encP f par list hf hpar
    hlist

/-- Concatenate lists computed jointly from the original input and each list element.
Like `mapWithInput`, this is a composition rule for `fun_prop`. -/
theorem flatMapWithInput
    {α β γ : Type}
    {encA : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {f : γ → α → List β}
    {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hf : ComputableInPolyTime (fun (p : γ × α) => f p.1 p.2)
  (encPair encIn encA) (encList encB)) :
    ComputableInPolyTime (fun (x : γ) => List.flatMap (f x) (list x))
      encIn (encList encB) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.flatMapWithInput α β γ encA encB encIn f list hlist hf

/-- Concatenating a list of lists is polynomial-time. -/
theorem flatten
    {α : Type}
    (enc : α ↪ List Bool) :
    ComputableInPolyTime List.flatten
      (encList (encList enc))
      (encList enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.flatten α enc

/-- A left fold is polynomial-time when its step is polynomial-time and its intermediate
accumulators have polynomially bounded encoded length. -/
theorem foldl'
    {γ α β : Type}
    {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encL : List α ↪ List Bool}
    [inst_1 : ListEncoding encA encL]
    [inst_2 : SizedListEncoding encA encL]
    {list : γ → List α}
    {init : γ → β}
    {step : β → α → β}
    (hlist : ComputableInPolyTime list encIn encL)
    (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun (p : β × α) => step p.1 p.2)
  (encPair encB encA) encB)
    {B : γ → ℕ}
    (hB : PolyBounded (fun (x : γ) => ((encIn : γ → List Bool) x).length) B)
    (hstates : ∀ (x : γ),
  ∀ i ≤ (list x).length,
    ((encB : β → List Bool) (List.foldl step (init x) (List.take i (list x)))).length ≤
      B x) :
    ComputableInPolyTime
      (fun (x : γ) => List.foldl step (init x) (list x)) encIn encB := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.foldl' γ α β encIn encA encB encL inst_1 inst_2 list init
    step hlist hinit hstep B hB hstates

/-- A polynomial-time fold whose step also uses a fixed, polynomial-time computable parameter. -/
theorem foldlWith
    {γ α β π : Type}
    {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encL : List α ↪ List Bool}
    {encP : π ↪ List Bool}
    [inst_1 : ListEncoding encA encL]
    [inst_2 : SizedListEncoding encA encL]
    {par : γ → π}
    {list : γ → List α}
    {init : γ → β}
    {step : π → β → α → β}
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn encL)
    (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun (p : (π × β) × α) => step p.1.1 p.1.2 p.2)
  (encPair (encPair encP encB) encA) encB)
    {B : γ → ℕ}
    (hB : PolyBounded (fun (x : γ) => ((encIn : γ → List Bool) x).length) B)
    (hstates : ∀ (x : γ),
  ∀ i ≤ (list x).length,
    ((encB : β → List Bool)
          (List.foldl (step (par x)) (init x) (List.take i (list x)))).length ≤
      B x) :
    ComputableInPolyTime
      (fun (x : γ) => List.foldl (step (par x)) (init x) (list x)) encIn encB := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.foldlWith γ α β π encIn encA encB encL encP inst_1 inst_2
    par list init step hpar hlist hinit hstep B hB hstates

/-- A fold callback may capture its original input. Growth is needed only on elements of the
runtime list, for every accumulator. Joint computation and encoding evidence lets automation
choose compatible list and callback certificates; paired growth obligations select a common
polynomial bound. The general `foldlWith_of_bounded_growth` contract takes separate premises. -/
theorem foldlWithInput_of_bounded_growth
    {γ α β : Type}
    {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encL : List α ↪ List Bool}
    {list : γ → List α}
    {init : γ → β}
    {step : γ → β → α → β}
    (hinit : ComputableInPolyTime init encIn encB)
    (hcompute : ComputableInPolyTime list encIn encL ∧
  ComputableInPolyTime
      (fun (p : (γ × β) × α) => step p.1.1 p.1.2 p.2)
      (encPair (encPair encIn encB) encA) encB ∧
    ListEncoding encA encL ∧
      SizedListEncoding encA encL)
    {growth : γ → ℕ}
    (hbound : PolyBounded (fun (x : γ) => ((encIn : γ → List Bool) x).length)
    growth ∧
  ∀ (x : γ) (state : β),
    ∀ value ∈ list x,
      ((encB : β → List Bool) (step x state value)).length ≤
        ((encB : β → List Bool) state).length + growth x) :
    ComputableInPolyTime
      (fun (x : γ) => List.foldl (step x) (init x) (list x)) encIn encB := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.foldlWithInput_of_bounded_growth γ α β encIn encA encB encL
    list init step hinit hcompute growth hbound

/-- A captured fold may add a polynomial amount of storage per element, measured against the
original input. The growth bound covers every accumulator and each element in the runtime list;
the joint step certificate still covers all parameters, accumulators and elements. -/
theorem foldlWith_of_bounded_growth
    {γ α β π : Type}
    {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encL : List α ↪ List Bool}
    {encP : π ↪ List Bool}
    [inst_1 : ListEncoding encA encL]
    [inst_2 : SizedListEncoding encA encL]
    {par : γ → π}
    {list : γ → List α}
    {init : γ → β}
    {step : π → β → α → β}
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn encL)
    (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun (p : (π × β) × α) => step p.1.1 p.1.2 p.2)
  (encPair (encPair encP encB) encA) encB)
    {growth : γ → ℕ}
    (hpoly : PolyBounded (fun (x : γ) => ((encIn : γ → List Bool) x).length)
  growth)
    (hgrowth : ∀ (x : γ) (state : β),
  ∀ value ∈ list x,
    ((encB : β → List Bool) (step (par x) state value)).length ≤
      ((encB : β → List Bool) state).length + growth x) :
    ComputableInPolyTime
      (fun (x : γ) => List.foldl (step (par x)) (init x) (list x)) encIn encB := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.foldlWith_of_bounded_growth γ α β π encIn encA encB encL
    encP inst_1 inst_2 par list init step hpar hlist hinit hstep growth hpoly hgrowth

/-- A prefix invariant supplies both the accumulator bound and the final postcondition for a
fold with a captured parameter. The size bound may depend on the original input and need not be
computable. The step certificate is uniform jointly in the parameter, accumulator and element. -/
theorem foldlWith_spec
    {γ α β π : Type}
    {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encL : List α ↪ List Bool}
    {encP : π ↪ List Bool}
    [inst_1 : ListEncoding encA encL]
    [inst_2 : SizedListEncoding encA encL]
    {par : γ → π}
    {list : γ → List α}
    {init : γ → β}
    {step : π → β → α → β}
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn encL)
    (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun (p : (π × β) × α) => step p.1.1 p.1.2 p.2)
  (encPair (encPair encP encB) encA) encB)
    (invariant : γ → List α → β → Prop)
    (hbase : ∀ (x : γ), invariant x [] (init x))
    (hpreserve : ∀ (x : γ) (consumed : List α) (state : β) (value : α),
  consumed ++ [value] <+: list x →
    invariant x consumed state →
      invariant x (consumed ++ [value]) (step (par x) state value))
    {size : γ → ℕ}
    (hsize : PolyBounded (fun (x : γ) => ((encIn : γ → List Bool) x).length) size)
    (hbound : ∀ (x : γ) (consumed : List α) (state : β),
  consumed <+: list x →
    invariant x consumed state → ((encB : β → List Bool) state).length ≤ size x) :
    ComputableInPolyTime
        (fun (x : γ) => List.foldl (step (par x)) (init x) (list x)) encIn encB ∧
      ∀ (x : γ), invariant x (list x) (List.foldl (step (par x)) (init x) (list x)) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.foldlWith_spec γ α β π encIn encA encB encL encP inst_1
    inst_2 par list init step hpar hlist hinit hstep invariant hbase hpreserve size hsize hbound

/-- Constant additive growth discharges the fold's intermediate-size obligation. -/
theorem foldl_of_bounded_growth
    {γ α β : Type}
    {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encL : List α ↪ List Bool}
    [inst_1 : ListEncoding encA encL]
    [inst_2 : SizedListEncoding encA encL]
    {list : γ → List α}
    {init : γ → β}
    {step : β → α → β}
    (hlist : ComputableInPolyTime list encIn encL)
    (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun (p : β × α) => step p.1 p.2)
  (encPair encB encA) encB)
    {growth : ℕ}
    (hgrowth : ∀ (state : β) (value : α),
  ((encB : β → List Bool) (step state value)).length ≤
    ((encB : β → List Bool) state).length + growth) :
    ComputableInPolyTime
      (fun (x : γ) => List.foldl step (init x) (list x)) encIn encB := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.foldl_of_bounded_growth γ α β encIn encA encB encL inst_1
    inst_2 list init step hlist hinit hstep growth hgrowth

/-- A prefix invariant supplies both the accumulator bound and the final postcondition.
The size bound may depend on the original input and need not be computable. The list and step
must have uniform polynomial-time certificates. -/
theorem foldl_spec
    {γ α β : Type}
    {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encL : List α ↪ List Bool}
    [inst_1 : ListEncoding encA encL]
    [inst_2 : SizedListEncoding encA encL]
    {list : γ → List α}
    {init : γ → β}
    {step : β → α → β}
    (hlist : ComputableInPolyTime list encIn encL)
    (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun (p : β × α) => step p.1 p.2)
  (encPair encB encA) encB)
    (invariant : γ → List α → β → Prop)
    (hbase : ∀ (x : γ), invariant x [] (init x))
    (hpreserve : ∀ (x : γ) (consumed : List α) (state : β) (value : α),
  consumed ++ [value] <+: list x →
    invariant x consumed state → invariant x (consumed ++ [value]) (step state value))
    {size : γ → ℕ}
    (hsize : PolyBounded (fun (x : γ) => ((encIn : γ → List Bool) x).length) size)
    (hbound : ∀ (x : γ) (consumed : List α) (state : β),
  consumed <+: list x →
    invariant x consumed state → ((encB : β → List Bool) state).length ≤ size x) :
    ComputableInPolyTime
        (fun (x : γ) => List.foldl step (init x) (list x)) encIn encB ∧
      ∀ (x : γ), invariant x (list x) (List.foldl step (init x) (list x)) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.foldl_spec γ α β encIn encA encB encL inst_1 inst_2 list
    init step hlist hinit hstep invariant hbase hpreserve size hsize hbound

/-- Look up a computed unary index, returning `none` outside a computed list. The list certificate
determines its encoding before proof search checks the corresponding operation and size rules. -/
theorem getElem?
    {α γ : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {encL : List α ↪ List Bool}
    {list : γ → List α}
    {index : γ → ℕ}
    (hlist : ComputableInPolyTime list encIn encL)
    (hindex : ComputableInPolyTime index encIn encUnary)
    [inst_1 : ListEncoding encA encL]
    [inst_2 : SizedListEncoding encA encL] :
    ComputableInPolyTime (fun (x : γ) => (list x)[index x]?) encIn
      (encOption encA) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.getElem? α γ encA encIn encL list index hlist hindex inst_1
    inst_2

/-- Read an optional head in any list encoding, without an inhabitant of the element type. -/
theorem head?
    {α : Type}
    (enc : α ↪ List Bool)
    {encL : List α ↪ List Bool}
    [inst_1 : ListEncoding enc encL] :
    ComputableInPolyTime List.head? encL
      (encOption enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.head? α enc encL inst_1

/-- Read the head of any list encoding with a fixed fallback. -/
theorem headD
    {α : Type}
    {encA : α ↪ List Bool}
    {encL : List α ↪ List Bool}
    [inst_1 : ListEncoding encA encL]
    (fallback : α) :
    ComputableInPolyTime (fun (list : List α) => list.headD fallback)
      encL encA := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.headD α encA encL inst_1 fallback

/-- The index of the first occurrence, or the list length if absent, computed in unary.
The element itself can use any encoding. -/
theorem idxOf
    {α : Type}
    [inst_1 : DecidableEq α]
    (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun (p : List α × α) => List.idxOf p.2 p.1)
      (encPair (encList enc) enc)
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.idxOf α inst_1 enc

/-- Find a computed value's first occurrence in a computed list. -/
theorem idxOfWithInput
    {α γ : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    [inst_1 : DecidableEq α]
    {list : γ → List α}
    {value : γ → α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hvalue : ComputableInPolyTime value encIn encA) :
    ComputableInPolyTime (fun (x : γ) => List.idxOf (value x) (list x))
      encIn encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.idxOfWithInput α γ encA encIn inst_1 list value hlist hvalue

/-- Efficient unary values share a polynomial bound over a polynomially bounded range of
indices. Selecting an index does not require a computable choice. -/
theorem indexed_polynomial_bound
    {f : ℕ → ℕ → ℕ}
    {count : ℕ → ℕ}
    (hf : ComputableInPolyTime (fun (input : ℕ × ℕ) => f input.1 input.2)
  (encPair encUnary encUnary)
  encUnary)
    (hcount : Cslib.PolynomiallyBounded count) :
    ∃ (c : ℕ) (d : ℕ), ∀ (n i : ℕ), i < count n → f n i ≤ c * (n + 1) ^ d := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.indexed_polynomial_bound f count hf hcount

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

/-- A unary loop count and polynomially bounded intermediate states give a polynomial-time loop. -/
theorem iterate
    {α β : Type}
    {encIn : α ↪ List Bool}
    {encState : β ↪ List Bool}
    {count : α → ℕ}
    {init : α → β}
    {step : β → β}
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hinit : ComputableInPolyTime init encIn encState)
    (hstep : ComputableInPolyTime step encState encState)
    {bound : α → ℕ}
    (hbound : PolyBounded (fun (x : α) => ((encIn : α → List Bool) x).length) bound)
    (hstates : ∀ (x : α),
  ∀ i ≤ count x, ((encState : β → List Bool) (step^[i] (init x))).length ≤ bound x) :
    ComputableInPolyTime (fun (x : α) => step^[count x] (init x)) encIn
      encState := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.iterate α β encIn encState count init step hcount hinit
    hstep bound hbound hstates

/-- Capture a computed parameter while bounding every intermediate loop state. -/
theorem iterateWith
    {α β : Type}
    {encIn : α ↪ List Bool}
    {encState : β ↪ List Bool}
    {π : Type}
    {encPar : π ↪ List Bool}
    {par : α → π}
    {count : α → ℕ}
    {init : α → β}
    {step : π → β → β}
    (hpar : ComputableInPolyTime par encIn encPar)
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hinit : ComputableInPolyTime init encIn encState)
    (hstep : ComputableInPolyTime (fun (p : π × β) => step p.1 p.2)
  (encPair encPar encState) encState)
    {bound : α → ℕ}
    (hbound : PolyBounded (fun (x : α) => ((encIn : α → List Bool) x).length) bound)
    (hstates : ∀ (x : α),
  ∀ i ≤ count x,
    ((encState : β → List Bool) ((step (par x))^[i] (init x))).length ≤ bound x) :
    ComputableInPolyTime
      (fun (x : α) => (step (par x))^[count x] (init x)) encIn encState := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.iterateWith α β encIn encState π encPar par count init step
    hpar hcount hinit hstep bound hbound hstates

/-- An iteration step may capture its original input. Paired growth obligations let automation
select a common polynomial bound. The uniform joint step certificate charges the captured input
on every iteration; the growth bound need not itself be computable. -/
theorem iterateWithInput_of_bounded_growth
    {α β : Type}
    {encIn : α ↪ List Bool}
    {encState : β ↪ List Bool}
    {count : α → ℕ}
    {init : α → β}
    {step : α → β → β}
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hinit : ComputableInPolyTime init encIn encState)
    (hstep : ComputableInPolyTime (fun (p : α × β) => step p.1 p.2)
  (encPair encIn encState) encState)
    {growth : α → ℕ}
    (hbound : PolyBounded (fun (x : α) => ((encIn : α → List Bool) x).length)
    growth ∧
  ∀ (x : α) (state : β),
    ((encState : β → List Bool) (step x state)).length ≤
      ((encState : β → List Bool) state).length + growth x) :
    ComputableInPolyTime (fun (x : α) => (step x)^[count x] (init x))
      encIn encState := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.iterateWithInput_of_bounded_growth α β encIn encState count
    init step hcount hinit hstep growth hbound

/-- A captured loop may add a polynomial amount of storage per iteration, measured against the
original input. A bound depending only on the current state would not justify this rule. -/
theorem iterateWith_of_bounded_growth
    {α β : Type}
    {encIn : α ↪ List Bool}
    {encState : β ↪ List Bool}
    {π : Type}
    {encPar : π ↪ List Bool}
    {par : α → π}
    {count : α → ℕ}
    {init : α → β}
    {step : π → β → β}
    (hpar : ComputableInPolyTime par encIn encPar)
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hinit : ComputableInPolyTime init encIn encState)
    (hstep : ComputableInPolyTime (fun (p : π × β) => step p.1 p.2)
  (encPair encPar encState) encState)
    {growth : α → ℕ}
    (hpoly : PolyBounded (fun (x : α) => ((encIn : α → List Bool) x).length)
  growth)
    (hgrowth : ∀ (x : α) (state : β),
  ((encState : β → List Bool) (step (par x) state)).length ≤
    ((encState : β → List Bool) state).length + growth x) :
    ComputableInPolyTime
      (fun (x : α) => (step (par x))^[count x] (init x)) encIn encState := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.iterateWith_of_bounded_growth α β encIn encState π encPar
    par count init step hpar hcount hinit hstep growth hpoly hgrowth

/-- Iteration may capture a computed parameter. The joint step certificate must be uniform
in that parameter; the invariant and size bound concern the original input. The bound need not
be computable and may use properties of the input beyond its encoded length. -/
theorem iterateWith_spec
    {α β : Type}
    {encIn : α ↪ List Bool}
    {encState : β ↪ List Bool}
    {π : Type}
    {encPar : π ↪ List Bool}
    {par : α → π}
    {count : α → ℕ}
    {init : α → β}
    {step : π → β → β}
    (hpar : ComputableInPolyTime par encIn encPar)
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hinit : ComputableInPolyTime init encIn encState)
    (hstep : ComputableInPolyTime (fun (p : π × β) => step p.1 p.2)
  (encPair encPar encState) encState)
    (invariant : α → ℕ → β → Prop)
    (hbase : ∀ (x : α), invariant x 0 (init x))
    (hpreserve : ∀ (x : α) (i : ℕ) (state : β),
  i < count x → invariant x i state → invariant x (i + 1) (step (par x) state))
    {size : α → ℕ}
    (hsize : PolyBounded (fun (x : α) => ((encIn : α → List Bool) x).length) size)
    (hbound : ∀ (x : α) (i : ℕ) (state : β),
  i ≤ count x → invariant x i state → ((encState : β → List Bool) state).length ≤ size x) :
    ComputableInPolyTime
        (fun (x : α) => (step (par x))^[count x] (init x)) encIn encState ∧
      ∀ (x : α), invariant x (count x) ((step (par x))^[count x] (init x)) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.iterateWith_spec α β encIn encState π encPar par count init
    step hpar hcount hinit hstep invariant hbase hpreserve size hsize hbound

/-- A loop with constant additive state growth has polynomially bounded intermediate states. -/
theorem iterate_of_bounded_growth
    {α β : Type}
    {encIn : α ↪ List Bool}
    {encState : β ↪ List Bool}
    {count : α → ℕ}
    {init : α → β}
    {step : β → β}
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hinit : ComputableInPolyTime init encIn encState)
    (hstep : ComputableInPolyTime step encState encState)
    {growth : ℕ}
    (hgrowth : ∀ (state : β),
  ((encState : β → List Bool) (step state)).length ≤
    ((encState : β → List Bool) state).length + growth) :
    ComputableInPolyTime (fun (x : α) => step^[count x] (init x)) encIn
      encState := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.iterate_of_bounded_growth α β encIn encState count init step
    hcount hinit hstep growth hgrowth

/-- One invariant proves both the resource bound and the final loop postcondition. -/
theorem iterate_spec
    {α β : Type}
    {encIn : α ↪ List Bool}
    {encState : β ↪ List Bool}
    {count : α → ℕ}
    {init : α → β}
    {step : β → β}
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hinit : ComputableInPolyTime init encIn encState)
    (hstep : ComputableInPolyTime step encState encState)
    (invariant : α → ℕ → β → Prop)
    (hbase : ∀ (x : α), invariant x 0 (init x))
    (hpreserve : ∀ (x : α) (i : ℕ) (state : β),
  i < count x → invariant x i state → invariant x (i + 1) (step state))
    {size : α → ℕ}
    (hsize : PolyBounded (fun (x : α) => ((encIn : α → List Bool) x).length) size)
    (hbound : ∀ (x : α) (i : ℕ) (state : β),
  i ≤ count x → invariant x i state → ((encState : β → List Bool) state).length ≤ size x) :
    ComputableInPolyTime (fun (x : α) => step^[count x] (init x)) encIn
        encState ∧
      ∀ (x : α), invariant x (count x) (step^[count x] (init x)) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.iterate_spec α β encIn encState count init step hcount hinit
    hstep invariant hbase hpreserve size hsize hbound

/-- The length of a list, in unary, including raw bit strings. -/
theorem length
    {α : Type}
    (enc : α ↪ List Bool)
    {encL : List α ↪ List Bool}
    [inst_1 : ListEncoding enc encL]
    [inst_2 : SizedListEncoding enc encL] :
    ComputableInPolyTime (fun (l : List α) => l.length) encL
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.length α enc encL inst_1 inst_2

/-- Length of a raw bit string. -/
theorem length_bits :
    ComputableInPolyTime (fun (l : List Bool) => l.length)
      encBits encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.length_bits

/-- Length of a computed raw bit string, fixing the intermediate encoding for proof search.
Registered after `encoding_length` so `fun_prop` first tries this rule on computed words. -/
theorem length_bits_comp
    {α : Type}
    {input : α ↪ List Bool}
    {word : α → List Bool}
    (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime (fun (a : α) => (word a).length) input
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.length_bits_comp α input word hword

/-- Length of a framed list; the element encoding is inferred from the list encoding. -/
theorem length_list
    {α : Type}
    (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun (l : List α) => l.length)
      (encList enc) encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.length_list α enc

/-- Concatenating two framed lists is polynomial-time. -/
theorem listAppend
    {α : Type}
    (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun (p : List α × List α) => p.1 ++ p.2)
      (encPair (encList enc)
        (encList enc))
      (encList enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.listAppend α enc

/-- Concatenate computed lists, inferring their shared encoding from the result. -/
theorem listAppend'
    {α γ : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {left right : γ → List α}
    (hleft : ComputableInPolyTime left encIn (encList encA))
    (hright : ComputableInPolyTime right encIn (encList encA)) :
    ComputableInPolyTime (fun (x : γ) => left x ++ right x) encIn
      (encList encA) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.listAppend' α γ encA encIn left right hleft hright

/-- Drop a computed unary number of elements from a computed framed list. -/
theorem listDropWithInput
    {α γ : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {list : γ → List α}
    {count : γ → ℕ}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hcount : ComputableInPolyTime count encIn encUnary) :
    ComputableInPolyTime (fun (x : γ) => List.drop (count x) (list x))
      encIn (encList encA) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.listDropWithInput α γ encA encIn list count hlist hcount

/-- List lookup with a fixed default and a unary index, including lookup in raw bit strings. -/
theorem listGetD
    {α : Type}
    {encA : α ↪ List Bool}
    {encL : List α ↪ List Bool}
    [inst_1 : ListEncoding encA encL]
    [inst_2 : SizedListEncoding encA encL]
    (d : α) :
    ComputableInPolyTime (fun (p : List α × ℕ) => p.1.getD p.2 d)
      (encPair encL encUnary) encA := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.listGetD α encA encL inst_1 inst_2 d

/-- Lookup in a computed list at a computed binary index. The index is first capped at the length
of the list, reading its binary digits most significant first and capping every partial value,
so
an index far beyond the list costs only its binary length; beyond the list every lookup returns
the default. -/
theorem listGetD_binary
    {α γ : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {encL : List α ↪ List Bool}
    [inst_1 : ListEncoding encA encL]
    [inst_2 : SizedListEncoding encA encL]
    {l : γ → List α}
    {i : γ → ℕ}
    (d : α)
    (hl : ComputableInPolyTime l encIn encL)
    (hi : ComputableInPolyTime i encIn encNat) :
    ComputableInPolyTime (fun (x : γ) => (l x).getD (i x) d) encIn encA := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.listGetD_binary α γ encA encIn encL inst_1 inst_2 l i d hl
    hi

/-- Read a computed framed list's head, inferring the element encoding from the list before
composing with a later field projection. -/
theorem listHeadDWithInput
    {α γ : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {list : γ → List α}
    (fallback : α)
    (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime (fun (a : γ) => (list a).headD fallback) encIn
      encA := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.listHeadDWithInput α γ encA encIn list fallback hlist

/-- Test emptiness without decoding a list element or requiring a default value. -/
theorem listIsEmpty
    {α : Type}
    {encA : α ↪ List Bool}
    {encL : List α ↪ List Bool}
    [inst_1 : ListEncoding encA encL] :
    ComputableInPolyTime List.isEmpty encL encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.listIsEmpty α encA encL inst_1

/-- Test a framed list's emptiness, determining its element encoding for automation. -/
theorem listIsEmpty'
    {α : Type}
    (enc : α ↪ List Bool) :
    ComputableInPolyTime List.isEmpty (encList enc)
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.listIsEmpty' α enc

/-- Reverse a framed list; the accumulator is a permutation of a prefix of the input. -/
theorem listReverse
    {α : Type}
    (enc : α ↪ List Bool) :
    ComputableInPolyTime List.reverse (encList enc)
      (encList enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.listReverse α enc

/-- Reverse a computed framed list, inferring its element encoding from the result. -/
theorem listReverseWithInput
    {α γ : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime (fun (a : γ) => (list a).reverse) encIn
      (encList encA) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.listReverseWithInput α γ encA encIn list hlist

/-- Drop the head of a framed list, determining its element encoding for automation. -/
theorem listTail
    {α : Type}
    (enc : α ↪ List Bool) :
    ComputableInPolyTime List.tail (encList enc)
      (encList enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.listTail α enc

/-- Take a computed unary number of elements from a computed framed list. -/
theorem listTakeWithInput
    {α γ : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {list : γ → List α}
    {count : γ → ℕ}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hcount : ComputableInPolyTime count encIn encUnary) :
    ComputableInPolyTime (fun (x : γ) => List.take (count x) (list x))
      encIn (encList encA) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.listTakeWithInput α γ encA encIn list count hlist hcount

/-- Remove the framing from a list of bits. -/
theorem listToBits :
    ComputableInPolyTime (fun (l : List Bool) => l)
      (encList encBool) encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.listToBits

/-- A polynomial-time function can be mapped over a list in polynomial time. -/
theorem map
    {α β : Type}
    {encA : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {f : α → β}
    (hf : ComputableInPolyTime f encA encB) :
    ComputableInPolyTime (List.map f) (encList encA)
      (encList encB) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.map α β encA encB f hf

/-- Map an input-dependent function over a fixed list. Only its members need certificates;
the list and its elements are not part of the computational input. -/
theorem mapConst.{u_1}
    {β γ : Type}
    {encB : β ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {ι : Type u_1}
    (l : List ι)
    {f : γ → ι → β}
    (hf : ∀ i ∈ l, ComputableInPolyTime (fun (x : γ) => f x i) encIn encB) :
    ComputableInPolyTime (fun (x : γ) => List.map (f x) l) encIn
      (encList encB) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.mapConst β γ encB encIn ι l f hf

/-- Filter and map a fixed list using computed guards and outputs. No encoding of the fixed
parameters is required; only members of the list need certificates. -/
theorem mapFilterConst.{u_1}
    {β γ : Type}
    {encB : β ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {ι : Type u_1}
    (list : List ι)
    {test : γ → ι → Bool}
    {f : γ → ι → β}
    (htest : ∀ i ∈ list,
  ComputableInPolyTime (fun (a : γ) => test a i) encIn
    encBool)
    (hf : ∀ i ∈ list, ComputableInPolyTime (fun (a : γ) => f a i) encIn encB) :
    ComputableInPolyTime
      (fun (a : γ) => List.map (f a) (List.filter (test a) list)) encIn
      (encList encB) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.mapFilterConst β γ encB encIn ι list test f htest hf

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

/-- Map a polynomial-time function with a fixed parameter over a polynomial-time computable list.
The list may have any polynomial encoded length. -/
theorem mapWith
    {α β γ π : Type}
    {encA : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {encP : π ↪ List Bool}
    {f : π × α → β}
    {par : γ → π}
    {list : γ → List α}
    (hf : ComputableInPolyTime f (encPair encP encA) encB)
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime
      (fun (x : γ) => List.map (fun (a : α) => f (par x, a)) (list x)) encIn
      (encList encB) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.mapWith α β γ π encA encB encIn encP f par list hf hpar
    hlist

/-- Map a function that also uses the original input. A single joint certificate in the input
and list element makes the cost uniform across all elements. The list certificate is supplied
first so that `fun_prop` can infer its element encoding before checking the body. -/
theorem mapWithInput
    {α β γ : Type}
    {encA : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {f : γ → α → β}
    {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hf : ComputableInPolyTime (fun (p : γ × α) => f p.1 p.2)
  (encPair encIn encA) encB) :
    ComputableInPolyTime (fun (x : γ) => List.map (f x) (list x)) encIn
      (encList encB) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.mapWithInput α β γ encA encB encIn f list hlist hf

/-- The binary digits of a natural number, as a raw bit string. -/
theorem natBits :
    ComputableInPolyTime Nat.bits encNat
      encBits := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.natBits

/-- Construct a list of a fixed number of efficiently computed entries. -/
theorem ofFn
    {α Value : Type}
    {input : α ↪ List Bool}
    {enc : Value ↪ List Bool}
    {count : ℕ}
    {values : α → Fin count → Value}
    (hvalues : ∀ (i : Fin count),
  ComputableInPolyTime (fun (a : α) => values a i) input enc) :
    ComputableInPolyTime (fun (a : α) => List.ofFn (values a)) input
      (encList enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.ofFn α Value input enc count values hvalues

/-- Branch on a computed option, charging its full value and any captured original input. -/
theorem optionElimWithInput
    {α β : Type}
    {encA : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {γ : Type}
    {encC : γ ↪ List Bool}
    {value : α → Option β}
    {fallback : α → γ}
    {body : α → β → γ}
    (hvalue : ComputableInPolyTime value encA (encOption encB))
    (hfallback : ComputableInPolyTime fallback encA encC)
    (hbody : ComputableInPolyTime (fun (p : α × β) => body p.1 p.2)
  (encPair encA encB) encC) :
    ComputableInPolyTime
      (fun (a : α) => (value a).elim (fallback a) (body a)) encA encC := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.optionElimWithInput α β encA encB γ encC value fallback body
    hvalue hfallback hbody

/-- Read an option with a fallback supplied as part of the input. -/
theorem optionGetD
    {α : Type}
    (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun (p : Option α × α) => p.1.getD p.2)
      (encPair (encOption enc) enc) enc := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.optionGetD α enc

/-- Read a computed option with a computed fallback, using their shared value encoding. -/
theorem optionGetDWithInput
    {α β : Type}
    {encA : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {value : α → Option β}
    {fallback : α → β}
    (hvalue : ComputableInPolyTime value encA (encOption encB))
    (hfallback : ComputableInPolyTime fallback encA encB) :
    ComputableInPolyTime (fun (a : α) => (value a).getD (fallback a))
      encA encB := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.optionGetDWithInput α β encA encB value fallback hvalue
    hfallback

/-- Test whether a computed option contains a value, without requiring a default value. -/
theorem optionIsSome
    {α β : Type}
    {encA : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {value : α → Option β}
    (hvalue : ComputableInPolyTime value encA (encOption encB)) :
    ComputableInPolyTime (fun (a : α) => (value a).isSome) encA
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.optionIsSome α β encA encB value hvalue

/-- Construct an optional value with the standard option encoding. -/
theorem optionSome
    {α : Type}
    (enc : α ↪ List Bool) :
    ComputableInPolyTime Option.some enc
      (encOption enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.optionSome α enc

/-- Construct a table by computing each entry, retaining the original input in each computation. -/
theorem pi
    {α Index Value : Type}
    {input : α ↪ List Bool}
    {enc : Value ↪ List Bool}
    [inst_1 : Fintype Index]
    {values : α → Index → Value}
    (hvalues : ∀ (i : Index),
  ComputableInPolyTime (fun (a : α) => values a i) input enc) :
    ComputableInPolyTime values input (encPi enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.pi α Index Value input enc inst_1 values hvalues

/-- Read a fixed entry, charging for the stored prefix without requiring a default value. -/
theorem pi_apply
    {Index Value : Type}
    [inst_1 : Fintype Index]
    (enc : Value ↪ List Bool)
    (i : Index) :
    ComputableInPolyTime (fun (values : Index → Value) => values i)
      (encPi enc) enc := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.pi_apply Index Value inst_1 enc i

/-- Read a computed index of a fixed finite table, charging the index and all stored entries. -/
theorem pi_apply'
    {α Index Value : Type}
    {input : α ↪ List Bool}
    {enc : Value ↪ List Bool}
    [inst_1 : Fintype Index]
    {indexEncoding : Index ↪ List Bool}
    {values : α → Index → Value}
    {index : α → Index}
    (hvalues : ComputableInPolyTime values input (encPi enc))
    (hindex : ComputableInPolyTime index input indexEncoding) :
    ComputableInPolyTime (fun (a : α) => values a (index a)) input enc := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.pi_apply' α Index Value input enc inst_1 indexEncoding
    values index hvalues hindex

/-- Evaluate a stored table at a stored index. The product view is registered with `fun_prop`;
for separately computed tables and indices, apply `pi_apply'` to their certificates. -/
theorem pi_eval
    {Index Value : Type}
    [inst_1 : Fintype Index]
    (indexEncoding : Index ↪ List Bool)
    (enc : Value ↪ List Bool) :
    ComputableInPolyTime
      (fun (pair : (Index → Value) × Index) => pair.1 pair.2)
      (encPair (encPi enc) indexEncoding) enc := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.pi_eval Index Value inst_1 indexEncoding enc

/-- Update a fixed table entry while charging for all preserved entries. -/
theorem pi_update
    {α Index Value : Type}
    {input : α ↪ List Bool}
    {enc : Value ↪ List Bool}
    [inst_1 : Fintype Index]
    [inst_2 : DecidableEq Index]
    {values : α → Index → Value}
    {value : α → Value}
    (hvalues : ComputableInPolyTime values input (encPi enc))
    (hvalue : ComputableInPolyTime value input enc)
    (i : Index) :
    ComputableInPolyTime
      (fun (a : α) => Function.update (values a) i (value a)) input
      (encPi enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.pi_update α Index Value input enc inst_1 inst_2 values value
    hvalues hvalue i

/-- Update a computed index while retaining and charging every other entry. -/
theorem pi_update'
    {α Index Value : Type}
    {input : α ↪ List Bool}
    {enc : Value ↪ List Bool}
    [inst_1 : Fintype Index]
    [inst_2 : DecidableEq Index]
    {indexEncoding : Index ↪ List Bool}
    {values : α → Index → Value}
    {index : α → Index}
    {value : α → Value}
    (hvalues : ComputableInPolyTime values input (encPi enc))
    (hindex : ComputableInPolyTime index input indexEncoding)
    (hvalue : ComputableInPolyTime value input enc) :
    ComputableInPolyTime
      (fun (a : α) => Function.update (values a) (index a) (value a)) input
      (encPi enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.pi_update' α Index Value input enc inst_1 inst_2
    indexEncoding values index value hvalues hindex hvalue

/-- A unary-output polynomial-time function is polynomially bounded in its unary input. -/
theorem polynomiallyBounded
    {f : ℕ → ℕ}
    (hf : ComputableInPolyTime f encUnary
  encUnary) :
    Cslib.PolynomiallyBounded f := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.polynomiallyBounded f hf

/-- Enumerate `0, …, n - 1`, with the bound and the elements in unary. -/
theorem range :
    ComputableInPolyTime List.range encUnary
      (encList encUnary) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.range

/-- Repeat a computed value a computed unary number of times, charging every copy and delimiter. -/
theorem replicate
    {α γ : Type}
    {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {count : γ → ℕ}
    {value : γ → α}
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hvalue : ComputableInPolyTime value encIn encA) :
    ComputableInPolyTime
      (fun (x : γ) => List.replicate (count x) (value x)) encIn
      (encList encA) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.replicate α γ encA encIn count value hcount hvalue

/-- Tag an encoded value as belonging to the left summand. -/
theorem sumInl
    {α β : Type}
    (left : α ↪ List Bool)
    (right : β ↪ List Bool) :
    ComputableInPolyTime Sum.inl left
      (encSum left right) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.sumInl α β left right

/-- Tag an encoded value as belonging to the right summand. -/
theorem sumInr
    {α β : Type}
    (left : α ↪ List Bool)
    (right : β ↪ List Bool) :
    ComputableInPolyTime Sum.inr right
      (encSum left right) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.sumInr α β left right

/-- Drop the head of any list encoding. -/
theorem tail
    {α : Type}
    {encA : α ↪ List Bool}
    {encL : List α ↪ List Bool}
    [inst_1 : ListEncoding encA encL] :
    ComputableInPolyTime List.tail encL encL := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.tail α encA encL inst_1

/-- Take a unary number of framed-list elements using certified reversal and dropping. -/
theorem takeUnary
    {α : Type}
    (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun (p : List α × ℕ) => List.take p.2 p.1)
      (encPair (encList enc)
        encUnary)
      (encList enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.takeUnary α enc

/-- Addition of unary naturals, by concatenating their encodings. -/
theorem unary_add :
    ComputableInPolyTime (fun (p : ℕ × ℕ) => p.1 + p.2)
      (encPair encUnary encUnary)
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_add

/-- Equality of computed unary counters, fixing the intermediate encoding for proof search. -/
theorem unary_beq
    {α : Type}
    {input : α ↪ List Bool}
    {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encUnary)
    (hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun (a : α) => left a == right a) input
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_beq α input left right hleft hright

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

/-- Evaluate a fixed polynomial on unary naturals, with its result also in unary. -/
theorem unary_eval
    (p : Polynomial ℕ) :
    ComputableInPolyTime (fun (x : ℕ) => Polynomial.eval x p)
      encUnary encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_eval p

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

/-- Compare unary naturals. -/
theorem unary_le :
    ComputableInPolyTime
      (fun (p : ℕ × ℕ) => Decidable.decide (p.1 ≤ p.2))
      (encPair encUnary encUnary)
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_le

/-- Compare computed unary values, fixing their intermediate encodings before proof search. -/
theorem unary_le'
    {α : Type}
    {input : α ↪ List Bool}
    {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encUnary)
    (hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime
      (fun (a : α) => Decidable.decide (left a ≤ right a)) input encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_le' α input left right hleft hright

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

/-- Strict comparison of unary naturals. -/
theorem unary_lt :
    ComputableInPolyTime
      (fun (p : ℕ × ℕ) => Decidable.decide (p.1 < p.2))
      (encPair encUnary encUnary)
      encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_lt

/-- Strictly compare computed unary values, with both operand encodings fixed. -/
theorem unary_lt'
    {α : Type}
    {input : α ↪ List Bool}
    {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encUnary)
    (hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime
      (fun (a : α) => Decidable.decide (left a < right a)) input encBool := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_lt' α input left right hleft hright

/-- Take the larger of two unary naturals. -/
theorem unary_max :
    ComputableInPolyTime (fun (p : ℕ × ℕ) => Max.max p.1 p.2)
      (encPair encUnary encUnary)
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_max

/-- Take the smaller of two unary naturals. -/
theorem unary_min :
    ComputableInPolyTime (fun (p : ℕ × ℕ) => Min.min p.1 p.2)
      (encPair encUnary encUnary)
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_min

/-- Remainder of two unary counters. -/
theorem unary_mod :
    ComputableInPolyTime (fun (p : ℕ × ℕ) => p.1 % p.2)
      (encPair encUnary encUnary)
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_mod

/-- Multiplication of unary naturals, by repeated addition. -/
theorem unary_mul :
    ComputableInPolyTime (fun (p : ℕ × ℕ) => p.1 * p.2)
      (encPair encUnary encUnary)
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_mul

/-- The natural-number pairing function, with both arguments and the result in unary. -/
theorem unary_pair :
    ComputableInPolyTime (fun (p : ℕ × ℕ) => Nat.pair p.1 p.2)
      (encPair encUnary encUnary)
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_pair

/-- A fixed power of a unary natural. -/
theorem unary_pow
    (d : ℕ) :
    ComputableInPolyTime (fun (n : ℕ) => n ^ d)
      encUnary encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_pow d

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

/-- Truncated subtraction of unary naturals. -/
theorem unary_sub :
    ComputableInPolyTime (fun (p : ℕ × ℕ) => p.1 - p.2)
      (encPair encUnary encUnary)
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_sub

/-- Convert a unary natural to its binary encoding by incrementing a binary counter. -/
theorem unary_to_binary :
    ComputableInPolyTime (fun (n : ℕ) => n) encUnary
      encNat := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.unary_to_binary

/-- Zip framed lists, charging both inputs and every pair in the output. -/
theorem zip
    {α β : Type}
    (encA : α ↪ List Bool)
    (encB : β ↪ List Bool) :
    ComputableInPolyTime (fun (p : List α × List β) => p.1.zip p.2)
      (encPair (encList encA)
        (encList encB))
      (encList (encPair encA encB)) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.zip α β encA encB

/-- Number the entries of a framed list with unary indices, charging the list and every index. -/
theorem zipIdx
    {α : Type}
    (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun (list : List α) => list.zipIdx)
      (encList enc)
      (encList
        (encPair enc encUnary)) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.zipIdx α enc

end Turing.MultiTapeTM.ComputableInPolyTime



attribute [fun_prop] ComputableInPolyTime.optionSome
attribute [fun_prop] ComputableInPolyTime.optionIsSome
attribute [fun_prop] ComputableInPolyTime.optionGetD
attribute [fun_prop] ComputableInPolyTime.optionGetDWithInput
attribute [fun_prop] ComputableInPolyTime.optionElimWithInput
attribute [fun_prop] ComputableInPolyTime.bitsAppend
attribute [fun_prop] ComputableInPolyTime.bitsCons
attribute [fun_prop] ComputableInPolyTime.headD
attribute [fun_prop] ComputableInPolyTime.listHeadDWithInput
attribute [fun_prop] ComputableInPolyTime.tail
attribute [fun_prop] ComputableInPolyTime.listIsEmpty
attribute [fun_prop] ComputableInPolyTime.listIsEmpty'
attribute [fun_prop] ComputableInPolyTime.bitsIsEmpty
attribute [fun_prop] ComputableInPolyTime.listTail
attribute [fun_prop] ComputableInPolyTime.bitsTail
attribute [fun_prop] ComputableInPolyTime.bitsReverse
attribute [fun_prop] ComputableInPolyTime.bitsReverseWithInput
attribute [fun_prop] ComputableInPolyTime.cons
attribute [fun_prop] ComputableInPolyTime.listAppend
attribute [fun_prop] ComputableInPolyTime.cons'
attribute [fun_prop] ComputableInPolyTime.listAppend'
attribute [fun_prop] ComputableInPolyTime.listReverse
attribute [fun_prop] ComputableInPolyTime.listReverseWithInput
attribute [fun_prop] ComputableInPolyTime.findWithInput
attribute [fun_prop] ComputableInPolyTime.filterWithInput
attribute [fun_prop] ComputableInPolyTime.filter
attribute [fun_prop] ComputableInPolyTime.mapWithInput
attribute [fun_prop] ComputableInPolyTime.map
attribute [fun_prop] ComputableInPolyTime.head?
attribute [fun_prop] ComputableInPolyTime.mapConst
attribute [fun_prop] ComputableInPolyTime.flatten
attribute [fun_prop] ComputableInPolyTime.flatMapWithInput
attribute [fun_prop] ComputableInPolyTime.flatMapConst
attribute [fun_prop] ComputableInPolyTime.mapFilterConst
attribute [fun_prop] ComputableInPolyTime.length_list
attribute [fun_prop] ComputableInPolyTime.length_bits
attribute [fun_prop] ComputableInPolyTime.encoding_length
attribute [fun_prop] ComputableInPolyTime.length_bits_comp
attribute [fun_prop] ComputableInPolyTime.countPWithInput
attribute [fun_prop] ComputableInPolyTime.countWithInput
attribute [fun_prop] ComputableInPolyTime.range
attribute [fun_prop] ComputableInPolyTime.replicate
attribute [fun_prop] ComputableInPolyTime.anyWithInput
attribute [fun_prop] ComputableInPolyTime.allWithInput
attribute [fun_prop] ComputableInPolyTime.allConst
attribute [fun_prop] ComputableInPolyTime.anyConst
attribute [fun_prop] ComputableInPolyTime.idxOf
attribute [fun_prop] ComputableInPolyTime.idxOfWithInput
attribute [fun_prop] ComputableInPolyTime.listDropWithInput
attribute [fun_prop] ComputableInPolyTime.takeUnary
attribute [fun_prop] ComputableInPolyTime.listTakeWithInput
attribute [fun_prop] ComputableInPolyTime.getElem?
attribute [fun_prop] ComputableInPolyTime.bitsDropWithInput
attribute [fun_prop] ComputableInPolyTime.bitsTake
attribute [fun_prop] ComputableInPolyTime.bitsTakeWithInput
attribute [fun_prop] ComputableInPolyTime.listGetD
attribute [fun_prop] ComputableInPolyTime.bitsGetD
attribute [fun_prop] ComputableInPolyTime.bitsGetDWithInput
attribute [fun_prop] ComputableInPolyTime.zip
attribute [fun_prop] ComputableInPolyTime.zipIdx
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
attribute [fun_prop] ComputableInPolyTime.ofFn
attribute [fun_prop] ComputableInPolyTime.pi_update
attribute [fun_prop] ComputableInPolyTime.pi_eval
attribute [fun_prop] ComputableInPolyTime.pi_update'
attribute [fun_prop] ComputableInPolyTime.dpi_update
attribute [fun_prop] ComputableInPolyTime.bool_toUnary
attribute [fun_prop] ComputableInPolyTime.unary_add
attribute [fun_prop] ComputableInPolyTime.unary_sub
attribute [fun_prop] ComputableInPolyTime.unary_mul
attribute [fun_prop] ComputableInPolyTime.unary_min
attribute [fun_prop] ComputableInPolyTime.unary_max
attribute [fun_prop] ComputableInPolyTime.unary_le
attribute [fun_prop] ComputableInPolyTime.unary_lt
attribute [fun_prop] ComputableInPolyTime.unary_le'
attribute [fun_prop] ComputableInPolyTime.unary_lt'
attribute [fun_prop] ComputableInPolyTime.unary_beq
attribute [fun_prop] ComputableInPolyTime.unary_pair
attribute [fun_prop] ComputableInPolyTime.unary_pow
attribute [fun_prop] ComputableInPolyTime.unary_eval
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
attribute [fun_prop] ComputableInPolyTime.sumInl
attribute [fun_prop] ComputableInPolyTime.sumInr
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
attribute [fun_prop] ComputableInPolyTime.foldlWithInput_of_bounded_growth
attribute [fun_prop] ComputableInPolyTime.iterateWithInput_of_bounded_growth
attribute [fun_prop] ComputableInPolyTime.bitsToList
attribute [fun_prop] ComputableInPolyTime.listToBits
attribute [fun_prop] ComputableInPolyTime.pi
attribute [fun_prop] ComputableInPolyTime.pi_apply
attribute [fun_prop] ComputableInPolyTime.dpi
attribute [fun_prop] ComputableInPolyTime.dpi_apply
attribute [fun_prop] ComputableInPolyTime.unary_to_binary
