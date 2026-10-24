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

/-- The base-two logarithm is polynomial-time on binary naturals, with its result in unary. -/
theorem binary_log_two :
    ComputableInPolyTime (Nat.log 2) encNat
      encUnary := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.binary_log_two

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
