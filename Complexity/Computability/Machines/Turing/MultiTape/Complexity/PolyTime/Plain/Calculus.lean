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
