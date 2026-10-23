/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public meta import Complexity.Tactic.PlainMirror
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
# Plain structural and primitive polynomial-time calculus

Import this module to synthesize plain certificates with the same structural and primitive rules
as the tidy implementation. Counterparts are derived from the elaborated source statements, so
list/fold/iteration bounds and captured parameters are retained rather than copied by hand.
The explicit source list contains generic machine calculus only; it excludes domain endpoints.

The source-to-counterpart registry also identifies originals for coordinated internalization.
It is not a permanent exception to the plain public-surface policy.
-/

public section

plain_mirror_sources [
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Factorial,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Fin,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Prime,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Search]
