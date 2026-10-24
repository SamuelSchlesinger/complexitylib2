/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Factorial
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Prime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Fin

/-! Ordinary original-home providers with explicit unary/binary and fixed-bound contracts. -/

open Turing.MultiTapeTM

example : ComputableInPolyTime Nat.factorial encUnary encNat := by fun_prop

example {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun x => Nat.gcd (left x) (right x)) input encNat := by fun_prop

example : Nat.gcd 0 0 = 0 ∧ Nat.gcd 0 17 = 17 ∧ Nat.gcd 24 18 = 6 := by decide +kernel

example : ComputableInPolyTime (Nat.log 2) encNat encUnary := by fun_prop

example (base : ℕ) : ComputableInPolyTime (Nat.clog base) encUnary encUnary := by fun_prop

example : Nat.log 2 0 = 0 ∧ Nat.log 2 1 = 0 ∧ Nat.log 2 8 = 3 ∧
    Nat.clog 2 9 = 4 ∧ Nat.log 0 100 = 0 ∧ Nat.log 1 100 = 0 := by decide +kernel

example : ComputableInPolyTime (fun n : ℕ => decide n.Prime) encUnary encBool := by fun_prop

example : ¬Nat.Prime 0 ∧ ¬Nat.Prime 1 ∧ Nat.Prime 2 ∧ ¬Nat.Prime 21 := by decide +kernel

-- The output encoding and positive finite bound are fixed independently of each runtime word.
example (output : Fin 3 ↪ List Bool) : ComputableInPolyTime
    (fun word : List Bool => (⟨word.length % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3))
    encBits output :=
  (ComputableInPolyTime.unary_finMod (by decide) output).comp
    (ComputableInPolyTime.length encBool)

run_meta do
  let retired : List Lean.Name := [
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_factorial,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_gcd,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_gcd',
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_log_two,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_log_two,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_log_const,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_clog_const,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_pow_clog_const,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_decide_prime,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_finMod]
  let env ← Lean.getEnv
  for name in retired do
    if env.contains name then
      throwError "superseded arithmetic provider remains: {name}"

/-- info: 'Turing.MultiTapeTM.ComputableInPolyTime.binary_gcd' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputableInPolyTime.binary_gcd
