/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Search

/-! Unary arithmetic, membership and inclusive bounded search from ordinary topic imports. -/

open Turing.MultiTapeTM

example : ComputableInPolyTime (fun p : ℕ × ℕ => (p.1 / p.2, p.1 % p.2))
    (encPair encUnary encUnary) (encPair encUnary encUnary) := by fun_prop

example : (19 / 0, 19 % 0) = (0, 19) ∧ (19 / 1, 19 % 1) = (19, 0) := by
  decide +kernel

example : ComputableInPolyTime (fun p : ℤ × ℕ => decide (|p.1 - 1| ≤ (p.2 : ℤ)))
    (encPair encInt encUnary) encBool := by fun_prop

example : Int.natAbs (-1) = 1 ∧ Int.toNat (-1) = 0 ∧ Equiv.intEquivNat (-4) = 7 := by
  decide +kernel

example {γ α : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}
    {values : γ → List α} {value : γ → α} [∀ x, Decidable (value x ∈ values x)]
    (hvalues : ComputableInPolyTime values encIn (encList encA))
    (hvalue : ComputableInPolyTime value encIn encA) :
    ComputableInPolyTime (fun x => decide (value x ∉ values x)) encIn encBool := by fun_prop

example : ComputableInPolyTime (fun p : ℕ × List Bool =>
    Nat.findGreatest (fun i => p.2.getD i false = true) p.1)
      (encPair encUnary encBits) encUnary := by fun_prop

example : Nat.findGreatest (fun i => i ≤ 3) 7 = 3 ∧
    Nat.findGreatest (fun _ => False) 7 = 0 ∧ Nat.findGreatest (fun _ => True) 0 = 0 := by
  decide +kernel

run_meta do
  let retired : List Lean.Name := [
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_natCast,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_negSucc,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_natCast_sub,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_succ,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_pred,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_pos,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_neg,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_toNat,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_natAbs,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_sub_sign,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_abs_le_nat,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_abs_le_nat',
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_equivNat,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_not,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_mem,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_divMod,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_div,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_mod,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_div_const,
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.findGreatest]
  let env ← Lean.getEnv
  for name in retired do
    if env.contains name then
      throwError "superseded unary/search/membership provider remains: {name}"

/-- info: 'Turing.MultiTapeTM.ComputableInPolyTime.unary_divMod' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputableInPolyTime.unary_divMod
