/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm

/-! Binary exponential clocks charge the complete growing output, without unary expansion. -/

open Turing.MultiTapeTM

example : encNat (2 ^ 0) = [true] := rfl

example : encNat (2 ^ 3) = [false, false, false, true] := rfl

example (n : ℕ) : (encNat (2 ^ n)).length = n + 1 := by
  rw [encNat_two_pow, List.length_append, List.length_replicate]
  rfl

-- Both resource degree and independent output degree stay one for arbitrary encodings.
example {α : Type*} (input : α ↪ List Bool) :
    ComputableTidilyInDegree (fun a => 2 ^ (input a).length) input encNat 1 1 :=
  ComputableTidilyInDegree.two_pow_length input

-- The exported contract also supplies an ordinary certificate with those exact degrees.
example : ComputableInDegree (fun n => 2 ^ n) encUnary encNat 1 1 := by
  simpa only [encUnary_apply, List.length_replicate] using
    Internal.forgetDegree (ComputableTidilyInDegree.two_pow_length encUnary)

/-- info: 'Turing.MultiTapeTM.ComputableTidilyInDegree.two_pow_length' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputableTidilyInDegree.two_pow_length
