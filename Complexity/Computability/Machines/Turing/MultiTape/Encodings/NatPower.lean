/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm

/-!
# Powers of two in binary

The binary digits of `2 ^ n`, least significant first, are `n` zeros followed by a one
(`Turing.MultiTapeTM.encNat_two_pow`). So an exponential clock `2 ^ n` is written in linear time,
by a transducer replacing every symbol of a word of length `n` by `false` and appending `true`,
without ever writing `2 ^ n` in unary.

## Main results

* `Turing.MultiTapeTM.encNat_two_pow`: the binary digits of `2 ^ n`.
* `Turing.MultiTapeTM.ComputableInDegree.two_pow_length`: `2 ^ (encIn a).length` is linear.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- The binary digits of `2 ^ n`, least significant first: `n` zeros followed by a one. -/
theorem encNat_two_pow (n : ℕ) : encNat (2 ^ n) = List.replicate n false ++ [true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [encNat_apply, pow_succ, mul_comm, Nat.bit0_bits _ (by positivity), ← encNat_apply, ih,
      List.replicate_succ, List.cons_append]

/-- Replaces every symbol by `false` and appends `true`. -/
def twoPowT : Transducer Bool Unit where
  q₀ := ()
  step _ _ := ((), [false])
  final _ := [true]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

theorem twoPowT_run (w : List Bool) :
    twoPowT.run () w = List.replicate w.length false ++ [true] := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [Transducer.run_cons, ih]
    rfl

/-- **An exponential clock in binary.** `2 ^ (encIn a).length` is computable in linear time
and space, for every encoding of the input. -/
theorem ComputableInDegree.two_pow_length {α : Type*} (encIn : α ↪ List Bool) :
    ComputableInDegree (fun a => 2 ^ (encIn a).length) encIn encNat 1 1 :=
  ComputableInDegree.of_linear
    (twoPowT.computableInLinearTimeAndSpace fun a => by
      rw [encNat_two_pow, twoPowT_run])

end Turing.MultiTapeTM
