/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BPP
public import Complexity.Computability.Complexity.Reduction
import Complexity.Foundations.Data.BitString.WordCount
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# BPP is closed under polynomial-time reductions

If `A` reduces to `B` in polynomial time and `B` is in `BPP`, then so is `A`
(`Cslib.Complexity.PolyTimeReducible.mem_BPP`): run the decider of `B` on the reduced instance.
The random string for an instance `a` of `A` must have a length fixed by the length of `a` alone,
so it is taken polynomially long enough for the reduced instance, and the decider reads only the
prefix it expects. Every prefix is extended by the same number of strings, so the fractions of
right answers are unchanged (`Cslib.BitString.card_filter_take`).

## Main results

* `Cslib.Complexity.PolyTimeReducible.mem_BPP`: `BPP` is closed under polynomial-time reductions.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableTidilyInPolyTime

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}

/-- Reading only a prefix of `k` bits multiplies the number of strings giving each answer by the
number `2 ^ j` of extensions of that prefix. -/
theorem card_filter_take_eq (W : List Bool → Bool) (k j : ℕ) (b : Bool) :
    (Finset.univ.filter fun r : Fin (k + j) → Bool => W ((List.ofFn r).take k) = b).card =
      2 ^ j * (Finset.univ.filter fun s : Fin k → Bool => W (List.ofFn s) = b).card := by
  rw [BitString.card_filter_take (Nat.le_add_right k j) fun w => W w = b, Nat.add_sub_cancel_left]

/-- **`BPP` is closed under polynomial-time reductions.** The decider of `A` runs the decider of
`B` on the reduced instance and on the prefix of the random string that this decider expects. -/
theorem PolyTimeReducible.mem_BPP (h : PolyTimeReducible enc encB A B) (hB : B ∈ BPP encB) :
    A ∈ BPP enc := by
  obtain ⟨g, hg, hAB⟩ := h
  obtain ⟨q, W, hW, hWB⟩ := hB
  have hlen : ComputableTidilyInPolyTime (fun a => q.eval (encB (g a)).length) enc encUnary :=
    (unary_eval q).comp ((encoding_length encB).comp hg)
  obtain ⟨c, d, hle⟩ := hlen.polyBounded.exists_le
  refine ⟨Polynomial.C c * (Polynomial.X + 1) ^ d,
    fun x => W (g x.1, x.2.take (q.eval (encB (g x.1)).length)),
    hW.comp ((hg.comp (fst _ _)).prod (bitsTakeWithInput (snd _ _) (hlen.comp (fst _ _)))),
    fun a => ?_⟩
  have hk : q.eval (encB (g a)).length ≤
      (Polynomial.C c * (Polynomial.X + 1) ^ d).eval (enc a).length := by
    simpa using hle a
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hk
  rw [hj]
  have htrue := card_filter_take_eq (fun w => W (g a, w)) (q.eval (encB (g a)).length) j true
  have hfalse := card_filter_take_eq (fun w => W (g a, w)) (q.eval (encB (g a)).length) j false
  rw [htrue, hfalse, pow_add]
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · have := Nat.mul_le_mul_left (2 ^ j) ((hWB (g a)).1 ((hAB a).1 ha))
    linarith
  · have := Nat.mul_le_mul_left (2 ^ j) ((hWB (g a)).2 fun hgB => ha ((hAB a).2 hgB))
    linarith

end Cslib.Complexity
