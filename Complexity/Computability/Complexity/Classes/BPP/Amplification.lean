/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BPP
public import Complexity.Foundations.Data.BitString.List
import Complexity.Computability.Complexity.Classes.SharpP
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Combinatorics.MajorityVote
import Complexity.Foundations.Data.List.OfFn

/-!
# Error reduction for BPP

The error `1 / 3` in the definition of `BPP` (`Cslib.Complexity.BPP`) can be made exponentially
small [Arora and Barak, Section 7.4.1][AroraBarak09]. Cut the random string into `2 r(n)` blocks of
`p(n)` bits, where `n` is the length of the encoded instance, run the bounded-error decider on
every block and accept when a strict majority, more than `r(n)`, of the runs accept
(`Cslib.Complexity.repeatMajority`). The answer is wrong only when at most half of the runs are
right, which happens on at most an `(8 / 9) ^ r(n)` fraction of the random strings
(`Cslib.card_filter_card_filter_le_le`, an exponential-moment bound). Since `2 * 8 ^ 6 < 9 ^ 6`,
`r = 6 q` runs make the error at most `2 ^ (-q(n))`.

The condition `Cslib.Complexity.DecidesWithErrorExponent enc q p V A` says that `V` errs on at most
a `2 ^ (-q(n))` fraction of the random strings. A problem is in `BPP` exactly when it is decided
in polynomial time with error at most `2 ^ (-q(n))` for every polynomial `q`
(`Cslib.Complexity.mem_BPP_iff_forall_decidesWithErrorExponent`). The one-sided version for `RP`
is `Cslib.Complexity.mem_RP_iff_forall_decidesWithOneSidedErrorExponent`.

## Main definitions

* `Cslib.Complexity.DecidesWithErrorExponent`: error at most `2 ^ (-q(n))`.
* `Cslib.Complexity.repeatMajority`: the strict majority of `2 r(n)` independent runs.

## Main results

* `Cslib.BitString.listRows_ofFn`: the rows of a word of `k * m` bits are its blocks.
* `Cslib.BitString.two_pow_mul_card_filter_card_filter_block_le`: majority votes of `12 e` blocks
  err on at most a `2 ^ (-e)` fraction.
* `Cslib.Complexity.DecidesWithBoundedError.repeatMajority`: `12 q(n)` majority votes reduce the
  error to `2 ^ (-q(n))`.
* `Cslib.Complexity.computableTidilyInPolyTime_repeatMajority`: majority votes take polynomial
  time.
* `Cslib.Complexity.DecidesWithErrorExponent.decidesWithBoundedError`: error at most
  `2 ^ (-q(n)) ≤ 1 / 4` is bounded error.
* `Cslib.Complexity.mem_BPP_iff_forall_decidesWithErrorExponent`: error reduction for `BPP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.BitString

/-- The rows of a word of `k * m` bits are its blocks. -/
theorem listRows_ofFn {k m : ℕ} (x : BitString (k * m)) :
    listRows k m (List.ofFn x) = List.ofFn fun i => List.ofFn (block x i) := by
  rw [listRows_eq_ofFn, ofList_ofFn]

open Finset in
/-- **Majority votes of blocks.** If at least two thirds of the strings of `m` bits satisfy `g`,
then at most a `2 ^ (-e)` fraction of the strings of `2 R = 12 e` blocks of `m` bits have at most
`R` blocks satisfying `g`: the exponential-moment bound `Cslib.card_filter_card_filter_le_le`, with
`2 * 8 ^ 6 ≤ 9 ^ 6`. -/
theorem two_pow_mul_card_filter_card_filter_block_le {m e R : ℕ} (hR : R = 6 * e)
    (g : BitString m → Prop) [DecidablePred g] (hg : 2 * 2 ^ m ≤ 3 * #{s | g s}) :
    2 ^ e * #{x : BitString (2 * R * m) | #{i | g (block x i)} ≤ R} ≤ 2 ^ (2 * R * m) := by
  have hmaj := card_filter_card_filter_le_le (univ.filter g)
    (by simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using hg) R
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, ← pow_mul, Nat.mul_comm m] at hmaj
  have hc : 9 ^ R * #{x : BitString (2 * R * m) | #{i | g (block x i)} ≤ R} ≤
      8 ^ R * 2 ^ (2 * R * m) := by
    refine (Nat.mul_le_mul_left _ ?_).trans hmaj
    rw [← card_map blocksEquiv.toEmbedding]
    refine card_le_card fun ω hω => ?_
    obtain ⟨x, hx, rfl⟩ := mem_map.1 hω
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    simpa only [mem_filter, mem_univ, true_and, Equiv.coe_toEmbedding, blocksEquiv_apply] using hx
  have hq : 2 ^ e * 8 ^ R ≤ 9 ^ R := by
    subst hR
    simp only [pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (by norm_num) _
  refine Nat.le_of_mul_le_mul_left ?_ (by positivity : 0 < 9 ^ R)
  calc 9 ^ R * (2 ^ e * #{x : BitString (2 * R * m) | #{i | g (block x i)} ≤ R})
      = 2 ^ e * (9 ^ R * #{x : BitString (2 * R * m) | #{i | g (block x i)} ≤ R}) := by
        ring
    _ ≤ 2 ^ e * (8 ^ R * 2 ^ (2 * R * m)) := Nat.mul_le_mul_left _ hc
    _ = 2 ^ e * 8 ^ R * 2 ^ (2 * R * m) := by ring
    _ ≤ 9 ^ R * 2 ^ (2 * R * m) := Nat.mul_le_mul_right _ hq

end Cslib.BitString

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

variable {α : Type}

/-- `V` decides `A` with error at most `2 ^ (-q(n))`, using random strings whose length is `p`
evaluated at the length `n` of the encoded instance: for every instance `a`, the random strings `r`
giving the wrong answer, `V (a, r) = false` for members of `A` and `V (a, r) = true` for the
others, make up at most a `2 ^ (-q(n))` fraction. -/
def DecidesWithErrorExponent (enc : α ↪ List Bool) (q p : Polynomial ℕ)
    (V : α × List Bool → Bool) (A : Set α) : Prop :=
  ∀ a, (a ∈ A → 2 ^ q.eval (enc a).length *
      (univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn r) = false).card ≤ 2 ^ p.eval (enc a).length) ∧
    (a ∉ A → 2 ^ q.eval (enc a).length *
      (univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn r) = true).card ≤ 2 ^ p.eval (enc a).length)

/-- The strict majority of `2 r(n)` runs of `V`, where `n` is the length of the encoded instance:
the random string is cut into `2 r(n)` rows of `p(n)` bits (`Cslib.BitString.listRows`), `V` runs
on each row, and the answer is `true` when more than `r(n)` runs accept. Bits missing from a short
random string read as `false`. -/
def repeatMajority (enc : α ↪ List Bool) (r p : Polynomial ℕ) (V : α × List Bool → Bool)
    (x : α × List Bool) : Bool :=
  decide (r.eval (enc x.1).length <
    (BitString.listRows (2 * r.eval (enc x.1).length) (p.eval (enc x.1).length) x.2).countP
      fun row => V (x.1, row))

variable {enc : α ↪ List Bool}

/-- Majority votes of a polynomial-time decider take polynomial time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_repeatMajority {V : α × List Bool → Bool}
    (hV : ComputableTidilyInPolyTime V (encPair enc encBits) encBool) (r p : Polynomial ℕ) :
    ComputableTidilyInPolyTime (repeatMajority enc r p V) (encPair enc encBits) encBool := by
  unfold repeatMajority
  fun_prop

/-- On a random string of `2 r(n)` rows of `p(n)` bits, the majority vote compares the number of
accepting rows with `r(n)`. -/
theorem repeatMajority_ofFn {r p : Polynomial ℕ} {V : α × List Bool → Bool} (a : α)
    (x : BitString (2 * r.eval (enc a).length * p.eval (enc a).length)) :
    repeatMajority enc r p V (a, List.ofFn x) = decide (r.eval (enc a).length <
      (univ.filter fun i => V (a, List.ofFn (BitString.block x i)) = true).card) := by
  rw [repeatMajority, BitString.listRows_ofFn, List.countP_ofFn, card_filter]

/-- **Error reduction for `BPP`** [Arora and Barak, Section 7.4.1][AroraBarak09]. The strict
majority of `12 q(n)` runs of a bounded-error decider, on independent blocks of random bits, errs on
at most a `2 ^ (-q(n))` fraction of the random strings. -/
theorem DecidesWithBoundedError.repeatMajority {p : Polynomial ℕ} {V : α × List Bool → Bool}
    {A : Set α} (h : DecidesWithBoundedError enc p V A) (q : Polynomial ℕ) :
    DecidesWithErrorExponent enc q (12 * q * p) (Complexity.repeatMajority enc (6 * q) p V) A := by
  intro a
  have hlen : (12 * q * p).eval (enc a).length =
      2 * (6 * q).eval (enc a).length * p.eval (enc a).length := by
    simp only [Polynomial.eval_mul, Polynomial.eval_ofNat]
    ring
  have hR : (6 * q).eval (enc a).length = 6 * q.eval (enc a).length := by simp
  rw [hlen]
  constructor
  · -- on a member, the majority rejects only when at most `R` runs accept
    intro ha
    refine (Nat.mul_le_mul_left _ (card_le_card fun x hx => ?_)).trans
      (BitString.two_pow_mul_card_filter_card_filter_block_le hR
        (fun s => V (a, List.ofFn s) = true) ((h a).1 ha))
    rw [mem_filter, repeatMajority_ofFn, decide_eq_false_iff_not, not_lt] at hx
    exact mem_filter.2 ⟨mem_univ _, hx.2⟩
  · -- on a non-member, the majority accepts only when at most `R` runs reject
    intro ha
    refine (Nat.mul_le_mul_left _ (card_le_card fun x hx => ?_)).trans
      (BitString.two_pow_mul_card_filter_card_filter_block_le hR
        (fun s => V (a, List.ofFn s) = false) ((h a).2 ha))
    rw [mem_filter, repeatMajority_ofFn, decide_eq_true_iff] at hx
    have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 *
      (6 * q).eval (enc a).length))))
      fun i => V (a, List.ofFn (BitString.block x i)) = true
    simp only [Bool.not_eq_true, card_univ, Fintype.card_fin] at hsum
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    omega

/-- Error at most `2 ^ (-q(n)) ≤ 1 / 4` is bounded error. -/
theorem DecidesWithErrorExponent.decidesWithBoundedError {q p : Polynomial ℕ}
    {V : α × List Bool → Bool} {A : Set α} (h : DecidesWithErrorExponent enc q p V A)
    (hq : ∀ n, 2 ≤ q.eval n) : DecidesWithBoundedError enc p V A := fun a => by
  have hsum := acceptCount_add_card_filter_eq_false (V := V) (a := a) (n := p.eval (enc a).length)
  have h4 : 2 ^ 2 ≤ 2 ^ q.eval (enc a).length := Nat.pow_le_pow_right (by norm_num) (hq _)
  rw [← acceptCount]
  constructor
  · intro ha
    have := (Nat.mul_le_mul_right _ h4).trans ((h a).1 ha)
    omega
  · intro ha
    have := (Nat.mul_le_mul_right _ h4).trans ((h a).2 ha)
    rw [← acceptCount] at this
    omega

/-- **Error reduction for `BPP`** [Arora and Barak, Section 7.4.1][AroraBarak09]: a problem is in
`BPP` exactly when, for every polynomial `q`, it is decided in polynomial time with error at most
`2 ^ (-q(n))`. -/
theorem mem_BPP_iff_forall_decidesWithErrorExponent {A : Set α} :
    A ∈ BPP enc ↔ ∀ q : Polynomial ℕ, ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧
        DecidesWithErrorExponent enc q p V A := by
  refine ⟨fun ⟨p, V, hV, h⟩ q => ⟨12 * q * p, _,
    computableTidilyInPolyTime_repeatMajority hV _ _, h.repeatMajority q⟩, fun h => ?_⟩
  obtain ⟨p, V, hV, h⟩ := h 2
  exact ⟨p, V, hV, h.decidesWithBoundedError fun _ => by simp⟩

end Cslib.Complexity
