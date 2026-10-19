/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.PseudorandomGenerator
public import Complexity.Languages.Probabilistic.UniformNat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
import Complexity.Crypto.Game.Hybrid
import Complexity.Computability.Probabilistic.UniformNat
import Complexity.Probability.PMF.Map
import Complexity.Tactic.PPT

/-!
# Polynomial stretch from one-bit pseudorandom generators

Keep a seed of the original length at the front of a word. Each iteration expands that seed
by one bit and retains the previously emitted suffix. The security proof replaces successive
seed expansions by uniform bits, using one uniformly randomized reduction across all hops.
The seed width may differ from the security parameter, and the generator may capture an index.
`indexed_indistinguishable` preserves a secure choice in such a family. Efficiency only needs a
bounded seed prefix; the one-bit length promise is used separately to prove output lengths.

Under the genuine one-bit length invariant (`(generator s).length = s.length + 1`), `iterate` and
`stretch` also admit cumulative quantitative certificates (`ComputableTidilyInTimeAndSpace`) that
stream the emitted bits in forward generation order followed by the reversed final seed
(`forwardIterate`), charging `O(n + k + ∑_{i < k} (tGen(seed_i) + n + 1))` time and `O(Q + n + 1)`
workspace during the streaming loop, and then apply one linear-time zero-workspace reversal
(`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.reverse_bits`) whose composition charges the
`(n + k)`-bit reversal buffer to restore the exact original output order.

## Main definitions

* `PRGStretch.stretch`: repeatedly expand a fixed-width seed prefix and retain emitted bits.
* `PRGStretch.seedStep`, `PRGStretch.emitBit`, `PRGStretch.seedAt`, `PRGStretch.forwardIterate`:
  seed trajectory and forward-streamed intermediate representation before final reversal.
* `PRGStretch.reduction`: one uniform bounded-hop security reduction.

## Main results

* `PRGStretch.polyTime_iterate`: captured functional iteration has a uniform TM certificate.
* `PRGStretch.computableTidilyInTimeAndSpace_forwardIterate`: streaming `k` expansions in forward
  order with cumulative time and `k`-independent workspace `O(Q + n + 1)`.
* `PRGStretch.computableTidilyInTimeAndSpace_iterate_pair`,
  `PRGStretch.computableTidilyInTimeAndSpace_iterate_captured`,
  `PRGStretch.computableTidilyInTimeAndSpace_stretch`,
  `PRGStretch.computableTidilyInDegree_stretch`,
  `PRGStretch.polyTime_stretch_of_length_eq`: quantitative cumulative-time, workspace and degree
  certificates for `iterate` (unparameterized and with captured parameters) and `stretch`,
  preserving the exact reverse-generation output order and recovering `ComputableTidilyInPolyTime`.
* `PRGStretch.advantage_eq`: exact sampling-range loss for the uniform reduction.
* `PseudorandomGenerator.amplify`, `.truncate`: efficient changes of output length.

## References

* [B. Barak, *Pseudorandomness*, CS 127][Barak2016PRG], length extension for PRGs.
  We retain the final seed and reverse the order of the emitted bits. The reduction explicitly
  samples its hop to preserve uniformity, with dyadic padding for strict fair-coin sampling.

Adapted from `Crypto/Computational/Stretch.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the tidy calculus and current upstream games.
-/

@[expose] public section

namespace Cslib.Crypto.PRGStretch

open Probability BitString Turing.MultiTapeTM

/-- Expand the first `n` bits, preserving the previously emitted suffix. -/
def step (generator : List Bool → List Bool) (n : ℕ) (word : List Bool) : List Bool :=
  generator (word.take n) ++ word.drop n

/-- Repeat seed expansion a specified number of times. -/
def iterate (generator : List Bool → List Bool) (n count : ℕ) (word : List Bool) : List Bool :=
  (step generator n)^[count] word

/-- A one-bit generator yields `count n` additional bits from an `n`-bit seed. -/
def stretch (generator : List Bool → List Bool) (count : ℕ → ℕ) (seed : List Bool) : List Bool :=
  iterate generator seed.length (count seed.length) seed

/-- Each call increases the whole word's length by one, even on short intermediate words. -/
theorem length_step {generator : List Bool → List Bool}
    (hlen : ∀ seed, (generator seed).length = seed.length + 1) (n : ℕ) (word : List Bool) :
    (step generator n word).length = word.length + 1 := by
  simp only [step, List.length_append, hlen, List.length_take, List.length_drop]
  lia

/-- The loop's length invariant. -/
theorem length_iterate {generator : List Bool → List Bool}
    (hlen : ∀ seed, (generator seed).length = seed.length + 1) (n count : ℕ) (word : List Bool) :
    (iterate generator n count word).length = word.length + count := by
  induction count with
  | zero => simp [iterate]
  | succ count ih =>
    simp only [iterate, Function.iterate_succ_apply', length_step hlen]
    simp only [iterate] at ih
    lia

/-- A generator need only expand seeds at the specified length. Longer input words carry a
saved suffix, and every subsequent iteration again uses a correctly sized seed prefix. -/
theorem length_iterate_of_le {generator : List Bool → List Bool} {seedBits : ℕ}
    (hlen : ∀ seed, seed.length = seedBits → (generator seed).length = seedBits + 1)
    (count : ℕ) (word : List Bool) (hword : seedBits ≤ word.length) :
    (iterate generator seedBits count word).length = word.length + count := by
  induction count with
  | zero => simp [iterate]
  | succ count ih =>
    rw [iterate, Function.iterate_succ_apply']
    change (step generator seedBits (iterate generator seedBits count word)).length = _
    rw [step, List.length_append, hlen _ (by
      rw [List.length_take, ih]
      exact Nat.min_eq_left (by lia)), List.length_drop, ih]
    lia

/-- A valid seed prefix is expanded independently of the saved suffix. -/
theorem step_append (generator : List Bool → List Bool) {n : ℕ} (seed suffix : List Bool)
    (hlen : seed.length = n) : step generator n (seed ++ suffix) = generator seed ++ suffix := by
  subst n
  simp [step]

/-- Iteration may capture an arbitrary encoded input. Every call reads only a bounded seed
prefix, so polynomial time follows without a length promise on the generator. -/
theorem polyTime_iterate {α : Type} {input : α ↪ List Bool}
    {generator : α → List Bool → List Bool} {seedBits count : α → ℕ} {word : α → List Bool}
    (hgenerator : ComputableTidilyInPolyTime (fun pair => generator pair.1 pair.2)
      (encPair input encBits) encBits)
    (hseedBits : ComputableTidilyInPolyTime seedBits input encUnary)
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    (hword : ComputableTidilyInPolyTime word input encBits) :
    ComputableTidilyInPolyTime (fun a => iterate (generator a) (seedBits a) (count a) (word a))
      input encBits := by
  obtain ⟨c, d, hlength⟩ := hgenerator.polyBounded_length.exists_le
  have hpoly : PolyBounded (fun a => (input a).length)
      (fun a => c * (2 * (input a).length + seedBits a + 2) ^ d) :=
    ComputableTidilyInPolyTime.polyBounded (by fun_prop)
  have hgrowth (a : α) (state : List Bool) :
      (generator a (state.take (seedBits a)) ++ state.drop (seedBits a)).length ≤
        state.length + c * (2 * (input a).length + seedBits a + 2) ^ d := by
    have h := hlength (a, state.take (seedBits a))
    simp only [length_encPair, encBits_apply, List.length_take] at h
    have hbound : (generator a (state.take (seedBits a))).length ≤
        c * (2 * (input a).length + seedBits a + 2) ^ d :=
      h.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by lia) d))
    simp only [List.length_append, List.length_drop]
    lia
  unfold iterate step
  polytime

attribute [program_certificate] polyTime_iterate

/-- Any efficiently computed iteration count gives an efficient generator. -/
theorem polyTime_stretch {generator : List Bool → List Bool} {count : ℕ → ℕ}
    (hgenerator : ComputableTidilyInPolyTime generator encBits encBits)
    (hcount : ComputableTidilyInPolyTime count encUnary encUnary) :
    ComputableTidilyInPolyTime (stretch generator count) encBits encBits := by
  unfold stretch
  polytime

/-! ### Quantitative cumulative-time and workspace certificates -/

/-- The next seed produced by one expansion: all but the last bit of `generator seed`. -/
def seedStep (generator : List Bool → List Bool) (seed : List Bool) : List Bool :=
  (generator seed).dropLast

/-- The single output bit emitted by one expansion, as a 0-or-1-element list. -/
def emitBit (generator : List Bool → List Bool) (seed : List Bool) : List Bool :=
  (generator seed).getLast?.toList

/-- The seed at round `i` of one-bit expansion starting from `seed`. -/
def seedAt (generator : List Bool → List Bool) (seed : List Bool) (i : ℕ) : List Bool :=
  (seedStep generator)^[i] seed

/-- Forward streaming representation of `count` PRG expansions from `seed`: emits each round's bit
in forward generation order, followed by the reversed final seed
`(seedAt generator seed count).reverse`. Reversing this word once yields
`iterate generator seed.length count seed`. -/
def forwardIterate (generator : List Bool → List Bool) (count : ℕ) (seed : List Bool) :
    List Bool :=
  streamEmit (fun p : List Bool × Bool => seedStep generator p.1)
    (fun p => emitBit generator p.1) seed (List.replicate count true) ++
    (seedAt generator seed count).reverse

@[simp]
theorem seedAt_zero (generator : List Bool → List Bool) (seed : List Bool) :
    seedAt generator seed 0 = seed := rfl

theorem seedAt_succ (generator : List Bool → List Bool) (seed : List Bool) (i : ℕ) :
    seedAt generator seed (i + 1) = seedStep generator (seedAt generator seed i) :=
  Function.iterate_succ_apply' _ _ _

/-- A non-empty generator output splits into its next-seed prefix and its emitted bit. -/
theorem seedStep_append_emitBit (generator : List Bool → List Bool) (seed : List Bool)
    (hne : generator seed ≠ []) :
    seedStep generator seed ++ emitBit generator seed = generator seed := by
  unfold seedStep emitBit
  rw [List.getLast?_eq_some_getLast hne, Option.toList_some, List.dropLast_append_getLast hne]

/-- Under the one-bit length promise at width `n`, `seedStep` preserves width `n`. -/
theorem length_seedStep_of_eq {generator : List Bool → List Bool} {n : ℕ}
    (hlen : ∀ s, s.length = n → (generator s).length = n + 1) {s : List Bool} (hs : s.length = n) :
    (seedStep generator s).length = n := by
  simp [seedStep, List.length_dropLast, hlen s hs]

/-- Under the one-bit length promise at width `n`, `emitBit` has length `1`. -/
theorem length_emitBit_of_eq {generator : List Bool → List Bool} {n : ℕ}
    (hlen : ∀ s, s.length = n → (generator s).length = n + 1) {s : List Bool} (hs : s.length = n) :
    (emitBit generator s).length = 1 := by
  have hne : generator s ≠ [] := List.ne_nil_of_length_pos (by have := hlen s hs; omega)
  simp [emitBit, List.getLast?_eq_some_getLast hne]

/-- `emitBit` has at most one element, so reversing it is the identity. -/
@[simp]
theorem reverse_emitBit (generator : List Bool → List Bool) (s : List Bool) :
    (emitBit generator s).reverse = emitBit generator s := by
  unfold emitBit
  cases (generator s).getLast? <;> rfl

/-- Under the one-bit length promise at `seed.length`, every round seed `seedAt generator seed i`
has length `seed.length`. -/
theorem length_seedAt {generator : List Bool → List Bool} {seed : List Bool}
    (hlen : ∀ s, s.length = seed.length → (generator s).length = seed.length + 1) (i : ℕ) :
    (seedAt generator seed i).length = seed.length := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [seedAt_succ]
    exact length_seedStep_of_eq hlen ih

/-- The streaming fold state after `j ≤ count` unary tokens equals `seedAt generator seed j`. -/
theorem streamState_replicate_eq_seedAt (generator : List Bool → List Bool) (seed : List Bool)
    (count j : ℕ) (hj : j ≤ count) :
    streamState seed (fun p : List Bool × Bool => seedStep generator p.1)
      (List.replicate count true) j = seedAt generator seed j := by
  have haux : ∀ (m : ℕ) (s : List Bool),
      (List.replicate m true).foldl (fun acc _ => seedStep generator acc) s =
        (seedStep generator)^[m] s := by
    intro m
    induction m with
    | zero => intro s; rfl
    | succ m ih =>
      intro s
      rw [List.replicate_succ, List.foldl_cons, ih, Function.iterate_succ_apply]
  rw [streamState, List.take_replicate, Nat.min_eq_left hj, haux, seedAt]

/-- Expanding `seed ++ suffix` for `count` rounds produces `seedAt generator seed count`, followed
by the emitted bits in reverse generation order, followed by `suffix`. -/
theorem iterate_append_eq_seedAt_append_streamEmit_reverse {generator : List Bool → List Bool}
    {n : ℕ} (hlen : ∀ s, s.length = n → (generator s).length = n + 1)
    (count : ℕ) {seed : List Bool} (hseed : seed.length = n) (suffix : List Bool) :
    iterate generator n count (seed ++ suffix) =
      seedAt generator seed count ++
        (streamEmit (fun p : List Bool × Bool => seedStep generator p.1)
          (fun p => emitBit generator p.1) seed (List.replicate count true)).reverse ++
        suffix := by
  induction count generalizing seed suffix with
  | zero => simp [iterate, seedAt, streamEmit]
  | succ count ih =>
    have hne : generator seed ≠ [] :=
      List.ne_nil_of_length_pos (by have := hlen seed hseed; omega)
    have hstep_len : (seedStep generator seed).length = n :=
      length_seedStep_of_eq hlen hseed
    rw [iterate, Function.iterate_succ_apply, ← iterate, step_append generator seed suffix hseed,
      ← seedStep_append_emitBit generator seed hne, List.append_assoc,
      ih hstep_len (emitBit generator seed ++ suffix),
      List.replicate_succ, streamEmit, List.reverse_append, reverse_emitBit]
    simp only [seedAt, Function.iterate_succ_apply, List.append_assoc]

/-- Reversing `forwardIterate generator count seed` recovers the exact output of
`iterate generator seed.length count seed` (final seed followed by emitted bits in reverse
generation order). -/
theorem reverse_forwardIterate_eq_iterate {generator : List Bool → List Bool} {seed : List Bool}
    (hlen : ∀ s, s.length = seed.length → (generator s).length = seed.length + 1) (count : ℕ) :
    (forwardIterate generator count seed).reverse =
      iterate generator seed.length count seed := by
  have h := iterate_append_eq_seedAt_append_streamEmit_reverse hlen count rfl []
  simpa only [forwardIterate, List.append_nil, List.reverse_append,
    List.reverse_reverse] using h.symm

/-- `forwardIterate generator count seed` has length `seed.length + count`. -/
theorem length_forwardIterate {generator : List Bool → List Bool} {seed : List Bool}
    (hlen : ∀ s, s.length = seed.length → (generator s).length = seed.length + 1) (count : ℕ) :
    (forwardIterate generator count seed).length = seed.length + count := by
  rw [← List.length_reverse, reverse_forwardIterate_eq_iterate hlen count,
    length_iterate_of_le hlen count seed le_rfl]

theorem length_seedAt_of_forall {generator : List Bool → List Bool}
    (hlen : ∀ s, (generator s).length = s.length + 1) (seed : List Bool) (i : ℕ) :
    (seedAt generator seed i).length = seed.length :=
  length_seedAt (fun s hs => by rw [hlen, hs]) i

theorem reverse_forwardIterate_eq_iterate_of_forall {generator : List Bool → List Bool}
    (hlen : ∀ s, (generator s).length = s.length + 1) (seed : List Bool) (count : ℕ) :
    (forwardIterate generator count seed).reverse =
      iterate generator seed.length count seed :=
  reverse_forwardIterate_eq_iterate (fun s hs => by rw [hlen, hs]) count

theorem length_forwardIterate_of_forall {generator : List Bool → List Bool}
    (hlen : ∀ s, (generator s).length = s.length + 1) (seed : List Bool) (count : ℕ) :
    (forwardIterate generator count seed).length = seed.length + count :=
  length_forwardIterate (fun s hs => by rw [hlen, hs]) count

/-- **Quantitative streaming certificate for `forwardIterate`.** On input `(seed, count)` encoded
with `encPair encBits encUnary`, `forwardIterate` streams `count` rounds directly from the unary
suffix on the input tape, emitting each round's bit in generation order and finishing with the
reversed final seed. Because `streamFold_pair_sum` executes the `emit` and `next` callbacks
sequentially in each round, both generator evaluations are accounted for in the round cost;
workspace is `O(Q + seed.length + 1)`, independent of the round count `count`. -/
theorem computableTidilyInTimeAndSpace_forwardIterate
    {generator : List Bool → List Bool} {tGen sGen : List Bool → ℕ}
    (hlen : ∀ s, (generator s).length = s.length + 1)
    (hgen : ComputableTidilyInTimeAndSpace generator encBits encBits tGen sGen)
    {Q : List Bool × ℕ → ℕ}
    (hspace : ∀ p i, i < p.2 → sGen (seedAt generator p.1 i) ≤ Q p) :
    ∃ c, ComputableTidilyInTimeAndSpace
      (fun p : List Bool × ℕ => forwardIterate generator p.2 p.1)
      (encPair encBits encUnary) encBits
      (fun p => c * (p.1.length + p.2 +
        (∑ i ∈ Finset.range p.2, (tGen (seedAt generator p.1 i) + p.1.length + 1)) + 1))
      (fun p => c * (Q p + p.1.length + 1)) := by
  obtain ⟨cfst, hfst⟩ := PairEncoding.fst (enc₁ := encBits) (enc₂ := encBool)
    (enc := encPair encBits encBool)
  obtain ⟨c₁, hgen_fst⟩ := hgen.comp hfst
  obtain ⟨c₂, hnext₀⟩ := ComputableTidilyInTimeAndSpace.dropLast_bits.comp hgen_fst
  obtain ⟨c₃, hemit₀⟩ := ComputableTidilyInTimeAndSpace.getLast_bits.comp hgen_fst
  set c_step := 3 * cfst + c₁ + c₂ + c₃ + 40
  have hnext : ComputableTidilyInTimeAndSpace
      (fun q : List Bool × Bool => seedStep generator q.1)
      (encPair encBits encBool) encBits
      (fun q => tGen q.1 + c_step * (q.1.length + 1))
      (fun q => sGen q.1 + c_step * (q.1.length + 1)) := by
    change ComputableTidilyInTimeAndSpace (fun q : List Bool × Bool => seedStep generator q.1)
      (encPair encBits encBool) encBits _ _ at hnext₀
    refine hnext₀.mono (fun q => ?_) (fun q => ?_) <;>
      · simp only [Function.comp_apply, length_encPair, encBits_apply, encBool_apply,
          List.length_singleton, hlen q.1, c_step]
        ring_nf
        omega
  have hemit : ComputableTidilyInTimeAndSpace
      (fun q : List Bool × Bool => emitBit generator q.1)
      (encPair encBits encBool) encBits
      (fun q => tGen q.1 + c_step * (q.1.length + 1))
      (fun q => sGen q.1 + c_step * (q.1.length + 1)) := by
    change ComputableTidilyInTimeAndSpace (fun q : List Bool × Bool => emitBit generator q.1)
      (encPair encBits encBool) encBits _ _ at hemit₀
    refine hemit₀.mono (fun q => ?_) (fun q => ?_) <;>
      · simp only [Function.comp_apply, length_encPair, encBits_apply, encBool_apply,
          List.length_singleton, hlen q.1, c_step]
        ring_nf
        omega
  let reader : InputReader Bool Unit := ⟨(), fun _ b => (none, some b)⟩
  set Kstep := 2 * c_step + 4
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.streamFold_pair_sum
    (g := fun p : List Bool × ℕ => forwardIterate generator p.2 p.1)
    (encIn := encPair encBits encUnary) (encOut := encBits)
    reader (fun b => [b]) (fun _ => List.cons_ne_nil _ _)
    (fun a rest => by simp [reader, InputReader.read])
    Prod.fst (fun p => List.replicate p.2 true)
    (fun p => by simp [encPair_apply, encUnary_apply])
    hnext hemit ComputableTidilyInTimeAndSpace.reverse_bits
    (fun p => by
      simp only [forwardIterate, encBits_apply, List.length_replicate,
        streamState_replicate_eq_seedAt generator p.1 p.2 p.2 le_rfl])
    (roundCost := fun p i =>
      Kstep * (tGen (seedAt generator p.1 i) + p.1.length + 1))
    (sMax := fun p => 2 * Q p + Kstep * (p.1.length + 1))
    (lMax := fun p => p.1.length + 1)
    (fun p i hi => by
      have hi' : i < p.2 := by simpa using hi
      rw [streamState_replicate_eq_seedAt generator p.1 p.2 i hi'.le,
        streamState_replicate_eq_seedAt generator p.1 p.2 (i + 1) hi']
      simp only [encBits_apply, encBool_apply, List.length_singleton,
        length_seedAt_of_forall hlen, Kstep]
      nlinarith)
    (fun p i hi => by
      have hi' : i < p.2 := by simpa using hi
      have hsp := hspace p i hi'
      rw [streamState_replicate_eq_seedAt generator p.1 p.2 i hi'.le]
      simp only [length_seedAt_of_forall hlen, Kstep]
      nlinarith)
    (fun p i hi => by
      have hi' : i ≤ p.2 := by simpa using hi
      rw [encBits_apply, streamState_replicate_eq_seedAt generator p.1 p.2 i hi',
        length_seedAt_of_forall hlen]
      omega)
    (fun _ _ _ => by simp)
  refine ⟨c * (Kstep + 10), h.mono (fun p => ?_) (fun p => ?_)⟩
  · have hsum_nonneg :
        0 ≤ ∑ i ∈ Finset.range p.2, (tGen (seedAt generator p.1 i) + p.1.length + 1) :=
      Nat.zero_le _
    simp only [encPair_apply, length_frame, encBits_apply, encUnary_apply, List.length_append,
      List.length_replicate, streamState_replicate_eq_seedAt generator p.1 p.2 p.2 le_rfl,
      length_seedAt_of_forall hlen, ← Finset.mul_sum, Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith

/-- **Quantitative cumulative-time and workspace certificate for `PRGStretch.iterate`.**
Composing `forwardIterate` with the linear-time zero-workspace reversal primitive
`ComputableTidilyInTimeAndSpace.reverse_bits` produces the exact output of
`iterate generator p.1.length p.2 p.1`. The time bound remains
`O(n + k + ∑_{i < k} (tGen(seed_i) + n + 1))`, while the workspace bound `O(Q + n + k + 1)`
explicitly includes the `(n + k)`-bit intermediate reversal buffer. -/
theorem computableTidilyInTimeAndSpace_iterate_pair
    {generator : List Bool → List Bool} {tGen sGen : List Bool → ℕ}
    (hlen : ∀ s, (generator s).length = s.length + 1)
    (hgen : ComputableTidilyInTimeAndSpace generator encBits encBits tGen sGen)
    {Q : List Bool × ℕ → ℕ}
    (hspace : ∀ p i, i < p.2 → sGen (seedAt generator p.1 i) ≤ Q p) :
    ∃ c, ComputableTidilyInTimeAndSpace
      (fun p : List Bool × ℕ => iterate generator p.1.length p.2 p.1)
      (encPair encBits encUnary) encBits
      (fun p => c * (p.1.length + p.2 +
        (∑ i ∈ Finset.range p.2, (tGen (seedAt generator p.1 i) + p.1.length + 1)) + 1))
      (fun p => c * (Q p + p.1.length + p.2 + 1)) := by
  obtain ⟨c₁, hfwd⟩ := computableTidilyInTimeAndSpace_forwardIterate hlen hgen hspace
  obtain ⟨c₂, hrev⟩ := ComputableTidilyInTimeAndSpace.reverse_bits.comp hfwd
  have heq : (List.reverse ∘ fun p : List Bool × ℕ => forwardIterate generator p.2 p.1) =
      fun p : List Bool × ℕ => iterate generator p.1.length p.2 p.1 := by
    funext p
    exact reverse_forwardIterate_eq_iterate_of_forall hlen p.1 p.2
  rw [heq] at hrev
  refine ⟨c₁ + c₂ + 20, hrev.mono (fun p => ?_) (fun p => ?_)⟩
  · have hsum_nonneg :
        0 ≤ ∑ i ∈ Finset.range p.2, (tGen (seedAt generator p.1 i) + p.1.length + 1) :=
      Nat.zero_le _
    simp only [encBits_apply, length_forwardIterate_of_forall hlen]
    nlinarith
  · simp only [encBits_apply, length_forwardIterate_of_forall hlen]
    nlinarith

/-- **Quantitative cumulative-time and workspace certificate for `PRGStretch.stretch`.**
On input `seed : List Bool` of length `n` with `k = count n`, `stretch generator count` runs in
time `O(tCount n + n + k + ∑_{i < k} (tGen(seed_i) + n + 1))` and workspace
`O(sCount n + Q seed + n + k + 1)`, charging `count`, pair assembly, every round's generator
callbacks and seed copying, and the `(n + k)`-bit reversal buffer. -/
theorem computableTidilyInTimeAndSpace_stretch
    {generator : List Bool → List Bool} {count : ℕ → ℕ}
    {tGen sGen : List Bool → ℕ} {tCount sCount : ℕ → ℕ}
    (hlen : ∀ s, (generator s).length = s.length + 1)
    (hgen : ComputableTidilyInTimeAndSpace generator encBits encBits tGen sGen)
    (hcount : ComputableTidilyInTimeAndSpace count encUnary encUnary tCount sCount)
    {Q : List Bool → ℕ}
    (hspace : ∀ seed i, i < count seed.length → sGen (seedAt generator seed i) ≤ Q seed) :
    ∃ c, ComputableTidilyInTimeAndSpace (stretch generator count) encBits encBits
      (fun seed => c * (tCount seed.length + seed.length + count seed.length +
        (∑ i ∈ Finset.range (count seed.length),
          (tGen (seedAt generator seed i) + seed.length + 1)) + 1))
      (fun seed => c * (sCount seed.length + Q seed + seed.length + count seed.length + 1)) := by
  have hlen_unary : ComputableTidilyInTimeAndSpace (fun seed : List Bool => seed.length)
      encBits encUnary (fun seed => 4 * seed.length + 8) (fun _ => 0) := by
    obtain ⟨k, State, hfin, tm, htm⟩ := ComputableTidilyInTimeAndSpace.map_bits (fun _ => true)
    refine ⟨k, State, hfin, tm, fun seed => ?_⟩
    have hmap : List.map (fun _ => true) seed = encUnary seed.length := by
      simp [encUnary_apply, List.map_const']
    exact hmap ▸ htm seed
  obtain ⟨c₁, hcnt_seed⟩ := hcount.comp hlen_unary
  obtain ⟨c₂, hpair⟩ := PairEncoding.pair_mono
    (enc := encPair encBits encUnary) computableTidilyInTimeAndSpace_id hcnt_seed
  obtain ⟨c₃, hiter⟩ := computableTidilyInTimeAndSpace_iterate_pair hlen hgen
    (Q := fun p => Finset.sup (Finset.range p.2) (fun i => sGen (seedAt generator p.1 i)))
    (fun p i hi => Finset.le_sup (f := fun j => sGen (seedAt generator p.1 j))
      (Finset.mem_range.mpr hi))
  obtain ⟨c₄, hcomp⟩ := hiter.comp hpair
  have heq : ((fun p : List Bool × ℕ => iterate generator p.1.length p.2 p.1) ∘
      fun seed : List Bool => (id seed, (count ∘ fun s : List Bool => s.length) seed)) =
      stretch generator count := rfl
  rw [heq] at hcomp
  refine ⟨c₂ * c₁ + 25 * c₂ + c₃ + c₄ + 30, hcomp.mono (fun seed => ?_) (fun seed => ?_)⟩
  · have hsum_nonneg : 0 ≤ ∑ i ∈ Finset.range (count seed.length),
        (tGen (seedAt generator seed i) + seed.length + 1) := Nat.zero_le _
    have hc2c1 : 0 ≤ c₂ * c₁ := Nat.zero_le _
    simp only [Function.comp_apply, id_eq, length_encPair, encBits_apply, encUnary_apply,
      List.length_replicate]
    nlinarith
  · have hQle : Finset.sup (Finset.range (count seed.length))
        (fun i => sGen (seedAt generator seed i)) ≤ Q seed :=
      Finset.sup_le fun i hi => hspace seed i (Finset.mem_range.mp hi)
    have hc2c1 : 0 ≤ c₂ * c₁ := Nat.zero_le _
    simp only [Function.comp_apply, id_eq, length_encPair, encBits_apply, encUnary_apply,
      List.length_replicate]
    nlinarith

/-- **Degree-level quantitative certificate for `PRGStretch.stretch`.**
If `generator` is computable in degree `(dGen, eGen)` and `count` is computable in degree
`(dCount, eCount)`, then under the one-bit length promise `(generator s).length = s.length + 1`,
`stretch generator count` is computable in time/space degree `max dCount (eCount + max dGen 1)` and
output-size degree `max 1 eCount`. -/
theorem computableTidilyInDegree_stretch
    {generator : List Bool → List Bool} {count : ℕ → ℕ}
    {dGen eGen dCount eCount : ℕ}
    (hlen : ∀ s, (generator s).length = s.length + 1)
    (hgen : ComputableTidilyInDegree generator encBits encBits dGen eGen)
    (hcount : ComputableTidilyInDegree count encUnary encUnary dCount eCount) :
    ComputableTidilyInDegree (stretch generator count) encBits encBits
      (max dCount (eCount + max dGen 1)) (max 1 eCount) := by
  obtain ⟨⟨tGen, sGen, ⟨ctG, hctG⟩, ⟨csG, hcsG⟩, hgen_ts⟩, -⟩ := hgen
  obtain ⟨⟨tCount, sCount, ⟨ctC, hctC⟩, ⟨csC, hcsC⟩, hcount_ts⟩, ⟨clC, hclC⟩⟩ := hcount
  obtain ⟨c, hstretch⟩ := computableTidilyInTimeAndSpace_stretch hlen hgen_ts hcount_ts
    (Q := fun seed => csG * (seed.length + 1) ^ dGen)
    (fun seed i _ => by
      simpa only [encBits_apply, length_seedAt_of_forall hlen] using
        hcsG (seedAt generator seed i))
  let size : List Bool → ℕ := fun seed => (encBits seed).length
  let d := max dCount (eCount + max dGen 1)
  have hdCount : dCount ≤ d := le_max_left _ _
  have heGen : eCount + max dGen 1 ≤ d := le_max_right _ _
  have hdGen : dGen ≤ d := (le_max_left dGen 1).trans ((Nat.le_add_left _ eCount).trans heGen)
  have h1 : 1 ≤ d := (le_max_right dGen 1).trans ((Nat.le_add_left _ eCount).trans heGen)
  have heCount : eCount ≤ d := (Nat.le_add_right eCount (max dGen 1)).trans heGen
  have htC : DegreeBounded size (fun seed => tCount seed.length) d :=
    DegreeBounded.mono_deg ⟨ctC, fun s => by simpa [size] using hctC s.length⟩ hdCount
  have hsC : DegreeBounded size (fun seed => sCount seed.length) d :=
    DegreeBounded.mono_deg ⟨csC, fun s => by simpa [size] using hcsC s.length⟩ hdCount
  have hlC_e : DegreeBounded size (fun seed => count seed.length) eCount :=
    ⟨clC, fun s => by simpa [size] using hclC s.length⟩
  have hlC : DegreeBounded size (fun seed => count seed.length) d :=
    hlC_e.mono_deg heCount
  have hseed : DegreeBounded size List.length d :=
    DegreeBounded.self.mono_deg h1
  have hQ : DegreeBounded size (fun seed => csG * (seed.length + 1) ^ dGen) d :=
    DegreeBounded.mono_deg ⟨csG, fun _ => le_rfl⟩ hdGen
  have hround : DegreeBounded size
      (fun seed => ctG * (seed.length + 1) ^ dGen + seed.length + 1) (max dGen 1) :=
    ((DegreeBounded.mono_deg ⟨ctG, fun _ => le_rfl⟩ (le_max_left dGen 1)).add
      (DegreeBounded.self.mono_deg (le_max_right dGen 1))).add_const 1
  have hsum : DegreeBounded size
      (fun seed => ∑ i ∈ Finset.range (count seed.length),
        (tGen (seedAt generator seed i) + seed.length + 1)) d := by
    refine ((hlC_e.mul hround).mono_deg heGen).mono (fun seed => ?_)
    calc ∑ i ∈ Finset.range (count seed.length),
          (tGen (seedAt generator seed i) + seed.length + 1)
      _ ≤ ∑ _i ∈ Finset.range (count seed.length),
          (ctG * (seed.length + 1) ^ dGen + seed.length + 1) := by
        apply Finset.sum_le_sum
        intro i _
        have ht := hctG (seedAt generator seed i)
        simp only [encBits_apply, length_seedAt_of_forall hlen] at ht
        omega
      _ = count seed.length * (ctG * (seed.length + 1) ^ dGen + seed.length + 1) := by
        simp [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hout : DegreeBounded size (fun seed => (encBits (stretch generator count seed)).length)
      (max 1 eCount) := by
    refine ((DegreeBounded.self.mono_deg (le_max_left 1 eCount)).add
      (hlC_e.mono_deg (le_max_right 1 eCount))).mono (fun seed => ?_)
    simp [stretch, length_iterate hlen, size]
  exact ⟨⟨_, _, (((htC.add hseed).add hlC).add hsum).add_const 1 |>.smul c,
    (((hsC.add hQ).add hseed).add hlC).add_const 1 |>.smul c, hstretch⟩, hout⟩

/-- Recover `ComputableTidilyInPolyTime (stretch generator count)` directly as a corollary of the
quantitative streaming theorem `computableTidilyInTimeAndSpace_stretch` (via
`computableTidilyInDegree_stretch`). -/
theorem polyTime_stretch_of_length_eq {generator : List Bool → List Bool} {count : ℕ → ℕ}
    (hlen : ∀ s, (generator s).length = s.length + 1)
    (hgenerator : ComputableTidilyInPolyTime generator encBits encBits)
    (hcount : ComputableTidilyInPolyTime count encUnary encUnary) :
    ComputableTidilyInPolyTime (stretch generator count) encBits encBits := by
  obtain ⟨clG, dlG, hclG⟩ := hgenerator.polyBounded_length.exists_le
  obtain ⟨tG, sG, htG, hsG, hgen_ts⟩ := hgenerator
  obtain ⟨ctG, dtG, hctG⟩ := htG.exists_le
  obtain ⟨csG, dsG, hcsG⟩ := hsG.exists_le
  obtain ⟨clC, dlC, hclC⟩ := hcount.polyBounded_length.exists_le
  obtain ⟨tC, sC, htC, hsC, hcount_ts⟩ := hcount
  obtain ⟨ctC, dtC, hctC⟩ := htC.exists_le
  obtain ⟨csC, dsC, hcsC⟩ := hsC.exists_le
  have hgen_deg : ComputableTidilyInDegree generator encBits encBits (max dtG dsG) dlG :=
    ⟨⟨tG, sG, DegreeBounded.mono_deg ⟨ctG, hctG⟩ (le_max_left _ _),
      DegreeBounded.mono_deg ⟨csG, hcsG⟩ (le_max_right _ _), hgen_ts⟩, ⟨clG, hclG⟩⟩
  have hcount_deg : ComputableTidilyInDegree count encUnary encUnary (max dtC dsC) dlC :=
    ⟨⟨tC, sC, DegreeBounded.mono_deg ⟨ctC, hctC⟩ (le_max_left _ _),
      DegreeBounded.mono_deg ⟨csC, hcsC⟩ (le_max_right _ _), hcount_ts⟩, ⟨clC, hclC⟩⟩
  exact (computableTidilyInDegree_stretch hlen hgen_deg hcount_deg).computableTidilyInPolyTime

/-- **Quantitative cumulative-time and workspace certificate for `PRGStretch.iterate` with a
captured parameter.** On input `((a, seed), count)` encoded with
`encPair (encPair encParam encBits) encUnary`, the streaming state holds `(a, seed_i)` on
`encPair encParam encBits`, so the captured parameter length `(encParam a).length` is charged
alongside `seed.length` in each round's copying cost and in the workspace bound. -/
theorem computableTidilyInTimeAndSpace_iterate_captured {α : Type}
    {encParam : α ↪ List Bool} {generator : α → List Bool → List Bool}
    {tGen sGen : α × List Bool → ℕ}
    (hlen : ∀ a s, (generator a s).length = s.length + 1)
    (hgen : ComputableTidilyInTimeAndSpace (fun p : α × List Bool => generator p.1 p.2)
      (encPair encParam encBits) encBits tGen sGen)
    {Q : (α × List Bool) × ℕ → ℕ}
    (hspace : ∀ x i, i < x.2 → sGen (x.1.1, seedAt (generator x.1.1) x.1.2 i) ≤ Q x) :
    ∃ c, ComputableTidilyInTimeAndSpace
      (fun x : (α × List Bool) × ℕ => iterate (generator x.1.1) x.1.2.length x.2 x.1.2)
      (encPair (encPair encParam encBits) encUnary) encBits
      (fun x => c * ((encParam x.1.1).length + x.1.2.length + x.2 +
        (∑ i ∈ Finset.range x.2,
          (tGen (x.1.1, seedAt (generator x.1.1) x.1.2 i) +
            (encParam x.1.1).length + x.1.2.length + 1)) + 1))
      (fun x => c * (Q x + (encParam x.1.1).length + x.1.2.length + x.2 + 1)) := by
  let encS := encPair encParam encBits
  obtain ⟨cfst, hfst⟩ := PairEncoding.fst (enc₁ := encS) (enc₂ := encBool)
    (enc := encPair encS encBool)
  obtain ⟨cfst_par, hfst_par⟩ := PairEncoding.fst (enc₁ := encParam) (enc₂ := encBits)
    (enc := encS)
  obtain ⟨cpar, hpar⟩ := hfst_par.comp hfst
  obtain ⟨c₁, hgen_fst⟩ := hgen.comp hfst
  obtain ⟨c₂, hdrop⟩ := ComputableTidilyInTimeAndSpace.dropLast_bits.comp hgen_fst
  obtain ⟨cnext, hnext₀⟩ := PairEncoding.pair_mono (enc := encS) hpar hdrop
  obtain ⟨c₃, hemit₀⟩ := ComputableTidilyInTimeAndSpace.getLast_bits.comp hgen_fst
  obtain ⟨csnd, hsnd⟩ := PairEncoding.snd (enc₁ := encParam) (enc₂ := encBits) (enc := encS)
  obtain ⟨cfin, hfin₀⟩ := ComputableTidilyInTimeAndSpace.reverse_bits.comp hsnd
  set c_step := 12 * cnext * cfst + 4 * cnext * cfst_par + cnext * cpar + cnext * c₁ +
    cnext * c₂ + 60 * cnext + 6 * cfst + c₁ + c₃ + 50
  have hnext : ComputableTidilyInTimeAndSpace
      (fun q : (α × List Bool) × Bool => (q.1.1, seedStep (generator q.1.1) q.1.2))
      (encPair encS encBool) encS
      (fun q => cnext * tGen q.1 + c_step * ((encParam q.1.1).length + q.1.2.length + 1))
      (fun q => cnext * sGen q.1 + c_step * ((encParam q.1.1).length + q.1.2.length + 1)) := by
    change ComputableTidilyInTimeAndSpace
      (fun q : (α × List Bool) × Bool => (q.1.1, seedStep (generator q.1.1) q.1.2))
      (encPair encS encBool) encS _ _ at hnext₀
    refine hnext₀.mono (fun q => ?_) (fun q => ?_) <;>
      · have hdrop_len : ((generator q.1.1 q.1.2).dropLast).length = q.1.2.length := by
          rw [List.length_dropLast, hlen, Nat.add_sub_cancel]
        simp only [Function.comp_apply, encS, length_encPair, encBits_apply, encBool_apply,
          List.length_singleton, hlen q.1.1 q.1.2, hdrop_len, c_step]
        ring_nf
        omega
  have hemit : ComputableTidilyInTimeAndSpace
      (fun q : (α × List Bool) × Bool => emitBit (generator q.1.1) q.1.2)
      (encPair encS encBool) encBits
      (fun q => tGen q.1 + c_step * ((encParam q.1.1).length + q.1.2.length + 1))
      (fun q => sGen q.1 + c_step * ((encParam q.1.1).length + q.1.2.length + 1)) := by
    change ComputableTidilyInTimeAndSpace
      (fun q : (α × List Bool) × Bool => emitBit (generator q.1.1) q.1.2)
      (encPair encS encBool) encBits _ _ at hemit₀
    refine hemit₀.mono (fun q => ?_) (fun q => ?_) <;>
      · simp only [Function.comp_apply, encS, length_encPair, encBits_apply, encBool_apply,
          List.length_singleton, hlen q.1.1 q.1.2, c_step]
        ring_nf
        omega
  set c_fin := 3 * csnd + cfin + 15
  have hfin : ComputableTidilyInTimeAndSpace
      (fun s : α × List Bool => s.2.reverse) encS encBits
      (fun s => c_fin * ((encParam s.1).length + s.2.length + 1))
      (fun s => c_fin * ((encParam s.1).length + s.2.length + 1)) := by
    change ComputableTidilyInTimeAndSpace (fun s : α × List Bool => s.2.reverse)
      encS encBits _ _ at hfin₀
    refine hfin₀.mono (fun s => ?_) (fun s => ?_) <;>
      · simp only [encS, length_encPair, encBits_apply, c_fin, Nat.add_mul, Nat.mul_add]
        nlinarith
  let reader : InputReader Bool Unit := ⟨(), fun _ b => (none, some b)⟩
  set Kstep := cnext + 2 * c_step + 6
  have hstate_eq (s₀ : α × List Bool) (k j : ℕ) (hj : j ≤ k) :
      streamState s₀
        (fun p : (α × List Bool) × Bool => (p.1.1, seedStep (generator p.1.1) p.1.2))
        (List.replicate k true) j = (s₀.1, seedAt (generator s₀.1) s₀.2 j) := by
    rcases s₀ with ⟨a, s⟩
    have haux : ∀ (m : ℕ) (s : List Bool),
        (List.replicate m true).foldl
          (fun (acc : α × List Bool) _ => (acc.1, seedStep (generator acc.1) acc.2)) (a, s) =
          (a, (seedStep (generator a))^[m] s) := by
      intro m
      induction m with
      | zero => intro s; rfl
      | succ m ih =>
        intro s
        rw [List.replicate_succ, List.foldl_cons, ih, Function.iterate_succ_apply]
    rw [streamState, List.take_replicate, Nat.min_eq_left hj, haux, seedAt]
  have hemit_eq (s₀ : α × List Bool) (k : ℕ) :
      streamEmit
        (fun p : (α × List Bool) × Bool => (p.1.1, seedStep (generator p.1.1) p.1.2))
        (fun p => emitBit (generator p.1.1) p.1.2)
        s₀ (List.replicate k true) =
      streamEmit
        (fun p : List Bool × Bool => seedStep (generator s₀.1) p.1)
        (fun p => emitBit (generator s₀.1) p.1)
        s₀.2 (List.replicate k true) := by
    rcases s₀ with ⟨a, s⟩
    induction k generalizing s with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ, streamEmit, streamEmit, ih]
  obtain ⟨c_stream, hstream₀⟩ := ComputableTidilyInTimeAndSpace.streamFold_pair_sum
    (g := fun x : (α × List Bool) × ℕ =>
      forwardIterate (generator x.1.1) x.2 x.1.2)
    (encIn := encPair encS encUnary) (encOut := encBits)
    reader (fun b => [b]) (fun _ => List.cons_ne_nil _ _)
    (fun a rest => by simp [reader, InputReader.read])
    Prod.fst (fun x => List.replicate x.2 true)
    (fun x => by simp [encPair_apply, encUnary_apply])
    hnext hemit hfin
    (fun x => by
      simp only [forwardIterate, encBits_apply, List.length_replicate,
        hstate_eq x.1 x.2 x.2 le_rfl, hemit_eq])
    (roundCost := fun x i =>
      Kstep * (tGen (x.1.1, seedAt (generator x.1.1) x.1.2 i) +
        (encParam x.1.1).length + x.1.2.length + 1))
    (sMax := fun x => (cnext + 1) * Q x + Kstep * ((encParam x.1.1).length + x.1.2.length + 1))
    (lMax := fun x => 2 * (encParam x.1.1).length + x.1.2.length + 2)
    (fun x i hi => by
      have hi' : i < x.2 := by simpa using hi
      rw [hstate_eq x.1 x.2 i hi'.le, hstate_eq x.1 x.2 (i + 1) hi']
      simp only [encS, length_encPair, encBits_apply, encBool_apply, List.length_singleton,
        length_seedAt_of_forall (hlen x.1.1), Kstep]
      nlinarith)
    (fun x i hi => by
      have hi' : i < x.2 := by simpa using hi
      have hsp := hspace x i hi'
      rw [hstate_eq x.1 x.2 i hi'.le]
      simp only [length_seedAt_of_forall (hlen x.1.1), Kstep]
      nlinarith)
    (fun x i hi => by
      have hi' : i ≤ x.2 := by simpa using hi
      rw [hstate_eq x.1 x.2 i hi']
      simp only [encS, length_encPair, encBits_apply,
        length_seedAt_of_forall (hlen x.1.1)]
      omega)
    (fun _ _ _ => by simp)
  set c_fwd := c_stream * (Kstep + c_fin + 10)
  have hstream : ComputableTidilyInTimeAndSpace
      (fun x : (α × List Bool) × ℕ => forwardIterate (generator x.1.1) x.2 x.1.2)
      (encPair encS encUnary) encBits
      (fun x => c_fwd * ((encParam x.1.1).length + x.1.2.length + x.2 +
        (∑ i ∈ Finset.range x.2,
          (tGen (x.1.1, seedAt (generator x.1.1) x.1.2 i) +
            (encParam x.1.1).length + x.1.2.length + 1)) + 1))
      (fun x => c_fwd * (Q x + (encParam x.1.1).length + x.1.2.length + 1)) := by
    refine hstream₀.mono (fun x => ?_) (fun x => ?_)
    · have hsum_nonneg : 0 ≤ ∑ i ∈ Finset.range x.2,
          (tGen (x.1.1, seedAt (generator x.1.1) x.1.2 i) +
            (encParam x.1.1).length + x.1.2.length + 1) := Nat.zero_le _
      have hfn : streamState x.1
          (fun p : (α × List Bool) × Bool => (p.1.1, seedStep (generator p.1.1) p.1.2))
          (List.replicate x.2 true) (List.replicate x.2 true).length =
          (x.1.1, seedAt (generator x.1.1) x.1.2 x.2) := by
        rw [List.length_replicate]
        exact hstate_eq x.1 x.2 x.2 le_rfl
      rw [hfn]
      simp only [encS, length_encPair, encBits_apply, encUnary_apply, List.length_replicate,
        length_seedAt_of_forall (hlen x.1.1), ← Finset.mul_sum, c_fwd, Nat.mul_assoc]
      apply Nat.mul_le_mul_left c_stream
      nlinarith
    · have hfn : streamState x.1
          (fun p : (α × List Bool) × Bool => (p.1.1, seedStep (generator p.1.1) p.1.2))
          (List.replicate x.2 true) (List.replicate x.2 true).length =
          (x.1.1, seedAt (generator x.1.1) x.1.2 x.2) := by
        rw [List.length_replicate]
        exact hstate_eq x.1 x.2 x.2 le_rfl
      rw [hfn]
      simp only [length_seedAt_of_forall (hlen x.1.1), Kstep, c_fwd, Nat.mul_assoc]
      apply Nat.mul_le_mul_left c_stream
      nlinarith
  obtain ⟨c_rev, hrev⟩ := ComputableTidilyInTimeAndSpace.reverse_bits.comp hstream
  have heq : (List.reverse ∘ fun x : (α × List Bool) × ℕ =>
      forwardIterate (generator x.1.1) x.2 x.1.2) =
      fun x : (α × List Bool) × ℕ => iterate (generator x.1.1) x.1.2.length x.2 x.1.2 := by
    funext x
    exact reverse_forwardIterate_eq_iterate_of_forall (hlen x.1.1) x.1.2 x.2
  rw [heq] at hrev
  refine ⟨c_fwd + c_rev + 20, hrev.mono (fun x => ?_) (fun x => ?_)⟩
  · have hsum_nonneg : 0 ≤ ∑ i ∈ Finset.range x.2,
        (tGen (x.1.1, seedAt (generator x.1.1) x.1.2 i) +
          (encParam x.1.1).length + x.1.2.length + 1) := Nat.zero_le _
    simp only [encBits_apply, length_forwardIterate_of_forall (hlen x.1.1)]
    nlinarith
  · simp only [encBits_apply, length_forwardIterate_of_forall (hlen x.1.1)]
    nlinarith

/-- Hybrid `i` has `i` genuinely random suffix bits and `total - i` seed expansions left. -/
noncomputable def hybrid (generator : List Bool → List Bool) (n total i : ℕ) : PMF (List Bool) :=
  (uniformList (n + i)).map (iterate generator n (total - i))

/-- The initial hybrid is the stretched generator's output. -/
theorem hybrid_zero (generator : List Bool → List Bool) (count : ℕ → ℕ) (n : ℕ) :
    hybrid generator n (count n) 0 = generatorEnsemble (stretch generator count) n := by
  simp only [hybrid, Nat.add_zero, Nat.sub_zero, generatorEnsemble]
  apply PMF.map_congr_on_support
  intro seed hseed
  simp only [stretch, length_of_mem_support_uniformList hseed]

/-- The final hybrid is uniform at the expanded length. -/
@[simp] theorem hybrid_last (generator : List Bool → List Bool) (n total : ℕ) :
    hybrid generator n total total = uniformList (n + total) := by
  unfold hybrid iterate
  simp only [Nat.sub_self, Function.iterate_zero]
  exact PMF.map_id _

/-- Replacing the challenge by a genuine generator output gives the earlier hybrid. -/
theorem real_hop (generator : List Bool → List Bool) (n total i : ℕ) (hi : i < total) :
    (generatorEnsemble generator n).bind (fun challenge =>
      (uniformList i).map (fun suffix =>
        iterate generator n (total - (i + 1)) (challenge ++ suffix))) =
      hybrid generator n total i := by
  have hcount : total - i = total - (i + 1) + 1 := by lia
  simp only [generatorEnsemble, PMF.bind_map, hybrid,
    uniformList_add, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply PMF.bind_congr_on_support
  intro seed hseed
  congr 1
  funext suffix
  simp only [iterate, hcount, Function.iterate_succ_apply,
    step_append generator seed suffix (length_of_mem_support_uniformList hseed)]

/-- Replacing the challenge by uniform bits gives the next hybrid. -/
theorem ideal_hop (generator : List Bool → List Bool) (n total i : ℕ) :
    (uniformList (n + 1)).bind (fun challenge =>
      (uniformList i).map (fun suffix =>
        iterate generator n (total - (i + 1)) (challenge ++ suffix))) =
      hybrid generator n total (i + 1) := by
  rw [hybrid, show n + (i + 1) = (n + 1) + i by lia, uniformList_add (n + 1) i]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- Embed one challenge at a chosen hop; out-of-range hops reject on both sides. -/
noncomputable def hop (generator : List Bool → List Bool) (count : ℕ → ℕ)
    (adversary : Distinguisher)
    (n i : ℕ) (challenge : List Bool) : ProbComp Bool := do
  if i < count n then
    let suffix ← BitString.sampleList i
    adversary n (iterate generator n (count n - (i + 1)) (challenge ++ suffix))
  else pure false

/-- One uniform reduction samples its hop using a bounded number of fair bits. -/
noncomputable def reduction (generator : List Bool → List Bool) (count : ℕ → ℕ)
    (adversary : Distinguisher) : Distinguisher := fun n challenge => do
  let i ← sampleBoundedIndex (count n)
  hop generator count adversary n i challenge

-- The tactic composes a sampled index, a conditional sample, and the supplied distinguisher.
/-- The reduction's complete efficiency proof uses the public programming interface. -/
@[program_certificate]
theorem isPPT_reduction {generator : List Bool → List Bool} {count : ℕ → ℕ}
    {adversary : Distinguisher} (hgenerator : ComputableTidilyInPolyTime generator encBits encBits)
    (hcount : ComputableTidilyInPolyTime count encUnary encUnary)
    (hadversary : IsPPT encBool adversary) :
    IsPPT encBool (reduction generator count adversary) := by
  unfold reduction hop
  ppt

/-- Apply the same random-hop reduction at an explicit seed length, with any captured test. -/
noncomputable def test (generator : List Bool → List Bool) (seedBits count : ℕ)
    (adversary : List Bool → ProbComp Bool) (challenge : List Bool) : ProbComp Bool :=
  reduction generator (fun _ => count) (fun _ => adversary) seedBits challenge

/-- Captured parameters, generator code, and the adversary compose through the public tactics. -/
@[program_certificate]
theorem isPPT_test {α : Type} {input : α ↪ List Bool}
    {generator : α → List Bool → List Bool} {seedBits count : α → ℕ}
    {adversary : α → List Bool → ProbComp Bool} {challenge : α → List Bool}
    (hgenerator : ComputableTidilyInPolyTime (fun pair => generator pair.1 pair.2)
      (encPair input encBits) encBits)
    (hseedBits : ComputableTidilyInPolyTime seedBits input encUnary)
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    (hadversary : IsPPTOn (encPair input encBits) encBool
      (fun pair => adversary pair.1 pair.2))
    (hchallenge : ComputableTidilyInPolyTime challenge input encBits) :
    IsPPTOn input encBool
      (fun a => test (generator a) (seedBits a) (count a) (adversary a) (challenge a)) := by
  unfold test reduction hop
  ppt

/-- Capping a sampled index only merges rejecting branches. -/
theorem hop_min (generator : List Bool → List Bool) (count : ℕ → ℕ)
    (adversary : Distinguisher)
    (n i : ℕ) (challenge : List Bool) :
    hop generator count adversary n (min (count n) i) challenge =
      hop generator count adversary n i challenge := by
  by_cases hi : i < count n
  · rw [Nat.min_eq_right (by lia)]
  · simp [hop, hi, Nat.min_eq_left (by lia : count n ≤ i)]

/-- The randomized reduction is exactly a uniform mixture of its padded hop reductions. -/
theorem eval_reduction (generator : List Bool → List Bool) (count : ℕ → ℕ)
    (adversary : Distinguisher)
    (n : ℕ) (challenge : List Bool) :
    ProbComp.eval (reduction generator count adversary n challenge) =
      (PMF.uniformOfFintype (Fin (2 ^ (Nat.log 2 (count n) + 1)))).bind
        (fun i => ProbComp.eval (hop generator count adversary n i.val challenge)) := by
  simp only [reduction, ProbComp.eval_bind, eval_sampleBoundedIndex, PMF.bind_map,
    Function.comp_def, hop_min]

/-- The real challenge at a fixed hop realizes the earlier hybrid experiment. -/
theorem eval_real_hop (generator : List Bool → List Bool) (count : ℕ → ℕ)
    (adversary : Distinguisher)
    (n i : ℕ) :
    (generatorEnsemble generator n).bind
        (fun challenge => ProbComp.eval (hop generator count adversary n i challenge)) =
      if i < count n then
        (hybrid generator n (count n) i).bind (fun word => ProbComp.eval (adversary n word))
      else PMF.pure false := by
  by_cases hi : i < count n
  · simp only [hi, ↓reduceIte]
    have h := congrArg (fun distribution : PMF (List Bool) =>
      distribution.bind (fun word => ProbComp.eval (adversary n word)))
      (real_hop generator n (count n) i hi)
    simpa only [hop, hi, ↓reduceIte, ProbComp.eval_bind, eval_sampleList,
      PMF.bind_bind, PMF.bind_map, Function.comp_def] using h
  · simp [hop, hi, PMF.bind_const]

/-- The ideal challenge at a fixed hop realizes the next hybrid experiment. -/
theorem eval_ideal_hop (generator : List Bool → List Bool) (count : ℕ → ℕ)
    (adversary : Distinguisher)
    (n i : ℕ) :
    (uniformList (n + 1)).bind
        (fun challenge => ProbComp.eval (hop generator count adversary n i challenge)) =
      if i < count n then
        (hybrid generator n (count n) (i + 1)).bind (fun word => ProbComp.eval (adversary n word))
      else PMF.pure false := by
  by_cases hi : i < count n
  · simp only [hi, ↓reduceIte]
    have h := congrArg (fun distribution : PMF (List Bool) =>
      distribution.bind (fun word => ProbComp.eval (adversary n word)))
      (ideal_hop generator n (count n) i)
    simpa only [hop, hi, ↓reduceIte, ProbComp.eval_bind, eval_sampleList,
      PMF.bind_bind, PMF.bind_map, Function.comp_def] using h
  · simp [hop, hi, PMF.bind_const]

/-- Exact loss of the uniform reduction, including the padded sampling outcomes. -/
theorem advantage_eq (generator : List Bool → List Bool) (count : ℕ → ℕ)
    (adversary : Distinguisher)
    (n : ℕ) :
    Game.advantage (ProbComp.eval (prgRealGame (stretch generator count) adversary n))
        (ProbComp.eval (prgIdealGame (fun n => n + count n) adversary n)) =
      (2 ^ (Nat.log 2 (count n) + 1) : ℕ) *
        Game.advantage
          (ProbComp.eval (prgRealGame generator (reduction generator count adversary) n))
          (ProbComp.eval
            (prgIdealGame (fun n => n + 1) (reduction generator count adversary) n)) := by
  have hreal : ProbComp.eval (prgRealGame generator (reduction generator count adversary) n) =
      (PMF.uniformOfFintype (Fin (2 ^ (Nat.log 2 (count n) + 1)))).bind (fun i =>
        if i.val < count n then (hybrid generator n (count n) i.val).bind
          (fun word => ProbComp.eval (adversary n word)) else PMF.pure false) := by
    rw [eval_prgRealGame]
    change (generatorEnsemble generator n).bind _ = _
    simp_rw [eval_reduction]
    rw [PMF.bind_comm]
    congr 1
    funext i
    exact eval_real_hop generator count adversary n i.val
  have hideal : ProbComp.eval (prgIdealGame (fun n => n + 1)
      (reduction generator count adversary) n) =
      (PMF.uniformOfFintype (Fin (2 ^ (Nat.log 2 (count n) + 1)))).bind (fun i =>
        if i.val < count n then (hybrid generator n (count n) (i.val + 1)).bind
          (fun word => ProbComp.eval (adversary n word)) else PMF.pure false) := by
    rw [eval_prgIdealGame]
    change (uniformList (n + 1)).bind _ = _
    simp_rw [eval_reduction]
    rw [PMF.bind_comm]
    congr 1
    funext i
    exact eval_ideal_hop generator count adversary n i.val
  have havg := Game.advantage_hybrid_average
    (fun i => (hybrid generator n (count n) i).bind
      (fun word => ProbComp.eval (adversary n word))) (count n)
    (2 ^ (Nat.log 2 (count n) + 1))
    (Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (count n)))
  rw [← hreal, ← hideal, hybrid_zero, hybrid_last] at havg
  simpa only [eval_prgRealGame, eval_prgIdealGame, distinguishingGame] using havg

/-- The same exact loss applies with the seed length independent of the security parameter.
This form is convenient for indexed candidate families. -/
theorem test_advantage_eq (generator : List Bool → List Bool) (seedBits count : ℕ)
    (adversary : List Bool → ProbComp Bool) :
    Game.advantage
      (((uniformList seedBits).map (iterate generator seedBits count)).bind
        (fun word => ProbComp.eval (adversary word)))
      ((uniformList (seedBits + count)).bind (fun word => ProbComp.eval (adversary word))) =
      (2 ^ (Nat.log 2 count + 1) : ℕ) *
        Game.advantage
          (((uniformList seedBits).map generator).bind
            (fun word => ProbComp.eval (test generator seedBits count adversary word)))
          ((uniformList (seedBits + 1)).bind
            (fun word => ProbComp.eval (test generator seedBits count adversary word))) := by
  have h := advantage_eq generator (fun _ => count) (fun _ => adversary) seedBits
  simp only [eval_prgRealGame, eval_prgIdealGame] at h
  rw [← hybrid_zero generator (fun _ => count) seedBits] at h
  simpa only [hybrid, Nat.add_zero, Nat.sub_zero, generatorEnsemble,
    distinguishingGame, test] using h

/-- Padding the sampled hop loses at most twice the number of expansions. -/
theorem advantage_le (generator : List Bool → List Bool) (count : ℕ → ℕ)
    (adversary : Distinguisher)
    (n : ℕ) (hpositive : 0 < count n) :
    Game.advantage (ProbComp.eval (prgRealGame (stretch generator count) adversary n))
        (ProbComp.eval (prgIdealGame (fun n => n + count n) adversary n)) ≤
      (2 * count n : ℕ) *
        Game.advantage
          (ProbComp.eval (prgRealGame generator (reduction generator count adversary) n))
          (ProbComp.eval
            (prgIdealGame (fun n => n + 1) (reduction generator count adversary) n)) := by
  rw [advantage_eq]
  have hpow : 2 ^ (Nat.log 2 (count n) + 1) ≤ 2 * count n := by
    rw [pow_succ]
    have := Nat.pow_log_le_self 2 (by lia : count n ≠ 0)
    lia
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hpow) zero_le

/-- Efficient unary counts give a polynomial bound on the reduction's dyadic loss. -/
theorem loss_polynomial {count : ℕ → ℕ}
    (hcount : ComputableTidilyInPolyTime count encUnary encUnary) :
    PolynomiallyBounded (fun n => 2 ^ (Nat.log 2 (count n) + 1)) :=
  dyadicSize_polynomiallyBounded.comp hcount.polynomiallyBounded

/-- Polynomially many expansions preserve the secure choice in a uniformly efficient family.
The choice is supplied only in the proof; each reduction receives its index as ordinary input. -/
theorem indexed_indistinguishable {generator : ℕ → ℕ → List Bool → List Bool}
    {seedBits count choose : ℕ → ℕ}
    (hgenerator : ComputableTidilyInPolyTime
      (fun input => generator input.1.1 input.1.2 input.2)
      (encPair (encPair encUnary encUnary) encBits) encBits)
    (hseedBits : ComputableTidilyInPolyTime seedBits encUnary encUnary)
    (hcount : ComputableTidilyInPolyTime count encUnary encUnary)
    (hsecure : ∀ adversary : ℕ → ℕ → List Bool → ProbComp Bool,
      IsPPTOn (encPair (encPair encUnary encUnary) encBits)
        encBool (fun input => adversary input.1.1 input.1.2 input.2) →
      Negligible (fun n => Game.advantage
        (((uniformList (seedBits n)).map (generator n (choose n))).bind
          (fun word => ProbComp.eval (adversary n (choose n) word)))
        ((uniformList (seedBits n + 1)).bind
          (fun word => ProbComp.eval (adversary n (choose n) word))))) :
    ∀ adversary : ℕ → ℕ → List Bool → ProbComp Bool,
      IsPPTOn (encPair (encPair encUnary encUnary) encBits)
        encBool (fun input => adversary input.1.1 input.1.2 input.2) →
      Negligible (fun n => Game.advantage
        (((uniformList (seedBits n)).map
          (iterate (generator n (choose n)) (seedBits n) (count n))).bind
            (fun word => ProbComp.eval (adversary n (choose n) word)))
        ((uniformList (seedBits n + count n)).bind
          (fun word => ProbComp.eval (adversary n (choose n) word)))) := by
  intro adversary hadversary
  let reduction := fun n index =>
    test (generator n index) (seedBits n) (count n) (adversary n index)
  have hprepare : ComputableTidilyInPolyTime
      (fun p : ((ℕ × ℕ) × List Bool) × List Bool => (p.1.1, p.2))
      (encPair (encPair (encPair encUnary encUnary) encBits) encBits)
      (encPair (encPair encUnary encUnary) encBits) := by fun_prop
  have hreduce : IsPPTOn (encPair (encPair encUnary encUnary) encBits)
      encBool (fun input => reduction input.1.1 input.1.2 input.2) := by
    unfold reduction
    exact isPPT_test (hgenerator.comp hprepare) (by polytime) (by polytime)
      (hadversary.preprocess hprepare) (by polytime)
  have h := (hsecure reduction hreduce).polynomiallyBounded_mul (loss_polynomial hcount)
  exact h.congr' (Filter.Eventually.of_forall (fun n => (test_advantage_eq _ _ _ _).symm))

/-- Polynomially many seed expansions preserve computational indistinguishability. -/
theorem indistinguishable {generator : List Bool → List Bool} {count : ℕ → ℕ}
    (hgenerator : PseudorandomGenerator generator (fun n => n + 1))
    (hcount : ComputableTidilyInPolyTime count encUnary encUnary) :
    ComputationallyIndistinguishable (generatorEnsemble (stretch generator count))
      (fun n => uniformList (n + count n)) := by
  intro adversary hadversary
  have hreduce := isPPT_reduction hgenerator.polyTime hcount hadversary
  have hnegligible := hgenerator.indistinguishable _ hreduce
  have hloss := hnegligible.polynomiallyBounded_mul (loss_polynomial hcount)
  convert hloss using 1
  funext n
  simpa only [eval_prgRealGame, eval_prgIdealGame] using
    advantage_eq generator count adversary n

/-- A positive efficiently computed number of one-bit expansions is a secure PRG. -/
theorem pseudorandomGenerator {generator : List Bool → List Bool} {count : ℕ → ℕ}
    (hgenerator : PseudorandomGenerator generator (fun n => n + 1))
    (hcount : ComputableTidilyInPolyTime count encUnary encUnary)
    (hpositive : ∀ n, 0 < count n) :
    PseudorandomGenerator (stretch generator count) (fun n => n + count n) := by
  refine PseudorandomGenerator.of_indistinguishable
    (polyTime_stretch_of_length_eq hgenerator.length_eq hgenerator.polyTime hcount) ?_ ?_
    (indistinguishable hgenerator hcount)
  · intro seed
    exact length_iterate hgenerator.length_eq _ _ _
  · intro n
    exact Nat.lt_add_of_pos_right (hpositive n)

end Cslib.Crypto.PRGStretch

namespace Cslib.Crypto

open Probability BitString Turing.MultiTapeTM

/-- Amplify a one-bit PRG to any efficiently computed, strictly larger output length. -/
theorem PseudorandomGenerator.amplify {generator : List Bool → List Bool}
    (hgenerator : PseudorandomGenerator generator (fun n => n + 1))
    (target : ℕ → ℕ) (htarget : ComputableTidilyInPolyTime target encUnary encUnary)
    (hstretch : ∀ n, n < target n) :
    PseudorandomGenerator (PRGStretch.stretch generator (fun n => target n - n)) target := by
  have hcount : ComputableTidilyInPolyTime (fun n => target n - n) encUnary encUnary := by polytime
  have h := PRGStretch.pseudorandomGenerator hgenerator hcount (fun n => by
    have := hstretch n
    lia)
  convert h using 1
  funext n
  have := hstretch n
  lia

/-- Truncating a PRG to an efficiently computed, still-expanding length preserves security. -/
theorem PseudorandomGenerator.truncate {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hgenerator : PseudorandomGenerator generator length)
    (target : ℕ → ℕ)
    (htarget : ComputableTidilyInPolyTime target encUnary encUnary)
    (hle : ∀ n, target n ≤ length n) (hstretch : ∀ n, n < target n) :
    PseudorandomGenerator (fun seed => (generator seed).take (target seed.length)) target := by
  have hpoly := hgenerator.polyTime
  refine PseudorandomGenerator.of_indistinguishable (by polytime) ?_ hstretch ?_
  · intro seed
    simp only [List.length_take, hgenerator.length_eq, Nat.min_eq_left (hle _)]
  · have h := hgenerator.indistinguishable.map
      (f := fun n word => word.take (target n)) (by polytime)
    simpa only [← generatorEnsemble_postprocess generator (fun n word => word.take (target n)),
      uniformList_take (hle _)] using h

end Cslib.Crypto
