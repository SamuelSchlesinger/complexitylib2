/-
Copyright (c) 2026 lean-trominoes contributors, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate (based on edemaine/lean-trominoes @6d5b36c1)

public import Complexity.Computability.WordRAM.Defs
public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Mathlib.Data.Nat.Log

/-!
# Time-bounded decision on the word RAM

These predicates count instructions of the word RAM over a basis of operations
(`Cslib.WordRAM.Basis`), with an explicit input encoding, time bound and word-size parameter. A
word must accommodate the input and its addresses [Cormen et al., Section 2.2][CLRS2009]. Two
contracts are useful, and the first specializes to the second above its threshold.

* **Uniform decision** (`Cslib.WordRAM.Program.DecidesInTime`,
  `Cslib.WordRAM.DecidableInTime`): one program answers correctly within the time bound at
  *every* word size `w ≥ bits a` that accommodates the input words, as in the transdichotomous
  model of [Fredman and Willard][FredmanWillard1993]. The same time bound must work at all these
  widths, even for a program that reads the word size.
* **Decision at a given word size** (`Cslib.WordRAM.Program.DecidesInTimeAt`,
  `Cslib.WordRAM.DecidableInTimeAt`): one program answers correctly at the word size `width a`
  whenever the input fits. The program may read that word size if its basis allows it, as the
  standard basis does (`Cslib.WordRAM.Op.width`).
  `Cslib.WordRAM.DecidableInTime.decidableInTimeAt` gives this conditional contract from a
  uniform decider at every word size above its threshold.

For a program that does not read the word size, answering correctly at one word size implies
answering correctly at every larger one (`Cslib.WordRAM.Program.Answers.mono_width`), so for such a
program the uniform form asks for correctness only at the least word size `w ≥ bits a` that
accommodates the input words.

The prescribed-width contract does not require the input to fit: if no instance fits, every
predicate satisfies it without a successful run. It also permits arbitrary `width a`, which can
pass instance-dependent advice through the width instruction. Thus its unrestricted converse to
uniform decision is false, even when every prescribed width fits. An interpretation as a usual
complexity class needs an input-fit guarantee and a specified size-based width convention;
converting it to another model also needs computability and resource bounds for selecting that
width and for the input encoding. Those assumptions are not bundled in these low-level predicates.

The classes `Cslib.WordRAM.LinearTime` and `Cslib.WordRAM.PolynomialTime` use the uniform form,
with the threshold a constant multiple `k (⌊log₂ n⌋ + 1)` of the number of binary digits of the
size `n`, taking one digit at zero: the time bound must hold at every larger width that fits the
input. The threshold is a lower bound, not an input-fit certificate. For example, singleton
inputs `[m]` have constant word-count size but unbounded bit length. To obtain a logarithmic-width
specialization, supply a fixed `k'` with `InputFits (logWidth k' (size a)) (encode a)` for every
instance and increase the threshold to the maximum of the two constants. The element-distinctness
client supplies such a certificate. Without it these classes do not assert execution with
`O(log(size a))`-bit words. No identification with Turing-machine polynomial time is proved here.

## Main definitions

* `Cslib.WordRAM.Program.Answers`: a program answers a yes/no question on an input at a word size
  within a number of instructions.
* `Cslib.WordRAM.Program.DecidesInTime`, `Cslib.WordRAM.DecidableInTime`: uniform decision by a
  given program, and by some program.
* `Cslib.WordRAM.Program.DecidesInTimeAt`, `Cslib.WordRAM.DecidableInTimeAt`: decision at a given
  word size.
* `Cslib.WordRAM.logWidth`: the word size `k (⌊log₂ n⌋ + 1)`.
* `Cslib.WordRAM.LinearTime`, `Cslib.WordRAM.PolynomialTime`: linear and polynomial instruction
  bounds, uniformly at every fitting word size above a logarithmic lower threshold.

## Main results

* `Cslib.WordRAM.DecidableInTime.decidableInTimeAt`: a uniform decider decides at every word size
  above its threshold.
* `Cslib.WordRAM.Program.Answers.mono_width`: a program that does not read the word size answers
  in the same way at every larger word size.
* `Cslib.WordRAM.LinearTime.polynomialTime`: linear time is polynomial time.
* `Cslib.WordRAM.DecidableInTime.recode`, `Cslib.WordRAM.LinearTime.recode`,
  `Cslib.WordRAM.PolynomialTime.recode`: decision transfers along maps between instance types
  that preserve the input words.
* `Cslib.WordRAM.fits_of_lt_pow`: a number below `(n + 1) ^ k` fits a word of
  `k (⌊log₂ n⌋ + 1)` bits.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
* [M. L. Fredman and D. E. Willard, *Surpassing the information theoretic bound with fusion
  trees*][FredmanWillard1993]
* [MIT–ULB CompGeom Group, *Undecidability of tiling with a tromino*][Tromino2025]; the uniform
  decision predicate is adapted from its accompanying Lean formalization.
-/

@[expose] public section

namespace Cslib.WordRAM

variable {B : Basis} {r : ℕ} {α β : Type*}

/-! ## Answering a question -/

/-- `p.Answers w input b time`: run at word size `w` on `input`, the program `p` halts after at
most `time` instructions with output `1` if `b` holds and `0` otherwise. -/
def Program.Answers (p : Program B r) (w : ℕ) (input : List ℕ) (b : Prop) (time : ℕ) : Prop :=
  ∃ v n, Executes w p (.init input) v n ∧ n ≤ time ∧ v ≤ 1 ∧ (v = 1 ↔ b)

namespace Program.Answers

variable {p : Program B r} {w : ℕ} {input : List ℕ} {b b' : Prop} {time time' : ℕ}

/-- A time bound can be increased. -/
theorem mono (h : p.Answers w input b time) (ht : time ≤ time') : p.Answers w input b time' :=
  let ⟨v, n, he, hn, hv⟩ := h
  ⟨v, n, he, hn.trans ht, hv⟩

theorem congr (h : p.Answers w input b time) (hb : b ↔ b') : p.Answers w input b' time :=
  let ⟨v, n, he, hn, hv, hb'⟩ := h
  ⟨v, n, he, hn, hv, hb'.trans hb⟩

/-- A program that does not read the word size answers in the same way at every larger word
size. -/
theorem mono_width (hp : ¬p.ReadsWidth) (h : p.Answers w input b time) {w' : ℕ} (hw : w ≤ w') :
    p.Answers w' input b time :=
  let ⟨v, n, he, hn⟩ := h
  ⟨v, n, he.mono_width hp hw, hn⟩

end Program.Answers

/-! ## Uniform decision and decision at a given word size -/

/-- **Uniform time-bounded decision.** The program `p` decides `A` on instances encoded by
`encode`: for every instance `a` and every word size `w ≥ bits a` that accommodates the input
words, it answers whether `a ∈ A` within `time a` instructions. Runs that fault do not count.
The input need not fit at the threshold itself. -/
def Program.DecidesInTime (p : Program B r) (encode : α → List ℕ) (A : Set α)
    (time bits : α → ℕ) : Prop :=
  ∀ a w, bits a ≤ w → InputFits w (encode a) → p.Answers w (encode a) (a ∈ A) (time a)

/-- **Decision at a given word size.** The program `p` decides `A` on instances encoded by
`encode` when run at word size `width a`, provided the input words fit it. This is vacuous on
instances that do not fit; the program may read the unrestricted, instance-dependent word size.
No input-fit or size-only width-selection guarantee is included. -/
def Program.DecidesInTimeAt (p : Program B r) (encode : α → List ℕ) (A : Set α)
    (time width : α → ℕ) : Prop :=
  ∀ a, InputFits (width a) (encode a) → p.Answers (width a) (encode a) (a ∈ A) (time a)

/-- Some program over the basis `B` decides `A` uniformly within `time a` instructions at every
word size `w ≥ bits a` that accommodates the input words. -/
def DecidableInTime (B : Basis) (A : Set α) (encode : α → List ℕ) (time bits : α → ℕ) : Prop :=
  ∃ r, ∃ p : Program B r, p.DecidesInTime encode A time bits

/-- Some program over the basis `B` decides `A` within `time a` instructions at the word size
`width a`, conditional on the input fitting. This permits the vacuity and width advice of
`Program.DecidesInTimeAt`. -/
def DecidableInTimeAt (B : Basis) (A : Set α) (encode : α → List ℕ) (time width : α → ℕ) : Prop :=
  ∃ r, ∃ p : Program B r, p.DecidesInTimeAt encode A time width

variable {encode : α → List ℕ} {A : Set α} {time time' bits bits' width : α → ℕ}

namespace Program

variable {p : Program B r}

/-- A uniform decider decides at every word size above its threshold. -/
theorem DecidesInTime.decidesInTimeAt (h : p.DecidesInTime encode A time bits)
    (hw : ∀ a, bits a ≤ width a) : p.DecidesInTimeAt encode A time width :=
  fun a ha => h a (width a) (hw a) ha

/-- Time bounds can be increased and thresholds raised. -/
theorem DecidesInTime.mono (h : p.DecidesInTime encode A time bits)
    (ht : ∀ a, time a ≤ time' a) (hb : ∀ a, bits a ≤ bits' a) :
    p.DecidesInTime encode A time' bits' :=
  fun a w hw hi => (h a w ((hb a).trans hw) hi).mono (ht a)

/-- A program that does not read the word size and answers correctly at the least admissible
word size decides uniformly. -/
theorem decidesInTime_of_not_readsWidth (hp : ¬p.ReadsWidth)
    (h : ∀ a w, bits a ≤ w → InputFits w (encode a) →
      ∃ w₀ ≤ w, bits a ≤ w₀ ∧ p.Answers w₀ (encode a) (a ∈ A) (time a)) :
    p.DecidesInTime encode A time bits :=
  fun a w hw hi =>
    let ⟨_, hw₀, _, h₀⟩ := h a w hw hi
    h₀.mono_width hp hw₀

end Program

/-- A uniform decider decides at every word size above its threshold. -/
theorem DecidableInTime.decidableInTimeAt (h : DecidableInTime B A encode time bits)
    (hw : ∀ a, bits a ≤ width a) : DecidableInTimeAt B A encode time width :=
  let ⟨r, p, hp⟩ := h
  ⟨r, p, hp.decidesInTimeAt hw⟩

/-- Time bounds can be increased and thresholds raised. -/
theorem DecidableInTime.mono (h : DecidableInTime B A encode time bits)
    (ht : ∀ a, time a ≤ time' a) (hb : ∀ a, bits a ≤ bits' a) :
    DecidableInTime B A encode time' bits' :=
  let ⟨r, p, hp⟩ := h
  ⟨r, p, hp.mono ht hb⟩

/-- A time bound can be increased. -/
theorem DecidableInTimeAt.mono (h : DecidableInTimeAt B A encode time width)
    (ht : ∀ a, time a ≤ time' a) : DecidableInTimeAt B A encode time' width :=
  let ⟨r, p, hp⟩ := h
  ⟨r, p, fun a ha => (hp a ha).mono (ht a)⟩

/-- Decision transfers along a map between instance types that preserves the input words: the
same program decides, and no conversion is charged. -/
theorem DecidableInTime.recode {encode' : β → List ℕ} {A' : Set β} {timeB bitsB : β → ℕ}
    (f : α → β) (hf : ∀ a, encode a = encode' (f a)) (hA : ∀ a, a ∈ A ↔ f a ∈ A')
    (ht : ∀ a, timeB (f a) ≤ time a) (hb : ∀ a, bitsB (f a) ≤ bits a)
    (h : DecidableInTime B A' encode' timeB bitsB) : DecidableInTime B A encode time bits :=
  let ⟨r, p, hp⟩ := h
  ⟨r, p, fun a w hw hi => by
    rw [hf] at hi ⊢
    exact ((hp (f a) w ((hb a).trans hw) hi).mono (ht a)).congr (hA a).symm⟩

/-! ## Linear and polynomial time -/

/-- The word size `k (⌊log₂ n⌋ + 1)`: `k` times the number of binary digits of `n` (with `0`
written as one digit, as in `Cslib.RAM.bitLength`). Every word size of order `log n` lies between
two of these. -/
def logWidth (k n : ℕ) : ℕ := k * (Nat.log 2 n + 1)

/-- A number below `(n + 1) ^ k` fits a word of `logWidth k n` bits. -/
theorem fits_of_lt_pow {k n v : ℕ} (hv : v < (n + 1) ^ k) : Fits (logWidth k n) v := by
  have hn : n + 1 ≤ 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two n
  calc v < (n + 1) ^ k := hv
    _ ≤ (2 ^ (Nat.log 2 n + 1)) ^ k := Nat.pow_le_pow_left hn k
    _ = 2 ^ logWidth k n := by rw [← pow_mul, logWidth, Nat.mul_comm]

theorem logWidth_mono {k k' n n' : ℕ} (hk : k ≤ k') (hn : n ≤ n') :
    logWidth k n ≤ logWidth k' n' :=
  Nat.mul_le_mul hk (Nat.add_le_add_right (Nat.log_mono_right hn) 1)

/-- **Linear time.** A single program over the basis `B` decides `A` within `c (size a + 1)`
instructions at every word size of at least `k` times the number of binary digits of `size a`
that accommodates the input words, for some constants `c` and `k`. This does not assert that
inputs fit at any logarithmic word size. -/
def LinearTime (B : Basis) (A : Set α) (encode : α → List ℕ) (size : α → ℕ) : Prop :=
  ∃ c k, DecidableInTime B A encode (fun a => c * (size a + 1)) (fun a => logWidth k (size a))

/-- **Polynomial time.** A single program over the basis `B` decides `A` within `T (size a)`
instructions for a polynomially bounded `T`, at every word size of at least `k` times the number of
binary digits of `size a` that accommodates the input words, for some constant `k`. This does not
assert that inputs fit at any logarithmic word size or identify this class with Turing-machine
polynomial time. -/
def PolynomialTime (B : Basis) (A : Set α) (encode : α → List ℕ) (size : α → ℕ) : Prop :=
  ∃ T, PolynomiallyBounded T ∧ ∃ k, DecidableInTime B A encode (fun a => T (size a))
    (fun a => logWidth k (size a))

theorem LinearTime.polynomialTime {size : α → ℕ} (h : LinearTime B A encode size) :
    PolynomialTime B A encode size :=
  let ⟨c, k, hd⟩ := h
  ⟨fun n => c * (n + 1), polynomiallyBounded_iff_le.2 ⟨c, 1, fun n => by simp⟩, k, hd⟩

/-- Polynomial time transfers along a map between instance types that preserves the input words
and the sizes. -/
theorem PolynomialTime.recode {encode' : β → List ℕ} {A' : Set β} {size : α → ℕ}
    {size' : β → ℕ} (f : α → β) (hf : ∀ a, encode a = encode' (f a))
    (hs : ∀ a, size a = size' (f a)) (hA : ∀ a, a ∈ A ↔ f a ∈ A')
    (h : PolynomialTime B A' encode' size') : PolynomialTime B A encode size :=
  let ⟨T, hT, k, hd⟩ := h
  ⟨T, hT, k, hd.recode f hf hA (fun a => by rw [hs]) (fun a => by rw [hs])⟩

/-- Linear time transfers along a map between instance types that preserves the input words and
the sizes. -/
theorem LinearTime.recode {encode' : β → List ℕ} {A' : Set β} {size : α → ℕ}
    {size' : β → ℕ} (f : α → β) (hf : ∀ a, encode a = encode' (f a))
    (hs : ∀ a, size a = size' (f a)) (hA : ∀ a, a ∈ A ↔ f a ∈ A')
    (h : LinearTime B A' encode' size') : LinearTime B A encode size :=
  let ⟨c, k, hd⟩ := h
  ⟨c, k, hd.recode f hf hA (fun a => by rw [hs]) (fun a => by rw [hs])⟩

end Cslib.WordRAM

end
