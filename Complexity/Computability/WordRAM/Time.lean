/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate (based on edemaine/lean-trominoes @6d5b36c1)

public import Complexity.Computability.WordRAM.Defs
public import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
public import Mathlib.Data.Nat.Log

/-!
# Time-bounded decision on the word RAM

A word-RAM algorithm is analysed for word sizes `w` of order `log n`, where `n` is the size of the
instance [Cormen et al., Section 2.2][CLRS2009]. Two ways of making this precise are useful, and
the first implies the second.

* **Uniform decision** (`Cslib.WordRAM.DecidesInTime`): one program answers correctly within the
  time bound at *every* word size `w ≥ bits a` that accommodates the input words, as in the
  transdichotomous model of [Fredman and Willard][FredmanWillard1993]. This is the strong form,
  in which upper bounds should be proved; the classes
  `Cslib.WordRAM.LinearTime` and `Cslib.WordRAM.PolynomialTime` take `bits a` to be a constant
  multiple of the length of the size of `a`.
* **Decision at a given word size** (`Cslib.WordRAM.DecidesInTimeAt`): one program answers
  correctly at the word size `width a`, which it may read (`Cslib.WordRAM.Op.width`). This is the
  weak form, against which lower bounds should be stated: `Cslib.WordRAM.DecidesInTime.at` shows
  that a uniform decider decides at every word size above its threshold.

For a program that does not read the word size, answering correctly at one word size implies
answering correctly at every larger one (`Cslib.WordRAM.Program.Answers.mono`), so the uniform
form only asks for correctness at the threshold.

The word size of the weak form should depend on an instance only through its size: a program can
read the word size, so a word size that depends on an instance in any other way passes
information about it to the program.

## Main definitions

* `Cslib.WordRAM.Program.Answers`: a program answers a yes/no question on an input at a word size
  within a number of instructions.
* `Cslib.WordRAM.DecidesInTime`, `Cslib.WordRAM.DecidesInTimeAt`: uniform decision, and decision
  at a given word size.
* `Cslib.WordRAM.LinearTime`, `Cslib.WordRAM.PolynomialTime`: linear and polynomial time with
  words of `O(log n)` bits.

## Main results

* `Cslib.WordRAM.DecidesInTime.at`: a uniform decider decides at every word size above its
  threshold.
* `Cslib.WordRAM.Program.Answers.mono`: a program that does not read the word size answers in the
  same way at every larger word size.
* `Cslib.WordRAM.LinearTime.polynomialTime`: linear time is polynomial time.
* `Cslib.WordRAM.DecidesInTime.recode`, `Cslib.WordRAM.PolynomialTime.recode`: decision transfers
  along maps between instance types that preserve the input words.
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

variable {r : ℕ} {α β : Type*}

/-! ## Answering a question -/

/-- `p.Answers w input b time`: run at word size `w` on `input`, the program `p` halts after at
most `time` instructions with output `1` if `b` holds and `0` otherwise. -/
def Program.Answers (p : Program r) (w : ℕ) (input : List ℕ) (b : Prop) (time : ℕ) : Prop :=
  ∃ v n, Executes w p (.init input) v n ∧ n ≤ time ∧ v ≤ 1 ∧ (v = 1 ↔ b)

namespace Program.Answers

variable {p : Program r} {w : ℕ} {input : List ℕ} {b b' : Prop} {time time' : ℕ}

theorem mono_time (h : p.Answers w input b time) (ht : time ≤ time') :
    p.Answers w input b time' :=
  let ⟨v, n, he, hn, hv⟩ := h
  ⟨v, n, he, hn.trans ht, hv⟩

theorem congr (h : p.Answers w input b time) (hb : b ↔ b') : p.Answers w input b' time :=
  let ⟨v, n, he, hn, hv, hb'⟩ := h
  ⟨v, n, he, hn, hv, hb'.trans hb⟩

/-- A program that does not read the word size answers in the same way at every larger word
size. -/
theorem mono (hp : ¬p.ReadsWidth) (h : p.Answers w input b time) {w' : ℕ} (hw : w ≤ w') :
    p.Answers w' input b time :=
  let ⟨v, n, he, hn⟩ := h
  ⟨v, n, he.mono hp hw, hn⟩

end Program.Answers

/-! ## Uniform decision and decision at a given word size -/

/-- **Uniform time-bounded decision.** A single program decides `P` on instances encoded by
`encode`: for every instance `a` and every word size `w ≥ bits a` that accommodates the input
words, it answers whether `P a` within `time a` instructions. Runs that fault do not count. -/
def DecidesInTime (encode : α → List ℕ) (P : α → Prop) (time bits : α → ℕ) : Prop :=
  ∃ r, ∃ p : Program r, ∀ a w, bits a ≤ w → InputFits w (encode a) →
    p.Answers w (encode a) (P a) (time a)

/-- **Decision at a given word size.** A single program decides `P` on instances encoded by
`encode` when run at word size `width a`, provided the input words fit it; the program may read
the word size. -/
def DecidesInTimeAt (encode : α → List ℕ) (P : α → Prop) (time width : α → ℕ) : Prop :=
  ∃ r, ∃ p : Program r, ∀ a, InputFits (width a) (encode a) →
    p.Answers (width a) (encode a) (P a) (time a)

variable {encode : α → List ℕ} {P : α → Prop} {time time' bits bits' width : α → ℕ}

/-- A uniform decider decides at every word size above its threshold. -/
theorem DecidesInTime.at (h : DecidesInTime encode P time bits) (hw : ∀ a, bits a ≤ width a) :
    DecidesInTimeAt encode P time width :=
  let ⟨r, p, hp⟩ := h
  ⟨r, p, fun a ha => hp a (width a) (hw a) ha⟩

theorem DecidesInTime.mono (h : DecidesInTime encode P time bits) (ht : ∀ a, time a ≤ time' a)
    (hb : ∀ a, bits a ≤ bits' a) : DecidesInTime encode P time' bits' :=
  let ⟨r, p, hp⟩ := h
  ⟨r, p, fun a w hw hi => (hp a w ((hb a).trans hw) hi).mono_time (ht a)⟩

theorem DecidesInTimeAt.mono (h : DecidesInTimeAt encode P time width)
    (ht : ∀ a, time a ≤ time' a) : DecidesInTimeAt encode P time' width :=
  let ⟨r, p, hp⟩ := h
  ⟨r, p, fun a ha => (hp a ha).mono_time (ht a)⟩

/-- Decision transfers along a map between instance types that preserves the input words: the
same program decides, and no conversion is charged. -/
theorem DecidesInTime.recode {encode' : β → List ℕ} {Q : β → Prop}
    {timeQ bitsQ : β → ℕ}
    (f : α → β) (hf : ∀ a, encode a = encode' (f a)) (hP : ∀ a, P a ↔ Q (f a))
    (ht : ∀ a, timeQ (f a) ≤ time a) (hb : ∀ a, bitsQ (f a) ≤ bits a)
    (h : DecidesInTime encode' Q timeQ bitsQ) : DecidesInTime encode P time bits :=
  let ⟨r, p, hp⟩ := h
  ⟨r, p, fun a w hw hi => by
    rw [hf] at hi ⊢
    exact ((hp (f a) w ((hb a).trans hw) hi).mono_time (ht a)).congr (hP a).symm⟩

/-! ## Linear and polynomial time -/

/-- The word size `k (⌊log₂ n⌋ + 1)`: `k` times the number of binary digits of `n`. Every word
size of order `log n` lies between two of these. -/
def logWords (k n : ℕ) : ℕ := k * (Nat.log 2 n + 1)

/-- A number below `(n + 1) ^ k` fits a word of `logWords k n` bits. -/
theorem fits_of_lt_pow {k n v : ℕ} (hv : v < (n + 1) ^ k) : Fits (logWords k n) v := by
  have hn : n + 1 ≤ 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two n
  calc v < (n + 1) ^ k := hv
    _ ≤ (2 ^ (Nat.log 2 n + 1)) ^ k := Nat.pow_le_pow_left hn k
    _ = 2 ^ logWords k n := by rw [← pow_mul, logWords, Nat.mul_comm]

theorem logWords_mono {k k' n n' : ℕ} (hk : k ≤ k') (hn : n ≤ n') :
    logWords k n ≤ logWords k' n' :=
  Nat.mul_le_mul hk (Nat.add_le_add_right (Nat.log_mono_right hn) 1)

/-- **Linear time.** A single program decides `P` within `c (size a + 1)` instructions at every
word size of at least `k` times the number of binary digits of `size a`, for some constants `c`
and `k`. -/
def LinearTime (encode : α → List ℕ) (size : α → ℕ) (P : α → Prop) : Prop :=
  ∃ c k, DecidesInTime encode P (fun a => c * (size a + 1)) (fun a => logWords k (size a))

/-- **Polynomial time.** A single program decides `P` within `T (size a)` instructions for a
polynomially bounded `T`, at every word size of at least `k` times the number of binary digits of
`size a`, for some constant `k`. -/
def PolynomialTime (encode : α → List ℕ) (size : α → ℕ) (P : α → Prop) : Prop :=
  ∃ T, PolynomiallyBounded T ∧ ∃ k, DecidesInTime encode P (fun a => T (size a))
    (fun a => logWords k (size a))

theorem LinearTime.polynomialTime {size : α → ℕ} (h : LinearTime encode size P) :
    PolynomialTime encode size P :=
  let ⟨c, k, hd⟩ := h
  ⟨fun n => c * (n + 1), by fun_prop, k, hd⟩

/-- Polynomial time transfers along a map between instance types that preserves the input words
and the sizes. -/
theorem PolynomialTime.recode {encode' : β → List ℕ} {Q : β → Prop} {size : α → ℕ}
    {size' : β → ℕ} (f : α → β) (hf : ∀ a, encode a = encode' (f a))
    (hs : ∀ a, size a = size' (f a)) (hP : ∀ a, P a ↔ Q (f a))
    (h : PolynomialTime encode' size' Q) : PolynomialTime encode size P :=
  let ⟨T, hT, k, hd⟩ := h
  ⟨T, hT, k, hd.recode f hf hP (fun a => by rw [hs]) (fun a => by rw [hs])⟩

/-- Linear time transfers along a map between instance types that preserves the input words and
the sizes. -/
theorem LinearTime.recode {encode' : β → List ℕ} {Q : β → Prop} {size : α → ℕ}
    {size' : β → ℕ} (f : α → β) (hf : ∀ a, encode a = encode' (f a))
    (hs : ∀ a, size a = size' (f a)) (hP : ∀ a, P a ↔ Q (f a))
    (h : LinearTime encode' size' Q) : LinearTime encode size P :=
  let ⟨c, k, hd⟩ := h
  ⟨c, k, hd.recode f hf hP (fun a => by rw [hs]) (fun a => by rw [hs])⟩

end Cslib.WordRAM

end
