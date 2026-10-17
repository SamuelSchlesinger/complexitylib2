/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Foundations.Data.BitString.List.Operations
public import Complexity.Foundations.Data.BitString.List.Binary
public import Complexity.Foundations.Data.BitString.Enumeration
public import Complexity.Computability.BitString.Padding
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Polynomial-time bit-list operations

Raw bit strings and framed lists share the list and iteration calculus. Captured traversals,
Boolean folds, pointwise operations, majority and selected mask sums have compositional
certificates. Runtime dimensions are computed in unary. Enumeration additionally requires a
polynomial bound on the complete encoded output. The operations are total on empty and short lists.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsToList`, `.listToBits`: encoding conversion.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsFrame`, `.bitsPadWord`: self-delimiting
  framing and bounded padding, including arbitrary encoded inputs and overlong words.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsGetElem?`: optional lookup in raw bits.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapToBitsWithInput`, `.bitsFilterWithInput`,
  `.bitsAnyWithInput`, `.bitsFoldlWithInput`, `.bitsZipWithInput`: compositional bit operations.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsStrictMajority`, `.bitsSingle`, `.bitsSingles`,
  `.bitsXorSelected`: finite-mask algorithms.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsCountPWithInput`, `.bitsCountWithInput`:
  unary counts under captured predicates or computed labels.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsNonpositiveMarginWithInput`:
  compare the correct-vote count with the word length.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsEnumList`: output-bounded enumeration.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsBoundedBinaryValue`: capped binary decoding
  to unary, with every intermediate accumulator bounded by the supplied cap.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsReplicate`: repeat a fixed bit.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsRowWithInput`: read one fixed-width row.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsRowsWithInput`: read a runtime number of rows.

## References

Adapted from `Computability/Probabilistic/BitString.lean` and
`Computability/Probabilistic/UniformNat.lean` and
`Crypto/Computational/GoldreichLevin/WordDecoder.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the tidy machine calculus.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- The encoding charges every bit and every delimiter in the enumerated words. -/
theorem length_encList_enumList (count : ℕ) :
    (encList encBits (Cslib.BitString.enumList count)).length =
      2 ^ count * (2 * count + 1) := by
  simp [encList, Cslib.BitString.enumList, List.length_flatMap, List.map_map,
    Function.comp_def]

namespace ComputableTidilyInPolyTime

/-- Frame the existing input encoding, charging every delimiter. -/
@[fun_prop]
theorem bitsFrame {α : Type} (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (fun a => frame (enc a)) enc encBits :=
  .of_linear (.of_frame fun _ => rfl)

/-- Saturating binary decoding to unary is polynomial time on arbitrary input words. -/
@[fun_prop]
theorem bitsBoundedBinaryValue : ComputableTidilyInPolyTime
    (fun p : ℕ × List Bool => Cslib.BitString.boundedBinaryValue p.1 p.2)
    (encPair encUnary encBits) encUnary := by
  apply foldlWith (encA := encBool) (encL := encBits) (encP := encUnary)
    (par := Prod.fst) (list := Prod.snd)
    (step := fun cap value bit => min cap (2 * value + bit.toNat))
    (fst encUnary encBits) (snd encUnary encBits) (const 0) (by fun_prop)
    (B := fun p => p.1)
  · simpa only [encUnary_apply, List.length_replicate] using
      (fst encUnary encBits).polyBounded_length
  · intro p i _
    simpa only [encUnary_apply, List.length_replicate, Cslib.BitString.boundedBinaryValue] using
      Cslib.BitString.boundedBinaryValue_le p.1 (p.2.take i)

/-- Decode computed bits under a computed unary cap, fixing both intermediate encodings. -/
@[fun_prop]
theorem bitsBoundedBinaryValueWithInput {α : Type} {input : α ↪ List Bool}
    {cap : α → ℕ} {word : α → List Bool}
    (hcap : ComputableTidilyInPolyTime cap input encUnary)
    (hword : ComputableTidilyInPolyTime word input encBits) :
    ComputableTidilyInPolyTime (fun a => Cslib.BitString.boundedBinaryValue (cap a) (word a))
      input encUnary := bitsBoundedBinaryValue.comp (hcap.prod hword)

/-- Convert a raw bit string to the framed list encoding. -/
@[fun_prop]
theorem bitsToList : ComputableTidilyInPolyTime (fun l => l) encBits (encList encBool) := by
  have h := foldl_of_bounded_growth (encA := encBool) (encL := encBits)
    (step := fun acc bit => acc ++ [bit]) (init := fun _ => [])
    (id' (encIn := encBits)) (const [])
    (show ComputableTidilyInPolyTime (fun p : List Bool × Bool => p.1 ++ [p.2])
      (encPair (encList encBool) encBool) (encList encBool) by fun_prop)
    (growth := 3) (fun _ _ => by simp)
  simpa only [List.foldl_append_eq_append, List.nil_append, List.flatten_eq_flatMap,
    List.flatMap_map, id_eq, List.flatMap_singleton'] using h

/-- Optional lookup in a raw bit string, fixing the representation of the returned bit. -/
@[fun_prop]
theorem bitsGetElem? {α : Type} {input : α ↪ List Bool}
    {list : α → List Bool} {index : α → ℕ}
    (hlist : ComputableTidilyInPolyTime list input encBits)
    (hindex : ComputableTidilyInPolyTime index input encUnary) :
    ComputableTidilyInPolyTime (fun x => (list x)[index x]?) input (encOption encBool) :=
  getElem? hlist hindex

/-- Remove the framing from a list of bits. -/
@[fun_prop]
theorem listToBits : ComputableTidilyInPolyTime (fun l => l) (encList encBool) encBits := by
  have h := foldl_of_bounded_growth (encA := encBool)
    (step := fun acc bit => acc ++ [bit]) (init := fun _ => [])
    (id' (encIn := encList encBool)) (const [])
    (show ComputableTidilyInPolyTime (fun p : List Bool × Bool => p.1 ++ [p.2])
      (encPair encBits encBool) encBits by fun_prop)
    (growth := 1) (fun _ _ => by simp)
  simpa only [List.foldl_append_eq_append, List.nil_append, List.flatten_eq_flatMap,
    List.flatMap_map, id_eq, List.flatMap_singleton'] using h

/-- Repeat a fixed bit a unary number of times. -/
@[fun_prop]
theorem bitsReplicate (bit : Bool) :
    ComputableTidilyInPolyTime (fun n => List.replicate n bit) encUnary encBits := by
  have h (n : ℕ) : (List.cons bit)^[n] [] = List.replicate n bit := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', ih, List.replicate_succ]
  simpa only [h, id_eq] using iterate_of_bounded_growth (count := id) (init := fun _ : ℕ => [])
    (step := List.cons bit) id' (const []) (by fun_prop) (growth := 1) (fun _ => by simp)

variable {α : Type} {input : α ↪ List Bool}

/-- Self-delimiting padding uses ordinary framing and unary arithmetic. -/
@[fun_prop]
theorem bitsPadWord {bound : α → ℕ} {word : α → List Bool}
    (hbound : ComputableTidilyInPolyTime bound input encUnary)
    (hword : ComputableTidilyInPolyTime word input encBits) :
    ComputableTidilyInPolyTime (fun a => Cslib.BitString.padWord (bound a) (word a))
      input encBits := by
  unfold Cslib.BitString.padWord
  fun_prop

/-- Map a captured Boolean-valued function over a framed list, emitting a raw bit string. -/
@[fun_prop]
theorem mapToBitsWithInput {β : Type} {enc : β ↪ List Bool} {list : α → List β}
    {f : α → β → Bool}
    (hlist : ComputableTidilyInPolyTime list input (encList enc))
    (hf : ComputableTidilyInPolyTime (fun p : α × β => f p.1 p.2)
      (encPair input enc) encBool) :
    ComputableTidilyInPolyTime (fun a => (list a).map (f a)) input encBits :=
  listToBits.comp (mapWithInput hlist hf)

/-- Map a captured Boolean operation over a raw bit string. -/
@[fun_prop]
theorem bitsMapWithInput {list : α → List Bool} {f : α → Bool → Bool}
    (hlist : ComputableTidilyInPolyTime list input encBits)
    (hf : ComputableTidilyInPolyTime (fun p : α × Bool => f p.1 p.2)
      (encPair input encBool) encBool) :
    ComputableTidilyInPolyTime (fun a => (list a).map (f a)) input encBits :=
  mapToBitsWithInput (bitsToList.comp hlist) hf

/-- Filter a raw bit string with a predicate that may capture its original input. -/
@[fun_prop]
theorem bitsFilterWithInput {list : α → List Bool} {test : α → Bool → Bool}
    (hlist : ComputableTidilyInPolyTime list input encBits)
    (htest : ComputableTidilyInPolyTime (fun p : α × Bool => test p.1 p.2)
      (encPair input encBool) encBool) :
    ComputableTidilyInPolyTime (fun a => (list a).filter (test a)) input encBits :=
  listToBits.comp (filterWithInput (bitsToList.comp hlist) htest)

/-- Count predicate matches in a raw bit string, including a captured input. -/
@[fun_prop]
theorem bitsCountPWithInput {list : α → List Bool} {test : α → Bool → Bool}
    (hlist : ComputableTidilyInPolyTime list input encBits)
    (htest : ComputableTidilyInPolyTime (fun p : α × Bool => test p.1 p.2)
      (encPair input encBool) encBool) :
    ComputableTidilyInPolyTime (fun x => (list x).countP (test x)) input encUnary :=
  countPWithInput (bitsToList.comp hlist) htest

/-- Count occurrences of a computed bit in a raw bit string. -/
@[fun_prop]
theorem bitsCountWithInput {list : α → List Bool} {value : α → Bool}
    (hlist : ComputableTidilyInPolyTime list input encBits)
    (hvalue : ComputableTidilyInPolyTime value input encBool) :
    ComputableTidilyInPolyTime (fun x => (list x).count (value x)) input encUnary :=
  countWithInput (bitsToList.comp hlist) hvalue

/-- Test whether any bit satisfies a captured predicate. -/
@[fun_prop]
theorem bitsAnyWithInput {list : α → List Bool} {test : α → Bool → Bool}
    (hlist : ComputableTidilyInPolyTime list input encBits)
    (htest : ComputableTidilyInPolyTime (fun p : α × Bool => test p.1 p.2)
      (encPair input encBool) encBool) :
    ComputableTidilyInPolyTime (fun a => (list a).any (test a)) input encBool :=
  anyWithInput (bitsToList.comp hlist) htest

/-- A Boolean fold has constant-sized state, so no separate state bound is needed. -/
@[fun_prop]
theorem bitsFoldlWithInput (op : Bool → Bool → Bool) {list : α → List Bool} {init : α → Bool}
    (hlist : ComputableTidilyInPolyTime list input encBits)
    (hinit : ComputableTidilyInPolyTime init input encBool) :
    ComputableTidilyInPolyTime (fun a => (list a).foldl op (init a)) input encBool :=
  foldl' (encA := encBool) hlist hinit (of_finite (fun p : Bool × Bool => op p.1 p.2))
    (.const 1) (fun _ _ _ => by simp)

/-- Apply a fixed Boolean operation pointwise, stopping at the shorter word. -/
@[fun_prop]
theorem bitsZipWith (op : Bool → Bool → Bool) :
    ComputableTidilyInPolyTime (fun p : List Bool × List Bool => p.1.zipWith op p.2)
      (encPair encBits encBits) encBits := by
  have hop : ComputableTidilyInPolyTime (fun p : Bool × Bool => op p.1 p.2)
      (encPair encBool encBool) encBool := of_finite _
  have h : ComputableTidilyInPolyTime (fun p : List Bool × List Bool =>
      (List.range (min p.1.length p.2.length)).map
        (fun i => op (p.1.getD i false) (p.2.getD i false)))
      (encPair encBits encBits) encBits := by fun_prop
  convert h using 1
  funext p
  apply List.ext_getElem (by simp)
  intro i hleft hright
  simp only [List.length_zipWith, Nat.lt_min] at hleft
  simp [List.getD, List.getElem?_eq_getElem hleft.1, List.getElem?_eq_getElem hleft.2]

/-- Pointwise operations on computed words, with both intermediate encodings fixed. -/
@[fun_prop]
theorem bitsZipWithInput (op : Bool → Bool → Bool) {left right : α → List Bool}
    (hleft : ComputableTidilyInPolyTime left input encBits)
    (hright : ComputableTidilyInPolyTime right input encBits) :
    ComputableTidilyInPolyTime (fun a => (left a).zipWith op (right a)) input encBits :=
  (bitsZipWith op).comp (hleft.prod hright)

/-- Strict majority uses filtering, length, unary multiplication and comparison. -/
@[fun_prop]
theorem bitsStrictMajority : ComputableTidilyInPolyTime Cslib.BitString.listStrictMajority
    encBits encBool := by
  unfold Cslib.BitString.listStrictMajority
  fun_prop

/-- Strict majority of computed votes fixes the intermediate raw-word encoding. -/
@[fun_prop]
theorem bitsStrictMajorityWithInput {votes : α → List Bool}
    (hvotes : ComputableTidilyInPolyTime votes input encBits) :
    ComputableTidilyInPolyTime (fun a => Cslib.BitString.listStrictMajority (votes a))
      input encBool :=
  bitsStrictMajority.comp hvotes

/-- The training test is polynomial time in the vote list and its supplied label. -/
@[fun_prop]
theorem bitsNonpositiveMarginWithInput
    {votes : α → List Bool} {truth : α → Bool}
    (hvotes : ComputableTidilyInPolyTime votes input encBits)
    (htruth : ComputableTidilyInPolyTime truth input encBool) :
    ComputableTidilyInPolyTime (fun a => Cslib.BitString.listNonpositiveMargin (votes a) (truth a))
      input encBool := by
  unfold Cslib.BitString.listNonpositiveMargin
  fun_prop

/-- Generate one coordinate mask from its unary width and index. -/
@[fun_prop]
theorem bitsSingle : ComputableTidilyInPolyTime
    (fun p : ℕ × ℕ => Cslib.BitString.listSingle p.1 p.2)
    (encPair encUnary encUnary) encBits := by
  unfold Cslib.BitString.listSingle
  fun_prop

/-- Generate all coordinate masks, charging for their quadratic total size. -/
@[fun_prop]
theorem bitsSingles : ComputableTidilyInPolyTime Cslib.BitString.listSingles
    encUnary (encList encBits) := by
  unfold Cslib.BitString.listSingles
  fun_prop

/-- Sum selected rows with a shrinking selector and an accumulator that never grows. -/
@[fun_prop]
theorem bitsXorSelected : ComputableTidilyInPolyTime
    (fun p : ℕ × List Bool × List (List Bool) =>
      Cslib.BitString.listXorSelected p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encBits (encList encBits))) encBits := by
  let advance (state : List Bool × List Bool) (row : List Bool) :=
    (state.1.tail, if state.1.headD false then state.2.zipWith Bool.xor row else state.2)
  have hfold : ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool × List (List Bool) =>
        p.2.2.foldl advance (p.2.1, List.replicate p.1 false))
      (encPair encUnary (encPair encBits (encList encBits))) (encPair encBits encBits) := by
    apply foldl_of_bounded_growth (encA := encBits) (encL := encList encBits) (growth := 0)
    · fun_prop
    · fun_prop
    · unfold advance; fun_prop
    · rintro ⟨selector, value⟩ row
      simp only [advance, length_encPair, encBits_apply, List.length_tail]
      split
      · rw [List.length_zipWith]; lia
      · lia
  exact hfold.snd'

/-- Enumerate words only when their complete encoded size is polynomially bounded.
This does not claim polynomial time in the number of enumerated bits. -/
theorem bitsEnumList {count : α → ℕ}
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    {size : ℕ → ℕ} (hsize : Cslib.PolynomiallyBounded size)
    (hbudget : ∀ a, 2 ^ count a * (2 * count a + 1) ≤ size (input a).length) :
    ComputableTidilyInPolyTime (fun a => Cslib.BitString.enumList (count a))
      input (encList encBits) := by
  let extend (values : List (List Bool)) :=
    values.flatMap (fun word => [false :: word, true :: word])
  have hstep : ComputableTidilyInPolyTime extend (encList encBits) (encList encBits) := by
    unfold extend
    fun_prop
  have hiterate (n : ℕ) : extend^[n] [[]] = Cslib.BitString.enumList n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, Cslib.BitString.enumList_succ]
  have h := iterate (init := fun _ => [[]]) hcount (const [[]]) hstep
    (.of_polynomiallyBounded _ hsize) (fun a index hi => by
      rw [hiterate, length_encList_enumList]
      exact (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0 < 2) hi)
        (by lia : 2 * index + 1 ≤ 2 * count a + 1)).trans (hbudget a))
  simpa only [hiterate] using h

/-- Read a row of a computed word, including the cost of padding a short word. -/
@[fun_prop]
theorem bitsRowWithInput {width row : α → ℕ} {word : α → List Bool}
    (hwidth : ComputableTidilyInPolyTime width input encUnary)
    (hrow : ComputableTidilyInPolyTime row input encUnary)
    (hword : ComputableTidilyInPolyTime word input encBits) :
    ComputableTidilyInPolyTime (fun a => Cslib.BitString.listRow (width a) (row a) (word a))
      input encBits := by
  unfold Cslib.BitString.listRow
  fun_prop

/-- Extract rows from a word with polynomial-time unary dimensions. -/
@[fun_prop]
theorem bitsRowsWithInput {count width : α → ℕ} {word : α → List Bool}
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    (hwidth : ComputableTidilyInPolyTime width input encUnary)
    (hword : ComputableTidilyInPolyTime word input encBits) :
    ComputableTidilyInPolyTime (fun a => Cslib.BitString.listRows (count a) (width a) (word a))
      input (encList encBits) := by
  unfold Cslib.BitString.listRows
  fun_prop

end ComputableTidilyInPolyTime

end Turing.MultiTapeTM
