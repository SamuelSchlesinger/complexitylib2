/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Polynomial-time list operations

List operations for the polynomial-time calculus, using Christian Reitwiessner's encodings,
degree-bounded operations and fold rules. Indices use `encUnary`: an index returned by `idxOf`
is at most the list length, irrespective of the encoding of its elements. In particular, looking
up a variable with a large binary label does not require a certificate as long as that label.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.cons`, `.listAppend`, `.map`, `.flatten`:
  constructing lists.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.cons'`, `.listAppend'`: composition rules
  that let `fun_prop` infer the element encoding from the result.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapWith`, `.flatMapWith`: constructing lists
  with a parameter; the input list may itself have polynomial encoded length.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapWithInput`, `.flatMapWithInput`,
  `.filterWithInput`, `.findWithInput`, `.anyWithInput`, `.allWithInput`:
  automation rules for traversals whose body also uses the original input.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapConst`, `.flatMapConst`: traverse a fixed
  list without requiring an encoding of its elements.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.filterWith`, `.findWith`: filtering or searching
  a polynomial-time list with a parameterized test.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.length`, `.range`: unary lengths and ranges.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.anyWith`, `.allWith`: Boolean scans with a
  parameter, applied explicitly like the fold rules.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.idxOf`: the first occurrence of an element.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listGetD`: lookup by a unary index.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listIsEmpty`, `.head?`: inspect a list without
  a default element.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.idxOfWithInput`, `.bitsGetDWithInput`:
  compositional rules for first-occurrence lookup and raw-bit access.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsDropWithInput`, `.bitsTakeWithInput`:
  runtime bit-string slicing, with computed unary indices.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

variable {α β γ π : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {encIn : γ ↪ List Bool} {encP : π ↪ List Bool}

/-- Concatenate raw bit strings, charging for both computed words. -/
@[fun_prop]
theorem bitsAppend {left right : γ → List Bool}
    (hleft : ComputableTidilyInPolyTime left encIn encBits)
    (hright : ComputableTidilyInPolyTime right encIn encBits) :
    ComputableTidilyInPolyTime (fun x => left x ++ right x) encIn encBits :=
  hleft.append hright fun _ => rfl

/-- Prepend a computed bit to a raw bit string. -/
@[fun_prop]
theorem bitsCons {head : γ → Bool} {tail : γ → List Bool}
    (hhead : ComputableTidilyInPolyTime head encIn encBool)
    (htail : ComputableTidilyInPolyTime tail encIn encBits) :
    ComputableTidilyInPolyTime (fun x => head x :: tail x) encIn encBits :=
  hhead.append htail fun _ => rfl

/-- Read the head of any list encoding with a fixed fallback. -/
@[fun_prop]
theorem headD {encL : List α ↪ List Bool} [ListEncoding encA encL] (fallback : α) :
    ComputableTidilyInPolyTime (fun list => list.headD fallback) encL encA :=
  (ComputableTidilyInDegree.headD fallback).computableTidilyInPolyTime

/-- Drop the head of any list encoding. -/
@[fun_prop]
theorem tail {encL : List α ↪ List Bool} [ListEncoding encA encL] :
    ComputableTidilyInPolyTime (List.tail (α := α)) encL encL :=
  (ComputableTidilyInDegree.tail (enc₁ := encA)).computableTidilyInPolyTime

/-- Test emptiness without decoding a list element or requiring a default value. -/
@[fun_prop]
theorem listIsEmpty {encL : List α ↪ List Bool} [ListEncoding encA encL] :
    ComputableTidilyInPolyTime (List.isEmpty (α := α)) encL encBool :=
  of_linear (ListEncoding.isEmpty (enc₁ := encA) (enc := encL))

/-- Drop the head of a framed list, determining its element encoding for automation. -/
@[fun_prop]
theorem listTail (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (List.tail (α := α)) (encList enc) (encList enc) :=
  tail (encA := enc)

/-- Drop the first raw bit. The raw encoding fixes the otherwise undetermined element encoding. -/
@[fun_prop]
theorem bitsTail : ComputableTidilyInPolyTime List.tail encBits encBits := tail (encA := encBool)

/-- Reverse a raw bit string using an accumulator that grows by one bit per step. -/
@[fun_prop]
theorem bitsReverse : ComputableTidilyInPolyTime List.reverse encBits encBits := by
  have h := foldl_of_bounded_growth (encA := encBool) (encL := encBits)
    (step := fun reversed bit => bit :: reversed) (init := fun _ => [])
    (id' (encIn := encBits)) (const [])
    (show ComputableTidilyInPolyTime (fun p : List Bool × Bool => p.2 :: p.1)
      (encPair encBits encBool) encBits by fun_prop)
    (growth := 1) (fun _ _ => by simp)
  simpa using h

/-- Prepending an element to a framed list is polynomial-time. -/
@[fun_prop]
theorem cons (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (fun p : α × List α => p.1 :: p.2)
      (encPair enc (encList enc)) (encList enc) :=
  (ComputableTidilyInDegree.cons enc).computableTidilyInPolyTime

/-- Concatenating two framed lists is polynomial-time. -/
@[fun_prop]
theorem listAppend (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (fun p : List α × List α => p.1 ++ p.2)
      (encPair (encList enc) (encList enc)) (encList enc) :=
  (ComputableTidilyInDegree.listAppend enc).computableTidilyInPolyTime

/-- Prepend computed data. The result encoding determines the element encoding before
`fun_prop` searches for the two component certificates. -/
@[fun_prop]
theorem cons' {head : γ → α} {tail : γ → List α}
    (hhead : ComputableTidilyInPolyTime head encIn encA)
    (htail : ComputableTidilyInPolyTime tail encIn (encList encA)) :
    ComputableTidilyInPolyTime (fun x => head x :: tail x) encIn (encList encA) :=
  (cons encA).comp (hhead.prod htail)

/-- Concatenate computed lists, inferring their shared encoding from the result. -/
@[fun_prop]
theorem listAppend' {left right : γ → List α}
    (hleft : ComputableTidilyInPolyTime left encIn (encList encA))
    (hright : ComputableTidilyInPolyTime right encIn (encList encA)) :
    ComputableTidilyInPolyTime (fun x => left x ++ right x) encIn (encList encA) :=
  (listAppend encA).comp (hleft.prod hright)

/-- Find the first element passing a polynomial-time test with a fixed parameter.
The list may have any polynomial encoded length. -/
theorem findWith {test : π × α → Bool} {par : γ → π} {list : γ → List α}
    (htest : ComputableTidilyInPolyTime test (encPair encP encA) encBool)
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA)) :
    ComputableTidilyInPolyTime (fun x => (list x).find? fun a => test (par x, a))
      encIn (encOption encA) := by
  obtain ⟨d, e, htest⟩ := htest.exists_degree
  exact (ComputableTidilyInDegree.findWith htest
    (ComputableTidilyInDegree.fst encP (encList encA))
    (ComputableTidilyInDegree.snd encP (encList encA))).computableTidilyInPolyTime.comp
      (hpar.prod hlist)

/-- Search with a predicate that captures the original input. -/
@[fun_prop]
theorem findWithInput {test : γ → α → Bool} {list : γ → List α}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (htest : ComputableTidilyInPolyTime (fun p : γ × α => test p.1 p.2)
      (encPair encIn encA) encBool) :
    ComputableTidilyInPolyTime (fun x => (list x).find? (test x)) encIn (encOption encA) :=
  findWith htest id' hlist

/-- Keep the elements passing a polynomial-time test with a fixed parameter.
The input list may have any polynomial encoded length. -/
theorem filterWith {test : π × α → Bool} {par : γ → π} {list : γ → List α}
    (htest : ComputableTidilyInPolyTime test (encPair encP encA) encBool)
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA)) :
    ComputableTidilyInPolyTime (fun x => (list x).filter fun a => test (par x, a))
      encIn (encList encA) := by
  obtain ⟨d, e, htest⟩ := htest.exists_degree
  exact (ComputableTidilyInDegree.filterWith htest
    (ComputableTidilyInDegree.fst encP (encList encA))
    (ComputableTidilyInDegree.snd encP (encList encA))).computableTidilyInPolyTime.comp
      (hpar.prod hlist)

/-- Filter with a predicate that captures the original input. -/
@[fun_prop]
theorem filterWithInput {test : γ → α → Bool} {list : γ → List α}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (htest : ComputableTidilyInPolyTime (fun p : γ × α => test p.1 p.2)
      (encPair encIn encA) encBool) :
    ComputableTidilyInPolyTime (fun x => (list x).filter (test x)) encIn (encList encA) :=
  filterWith htest id' hlist

/-- Filtering a list by a polynomial-time test is polynomial-time. -/
@[fun_prop]
theorem filter {test : α → Bool} (htest : ComputableTidilyInPolyTime test encA encBool) :
    ComputableTidilyInPolyTime (List.filter test) (encList encA) (encList encA) :=
  filterWith (htest.comp (snd encBool encA)) (const true) id'

/-- Map a polynomial-time function with a fixed parameter over a polynomial-time computable list.
The list may have any polynomial encoded length. -/
theorem mapWith {f : π × α → β} {par : γ → π} {list : γ → List α}
    (hf : ComputableTidilyInPolyTime f (encPair encP encA) encB)
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA)) :
    ComputableTidilyInPolyTime (fun x => (list x).map fun a => f (par x, a))
      encIn (encList encB) := by
  obtain ⟨d, e, hf⟩ := hf.exists_degree
  exact (ComputableTidilyInDegree.mapWith hf
    (ComputableTidilyInDegree.fst encP (encList encA))
    (ComputableTidilyInDegree.snd encP (encList encA))).computableTidilyInPolyTime.comp
      (hpar.prod hlist)

/-- Map a function that also uses the original input. A single joint certificate in the input
and list element makes the cost uniform across all elements. The list certificate is supplied
first so that `fun_prop` can infer its element encoding before checking the body. -/
@[fun_prop]
theorem mapWithInput {f : γ → α → β} {list : γ → List α}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (hf : ComputableTidilyInPolyTime (fun p : γ × α => f p.1 p.2)
      (encPair encIn encA) encB) :
    ComputableTidilyInPolyTime (fun x => (list x).map (f x)) encIn (encList encB) :=
  mapWith hf id' hlist

/-- A polynomial-time function can be mapped over a list in polynomial time. -/
@[fun_prop]
theorem map {f : α → β} (hf : ComputableTidilyInPolyTime f encA encB) :
    ComputableTidilyInPolyTime (List.map f) (encList encA) (encList encB) :=
  mapWith (hf.comp (snd encBool encA)) (const true) id'

/-- Read an optional head without an inhabitant of the element type. -/
@[fun_prop]
theorem head? (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (List.head? (α := α)) (encList enc) (encOption enc) := by
  apply ((headD (encA := encOption enc) none).comp (map (optionSome enc))).of_enc_eq
  intro values
  cases values <;> rfl

/-- Map an input-dependent function over a fixed list. Only its members need certificates;
the list and its elements are not part of the computational input. -/
@[fun_prop]
theorem mapConst {ι : Type*} (l : List ι) {f : γ → ι → β}
    (hf : ∀ i ∈ l, ComputableTidilyInPolyTime (fun x => f x i) encIn encB) :
    ComputableTidilyInPolyTime (fun x => l.map (f x)) encIn (encList encB) := by
  induction l with
  | nil => exact const []
  | cons a l ih =>
    exact (cons encB).comp ((hf a (List.mem_cons_self ..)).prod
      (ih fun b hb => hf b (List.mem_cons_of_mem _ hb)))

private theorem foldl_append (l : List (List α)) (acc : List α) :
    l.foldl (· ++ ·) acc = acc ++ l.flatten := by
  simpa only [List.map_id_fun, id_eq] using
    (List.foldl_append_eq_append (l := l) (f := id) (l' := acc))

private theorem length_encList_flatten_le (enc : α ↪ List Bool) (l : List (List α)) :
    (encList enc l.flatten).length ≤ (encList (encList enc) l).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatten_cons, encList_append, List.length_append, encList_cons, length_frame]
    lia

/-- Concatenating a list of lists is polynomial-time. -/
@[fun_prop]
theorem flatten (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime List.flatten (encList (encList enc)) (encList enc) := by
  have h := foldl' (list := id) (step := fun acc a => acc ++ a) id' (const [])
    (ComputableTidilyInDegree.listAppend enc).computableTidilyInPolyTime
    (B := fun l => (encList (encList enc) l).length) .self (fun l i _ => by
      rw [foldl_append, List.nil_append]
      exact (length_encList_flatten_le enc (l.take i)).trans
        (length_encList_take_le (encList enc) l i))
  simpa only [foldl_append, List.nil_append, id_eq] using h

/-- Concatenate polynomial-time lists computed from each element and a fixed parameter. -/
theorem flatMapWith {f : π × α → List β} {par : γ → π} {list : γ → List α}
    (hf : ComputableTidilyInPolyTime f (encPair encP encA) (encList encB))
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA)) :
    ComputableTidilyInPolyTime (fun x => (list x).flatMap fun a => f (par x, a))
      encIn (encList encB) := by
  simpa only [Function.comp_def, List.flatten_eq_flatMap, List.flatMap_map, id_eq] using
    (flatten encB).comp (mapWith hf hpar hlist)

/-- Concatenate lists computed jointly from the original input and each list element.
Like `mapWithInput`, this is a composition rule for `fun_prop`. -/
@[fun_prop]
theorem flatMapWithInput {f : γ → α → List β} {list : γ → List α}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (hf : ComputableTidilyInPolyTime (fun p : γ × α => f p.1 p.2)
      (encPair encIn encA) (encList encB)) :
    ComputableTidilyInPolyTime (fun x => (list x).flatMap (f x)) encIn (encList encB) :=
  flatMapWith hf id' hlist

/-- Concatenate input-dependent lists indexed by a fixed list of parameters.
No encoding of the fixed parameters is required. -/
@[fun_prop]
theorem flatMapConst {ι : Type*} (l : List ι) {f : γ → ι → List β}
    (hf : ∀ i ∈ l, ComputableTidilyInPolyTime (fun x => f x i) encIn (encList encB)) :
    ComputableTidilyInPolyTime (fun x => l.flatMap (f x)) encIn (encList encB) := by
  simpa only [Function.comp_def, List.flatten_eq_flatMap, List.flatMap_map, id_eq] using
    (flatten encB).comp (mapConst l hf)

/-- The length of a list, in unary, including raw bit strings. -/
theorem length (enc : α ↪ List Bool) {encL : List α ↪ List Bool} [ListEncoding enc encL]
    [SizedListEncoding enc encL] :
    ComputableTidilyInPolyTime (fun l : List α => l.length) encL encUnary := by
  have h := foldl' (encA := enc) (encL := encL) (list := id)
    (step := fun n _ => n + 1) id' (const 0)
    (ComputableTidilyInDegree.unary_succ.computableTidilyInPolyTime.comp (fst encUnary enc))
    (B := fun l => (encL l).length) .self (fun l i _ => by
      simpa [List.foldl_const] using (Nat.min_le_right i l.length).trans
        (SizedListEncoding.length_le (encA := enc) (encL := encL) l))
  simpa [List.foldl_const] using h

/-- Length of a framed list; the element encoding is inferred from the list encoding. -/
@[fun_prop]
theorem length_list (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (fun l : List α => l.length) (encList enc) encUnary := length enc

/-- Length of a raw bit string. -/
@[fun_prop]
theorem length_bits :
    ComputableTidilyInPolyTime (fun l : List Bool => l.length) encBits encUnary := length encBool

/-- The encoded input length, computed in unary by reading the input word. -/
@[fun_prop]
theorem encoding_length (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (fun a => (enc a).length) enc encUnary :=
  length_bits.comp (of_eq (encMid := encBits) fun _ => rfl)

/-- Length of a computed raw bit string, fixing the intermediate encoding for proof search.
Registered after `encoding_length` so `fun_prop` first tries this rule on computed words. -/
@[fun_prop]
theorem length_bits_comp {input : α ↪ List Bool} {word : α → List Bool}
    (hword : ComputableTidilyInPolyTime word input encBits) :
    ComputableTidilyInPolyTime (fun a => (word a).length) input encUnary :=
  length_bits.comp hword

/-- Enumerate `0, …, n - 1`, with the bound and the elements in unary. -/
@[fun_prop]
theorem range : ComputableTidilyInPolyTime List.range encUnary (encList encUnary) := by
  have hrep (n : ℕ) :
      (List.replicate n true).foldl (fun l _ => l ++ [l.length]) [] = List.range n := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ', List.foldl_append, ih, List.range_succ]
  have hstep := (ComputableTidilyInDegree.snoc encUnary).computableTidilyInPolyTime.comp
    ((fst (encList encUnary) encBool).prod
      ((length encUnary).comp (fst (encList encUnary) encBool)))
  have h := foldl' (encA := encBool) (encL := encBits)
    (list := fun n => List.replicate n true) (step := fun l _ => l ++ [l.length])
    (of_eq (encIn := encUnary) (encMid := encBits) fun _ => rfl) (const []) hstep
    (B := fun n => (encUnary n).length * (2 * (encUnary n).length + 1))
    (PolyBounded.self.mul (((PolyBounded.const 2).mul .self).add (.const 1)))
    (fun n i _ => by
      rw [List.take_replicate, hrep]
      refine (length_encList_le encUnary _ (b := n) fun a ha => ?_).trans ?_
      · simpa only [encUnary_apply, List.length_replicate] using
          (Nat.le_of_lt (List.mem_range.mp ha)).trans (Nat.min_le_right i n)
      · simp only [List.length_range, encUnary_apply, List.length_replicate]
        exact Nat.mul_le_mul_right _ (Nat.min_le_right i n))
  simpa only [hrep] using h

/-- Test whether any element satisfies a polynomial-time predicate with a fixed parameter. -/
theorem anyWith {test : π × α → Bool} {par : γ → π} {list : γ → List α}
    (htest : ComputableTidilyInPolyTime test (encPair encP encA) encBool)
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA)) :
    ComputableTidilyInPolyTime (fun x => (list x).any fun a => test (par x, a)) encIn encBool := by
  have heq (p : π) (l : List α) (b : Bool) :
      l.foldl (fun b a => b || test (p, a)) b = (b || l.any fun a => test (p, a)) := by
    induction l generalizing b <;> simp [*, Bool.or_assoc]
  have hstep : ComputableTidilyInPolyTime
      (fun q : (π × Bool) × α => q.1.2 || test (q.1.1, q.2))
      (encPair (encPair encP encBool) encA) encBool := by fun_prop
  have h := foldlWith (encA := encA) (encB := encBool)
    (step := fun p b a => b || test (p, a))
    hpar hlist (const false) hstep (B := fun _ => 1) (.const 1)
    (fun _ _ _ => by simp)
  simpa only [heq, Bool.false_or] using h

/-- Test whether every element satisfies a polynomial-time predicate with a fixed parameter. -/
theorem allWith {test : π × α → Bool} {par : γ → π} {list : γ → List α}
    (htest : ComputableTidilyInPolyTime test (encPair encP encA) encBool)
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA)) :
    ComputableTidilyInPolyTime (fun x => (list x).all fun a => test (par x, a)) encIn encBool := by
  have h := bool_not.comp (anyWith (bool_not.comp htest) hpar hlist)
  simpa only [Function.comp_def, ← List.all_eq_not_any_not] using h

/-- Test whether any list element satisfies a predicate that captures the original input. -/
@[fun_prop]
theorem anyWithInput {test : γ → α → Bool} {list : γ → List α}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (htest : ComputableTidilyInPolyTime (fun p : γ × α => test p.1 p.2)
      (encPair encIn encA) encBool) :
    ComputableTidilyInPolyTime (fun x => (list x).any (test x)) encIn encBool :=
  anyWith htest id' hlist

/-- Test whether every list element satisfies a predicate that captures the original input. -/
@[fun_prop]
theorem allWithInput {test : γ → α → Bool} {list : γ → List α}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (htest : ComputableTidilyInPolyTime (fun p : γ × α => test p.1 p.2)
      (encPair encIn encA) encBool) :
    ComputableTidilyInPolyTime (fun x => (list x).all (test x)) encIn encBool :=
  allWith htest id' hlist

private def idxStep [DecidableEq α] (v : α) (s : Bool × ℕ) (a : α) : Bool × ℕ :=
  if s.1 || decide (a = v) then (true, s.2) else (false, s.2 + 1)

private theorem foldl_idxStep [DecidableEq α] (v : α) (l : List α) (s : Bool × ℕ) :
    (l.foldl (idxStep v) s).2 = s.2 + if s.1 then 0 else l.idxOf v := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    rcases s with ⟨b, n⟩
    cases b <;> by_cases ha : a = v <;>
      simp [idxStep, ha, Nat.add_comm, Nat.add_left_comm]

/-- The index of the first occurrence, or the list length if absent, computed in unary.
The element itself can use any encoding. -/
@[fun_prop]
theorem idxOf [DecidableEq α] (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (fun p : List α × α => p.1.idxOf p.2)
      (encPair (encList enc) enc) encUnary := by
  have hsucc : ComputableTidilyInPolyTime (· + 1) encUnary encUnary :=
    ComputableTidilyInDegree.unary_succ.computableTidilyInPolyTime
  have hstep : ComputableTidilyInPolyTime
      (fun q : (α × (Bool × ℕ)) × α => idxStep q.1.1 q.1.2 q.2)
      (encPair (encPair enc (encPair encBool encUnary)) enc) (encPair encBool encUnary) := by
    have hq := fst (encPair enc (encPair encBool encUnary)) enc
    have hn := hq.snd'.snd'
    have ha := snd (encPair enc (encPair encBool encUnary)) enc
    exact (bool_or.comp (hq.snd'.fst'.prod ((decide_eq enc).comp (ha.prod hq.fst')))).ite'
      ((const true).prod hn) ((const false).prod (hsucc.comp hn))
  have h := foldlWith (snd (encList enc) enc) (fst (encList enc) enc)
    (const (false, 0)) hstep
    (B := fun p => 3 + (encPair (encList enc) enc p).length)
    ((PolyBounded.const 3).add .self) (fun p i hi => by
      have hidx := List.idxOf_le_length (a := p.2) (l := p.1.take i)
      have hlen := length_le_length_encList enc p.1
      simp only [length_encPair, encBool_apply, List.length_singleton, encUnary_apply,
        List.length_replicate, foldl_idxStep, Bool.false_eq_true, ite_false, Nat.zero_add,
        List.length_take] at *
      lia)
  simpa only [Function.comp_def, foldl_idxStep, Bool.false_eq_true, ite_false, Nat.zero_add]
    using (snd encBool encUnary).comp h

/-- Find a computed value's first occurrence in a computed list. -/
@[fun_prop]
theorem idxOfWithInput [DecidableEq α] {list : γ → List α} {value : γ → α}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (hvalue : ComputableTidilyInPolyTime value encIn encA) :
    ComputableTidilyInPolyTime (fun x => (list x).idxOf (value x)) encIn encUnary :=
  (idxOf encA).comp (hlist.prod hvalue)

/-- Drop a unary number of elements from a sized list encoding, including raw bit strings. -/
theorem dropUnary {encL : List α ↪ List Bool} [ListEncoding encA encL]
    [SizedListEncoding encA encL] :
    ComputableTidilyInPolyTime (fun p : List α × ℕ => p.1.drop p.2)
      (encPair encL encUnary) encL := by
  have heq (l : List α) (n : ℕ) :
      (List.replicate n true).foldl (fun acc _ => acc.tail) l = l.drop n := by
    simp [List.foldl_const, List.tail_iterate]
  have h := foldl' (encA := encBool) (encL := encBits)
    (list := fun p : List α × ℕ => List.replicate p.2 true) (step := fun acc _ => acc.tail)
    ((of_eq (encIn := encUnary) (encMid := encBits) fun _ => rfl).comp (snd encL encUnary))
    (fst encL encUnary)
    ((of_linear (ListEncoding.tail (enc₁ := encA))).comp (fst encL encBool))
    (B := fun p => (encPair encL encUnary p).length) .self (fun p i _ => by
      rw [List.take_replicate, heq]
      have := SizedListEncoding.length_drop_le (encA := encA) (encL := encL) p.1 (min i p.2)
      simp only [length_encPair]
      lia)
  simpa only [heq] using h

/-- Drop a computed unary number of bits from a computed bit string. -/
@[fun_prop]
theorem bitsDropWithInput {list : γ → List Bool} {count : γ → ℕ}
    (hlist : ComputableTidilyInPolyTime list encIn encBits)
    (hcount : ComputableTidilyInPolyTime count encIn encUnary) :
    ComputableTidilyInPolyTime (fun x => (list x).drop (count x)) encIn encBits :=
  (dropUnary (encA := encBool)).comp (hlist.prod hcount)

/-- Take a unary number of bits. Reversing and dropping reuses the certified list operations. -/
@[fun_prop]
theorem bitsTake : ComputableTidilyInPolyTime
    (fun p : List Bool × ℕ => p.1.take p.2) (encPair encBits encUnary) encBits := by
  have h : ComputableTidilyInPolyTime
      (fun p : List Bool × ℕ => (p.1.reverse.drop (p.1.length - p.2)).reverse)
      (encPair encBits encUnary) encBits := by fun_prop
  simpa only [← List.reverse_take, List.reverse_reverse] using h

/-- Take a computed unary number of bits from a computed bit string. -/
@[fun_prop]
theorem bitsTakeWithInput {list : γ → List Bool} {count : γ → ℕ}
    (hlist : ComputableTidilyInPolyTime list encIn encBits)
    (hcount : ComputableTidilyInPolyTime count encIn encUnary) :
    ComputableTidilyInPolyTime (fun x => (list x).take (count x)) encIn encBits :=
  bitsTake.comp (hlist.prod hcount)

/-- List lookup with a fixed default and a unary index, including lookup in raw bit strings. -/
@[fun_prop]
theorem listGetD {encL : List α ↪ List Bool} [ListEncoding encA encL]
    [SizedListEncoding encA encL] (d : α) :
    ComputableTidilyInPolyTime (fun p : List α × ℕ => p.1.getD p.2 d)
      (encPair encL encUnary) encA := by
  simpa only [Function.comp_def, List.headD_eq_head?_getD, List.head?_drop,
    List.getD_eq_getElem?_getD] using
    (of_linear (ListEncoding.headD (enc₁ := encA) (enc := encL) d)).comp
      (dropUnary (encA := encA))

/-- Read a bit at a unary index with a fixed fallback. Fixing the raw encoding avoids
guessing a list-encoding instance during compositional proof search. -/
@[fun_prop]
theorem bitsGetD (fallback : Bool) :
    ComputableTidilyInPolyTime (fun p : List Bool × ℕ => p.1.getD p.2 fallback)
      (encPair encBits encUnary) encBool := listGetD (encA := encBool) fallback

/-- Read a computed bit string at a computed unary index. -/
@[fun_prop]
theorem bitsGetDWithInput {list : γ → List Bool} {index : γ → ℕ}
    (hlist : ComputableTidilyInPolyTime list encIn encBits)
    (hindex : ComputableTidilyInPolyTime index encIn encUnary) (fallback : Bool) :
    ComputableTidilyInPolyTime (fun x => (list x).getD (index x) fallback) encIn encBool :=
  (bitsGetD fallback).comp (hlist.prod hindex)

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
