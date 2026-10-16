/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists

/-!
# Polynomial-time list operations

List operations for the polynomial-time calculus, using Christian Reitwiessner's encodings,
degree-bounded operations and fold rules. Indices use `encUnary`: an index returned by `idxOf`
is at most the list length, irrespective of the encoding of its elements. In particular, looking
up a variable with a large binary label does not require a certificate as long as that label.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.cons`, `.listAppend`, `.map`, `.flatten`:
  constructing lists.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapWith`, `.flatMapWith`: constructing lists
  with a parameter; the input list may itself have polynomial encoded length.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.filterWith`: filtering a polynomial-time list
  with a parameterized test.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.length`, `.range`: unary lengths and ranges.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.anyWith`, `.allWith`: Boolean scans with a
  parameter, applied explicitly like the fold rules.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.idxOf`: the first occurrence of an element.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listGetD`: lookup by a unary index.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

variable {α β γ π : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {encIn : γ ↪ List Bool} {encP : π ↪ List Bool}

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

/-- A polynomial-time function can be mapped over a list in polynomial time. -/
@[fun_prop]
theorem map {f : α → β} (hf : ComputableTidilyInPolyTime f encA encB) :
    ComputableTidilyInPolyTime (List.map f) (encList encA) (encList encB) :=
  mapWith (hf.comp (snd encBool encA)) (const true) id'

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

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
