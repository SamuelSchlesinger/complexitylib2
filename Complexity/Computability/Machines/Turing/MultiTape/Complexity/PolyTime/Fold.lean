/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Polynomial-time folds

The polynomial-time counterparts of Christian Reitwiessner's degree-bounded fold rules. A
`SizedListEncoding` accounts for list lengths, elements and suffixes, leaving only a polynomial
bound on the intermediate accumulator. The step may carry a fixed parameter.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldl'`: a fold with bounded accumulators.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldlWith`: a fold with a fixed parameter.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldl_spec`: one prefix invariant proves
  both polynomial-time computation and the final postcondition.

The specification interface is adapted from `IsPolyTime.list_foldl_spec` in the cslib
`crypto` branch, using the tidy machine calculus for the underlying computation.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

variable {γ α β π : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}
  {encB : β ↪ List Bool} {encL : List α ↪ List Bool} {encP : π ↪ List Bool}
  [ListEncoding encA encL] [SizedListEncoding encA encL]

/-- A left fold is polynomial-time when its step is polynomial-time and its intermediate
accumulators have polynomially bounded encoded length. -/
theorem foldl' {list : γ → List α} {init : γ → β} {step : β → α → β}
    (hlist : ComputableTidilyInPolyTime list encIn encL)
    (hinit : ComputableTidilyInPolyTime init encIn encB)
    (hstep : ComputableTidilyInPolyTime (fun p : β × α => step p.1 p.2)
      (encPair encB encA) encB)
    {B : γ → ℕ} (hB : PolyBounded (fun x => (encIn x).length) B)
    (hstates : ∀ x, ∀ i ≤ (list x).length,
      (encB (((list x).take i).foldl step (init x))).length ≤ B x) :
    ComputableTidilyInPolyTime (fun x => (list x).foldl step (init x)) encIn encB := by
  obtain ⟨_, _, hlist⟩ := hlist.exists_degree
  obtain ⟨_, _, hinit⟩ := hinit.exists_degree
  obtain ⟨_, _, hstep⟩ := hstep.exists_degree
  obtain ⟨c, d, hB⟩ := hB
  exact (ComputableTidilyInDegree.foldl' hlist hinit hstep
    (show DegreeBounded (fun x => (encIn x).length) B d from ⟨c, hB⟩)
    hstates).computableTidilyInPolyTime

/-- A polynomial-time fold whose step also uses a fixed, polynomial-time computable parameter. -/
theorem foldlWith {par : γ → π} {list : γ → List α} {init : γ → β}
    {step : π → β → α → β}
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn encL)
    (hinit : ComputableTidilyInPolyTime init encIn encB)
    (hstep : ComputableTidilyInPolyTime (fun p : (π × β) × α => step p.1.1 p.1.2 p.2)
      (encPair (encPair encP encB) encA) encB)
    {B : γ → ℕ} (hB : PolyBounded (fun x => (encIn x).length) B)
    (hstates : ∀ x, ∀ i ≤ (list x).length,
      (encB (((list x).take i).foldl (step (par x)) (init x))).length ≤ B x) :
    ComputableTidilyInPolyTime (fun x => (list x).foldl (step (par x)) (init x)) encIn encB := by
  obtain ⟨_, _, hpar⟩ := hpar.exists_degree
  obtain ⟨_, _, hlist⟩ := hlist.exists_degree
  obtain ⟨_, _, hinit⟩ := hinit.exists_degree
  obtain ⟨_, _, hstep⟩ := hstep.exists_degree
  obtain ⟨c, d, hB⟩ := hB
  exact (ComputableTidilyInDegree.foldlWith hpar hlist hinit hstep
    (show DegreeBounded (fun x => (encIn x).length) B d from ⟨c, hB⟩)
    hstates).computableTidilyInPolyTime

/-- A prefix invariant supplies both the accumulator bound and the final postcondition.
The list and step must have uniform polynomial-time certificates. -/
theorem foldl_spec {list : γ → List α} {init : γ → β} {step : β → α → β}
    (hlist : ComputableTidilyInPolyTime list encIn encL)
    (hinit : ComputableTidilyInPolyTime init encIn encB)
    (hstep : ComputableTidilyInPolyTime (fun p : β × α => step p.1 p.2)
      (encPair encB encA) encB)
    (invariant : γ → List α → β → Prop)
    (hbase : ∀ x, invariant x [] (init x))
    (hpreserve : ∀ x consumed state value, consumed ++ [value] <+: list x →
      invariant x consumed state → invariant x (consumed ++ [value]) (step state value))
    {size : ℕ → ℕ} (hsize : Cslib.PolynomiallyBounded size)
    (hbound : ∀ x consumed state, consumed <+: list x → invariant x consumed state →
      (encB state).length ≤ size (encIn x).length) :
    ComputableTidilyInPolyTime (fun x => (list x).foldl step (init x)) encIn encB ∧
      ∀ x, invariant x (list x) ((list x).foldl step (init x)) := by
  have htrace (x : γ) (i : ℕ) (hi : i ≤ (list x).length) :
      invariant x ((list x).take i) (((list x).take i).foldl step (init x)) := by
    induction i with
    | zero => simpa using hbase x
    | succ i ih =>
      have hlt : i < (list x).length := by lia
      simpa only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
        List.foldl_append, List.foldl_cons, List.foldl_nil] using
        hpreserve x ((list x).take i) _ (list x)[i]
          (by simpa only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some]
            using List.take_prefix (i + 1) (list x)) (ih (by lia))
  exact ⟨foldl' hlist hinit hstep (.of_polynomiallyBounded _ hsize)
    (fun x i hi => hbound x ((list x).take i) _ (List.take_prefix ..) (htrace x i hi)),
    fun x => by simpa using htrace x (list x).length le_rfl⟩

/-- Constant additive growth discharges the fold's intermediate-size obligation. -/
theorem foldl_of_bounded_growth {list : γ → List α} {init : γ → β} {step : β → α → β}
    (hlist : ComputableTidilyInPolyTime list encIn encL)
    (hinit : ComputableTidilyInPolyTime init encIn encB)
    (hstep : ComputableTidilyInPolyTime (fun p : β × α => step p.1 p.2)
      (encPair encB encA) encB)
    {growth : ℕ}
    (hgrowth : ∀ state value, (encB (step state value)).length ≤
      (encB state).length + growth) :
    ComputableTidilyInPolyTime (fun x => (list x).foldl step (init x)) encIn encB := by
  obtain ⟨ci, di, hi⟩ := hinit.polyBounded_length
  obtain ⟨cl, dl, hl⟩ := hlist.polyBounded_length
  refine (foldl_spec hlist hinit hstep
    (fun x consumed state => (encB state).length ≤
      (encB (init x)).length + consumed.length * growth)
    (by simp) ?_ (size := fun n => ci * (n + 1) ^ di + cl * (n + 1) ^ dl * growth)
    (by fun_prop) ?_).1
  · intro x consumed state value _ hs
    have := hgrowth state value
    simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
    lia
  · intro x consumed state hprefix hs
    have hlen := hprefix.length_le.trans
      (SizedListEncoding.length_le (encA := encA) (encL := encL) (list x))
    have hcount := Nat.mul_le_mul_right growth (hlen.trans (hl x))
    exact hs.trans (Nat.add_le_add (hi x) hcount)

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
