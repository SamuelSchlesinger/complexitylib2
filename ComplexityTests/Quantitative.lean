/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Mathlib.Tactic.Linarith

/-!
# Quantitative certificate clients

Resource bounds survive composition, ordinary functional spellings and streaming folds.
-/

open Turing.MultiTapeTM

namespace ComplexityTests.Quantitative

-- Quadratic computation with linear output feeds a cubic consumer without a degree-six bound.
example (f g : List Bool → List Bool)
    (hg : ComputableTidilyInDegree g encBits encBits 2 1)
    (hf : ComputableTidilyInDegree f encBits encBits 3 1) :
    ComputableTidilyInDegree (fun x => f (g x)) encBits encBits 3 1 := by
  fail_if_success (clear hg; fun_prop (disch := lia))
  fail_if_success (clear hf; fun_prop (disch := lia))
  fail_if_success
    have : ComputableTidilyInDegree (fun x => f (g x)) encBits encBits 3 0 := by
      fun_prop (disch := lia)
  fun_prop (disch := lia)

example (f g : List Bool → List Bool)
    (hg : ComputableTidilyInDegree g encBits encBits 2 1)
    (hf : ComputableTidilyInDegree f encBits encBits 3 1) :
    ComputableTidilyInDegree (f ∘ g) encBits encBits 3 1 := by
  fun_prop (disch := lia)

-- An alternative intermediate encoding and let spelling retain the same degrees.
example (f g : List Bool → List Bool)
    (hg : ComputableTidilyInDegree g encBits (encFramed encBits) 2 1)
    (hf : ComputableTidilyInDegree f (encFramed encBits) encBits 3 1) :
    ComputableTidilyInDegree (fun x => let y := g x; f y) encBits encBits 3 1 := by
  fun_prop (disch := lia)

-- Pairing preserves linear output even when the components take longer to compute.
example (f g : List Bool → List Bool)
    (hf : ComputableTidilyInDegree f encBits encBits 2 1)
    (hg : ComputableTidilyInDegree g encBits encBits 3 1) :
    ComputableTidilyInDegree (fun x => (f x, g x)) encBits (encPair encBits encBits) 3 1 := by
  fun_prop (disch := lia)

example (f g : List Bool → List Bool) (h : List Bool × List Bool → List Bool)
    (hf : ComputableTidilyInDegree f encBits encBits 2 1)
    (hg : ComputableTidilyInDegree g encBits encBits 2 1)
    (hh : ComputableTidilyInDegree h (encPair encBits encBits) encBits 3 1) :
    ComputableTidilyInDegree (fun x => h (f x, g x)) encBits encBits 3 1 := by
  fun_prop (disch := lia)

-- Reusing a let-bound value and expanding the binding must give the same resource bound.
example (f g : List Bool → List Bool)
    (hg : ComputableTidilyInDegree g encBits encBits 2 1)
    (hf : ComputableTidilyInDegree f encBits encBits 3 1) :
    ComputableTidilyInDegree (fun x => let y := g x; (f y, y)) encBits
      (encPair encBits encBits) 3 1 := by
  fun_prop (disch := lia)

example (f g : List Bool → List Bool)
    (hg : ComputableTidilyInDegree g encBits encBits 2 1)
    (hf : ComputableTidilyInDegree f encBits encBits 3 1) :
    ComputableTidilyInDegree (fun x => (f (g x), g x)) encBits
      (encPair encBits encBits) 3 1 := by
  fun_prop (disch := lia)

-- Sharing also works when the intermediate encoding differs from the input encoding.
example (f g : List Bool → List Bool)
    (hg : ComputableTidilyInDegree g encBits (encFramed encBits) 2 1)
    (hf : ComputableTidilyInDegree f (encFramed encBits) encBits 3 1) :
    ComputableTidilyInDegree (fun x => let y := g x; (f y, y)) encBits
      (encPair encBits (encFramed encBits)) 3 1 := by
  fun_prop (disch := lia)

-- The same certificates still imply ordinary polynomial time when requested.
example (f g : List Bool → List Bool)
    (hg : ComputableTidilyInDegree g encBits encBits 2 1)
    (hf : ComputableTidilyInDegree f encBits encBits 3 1) :
    ComputableTidilyInPolyTime (fun x => f (g x)) encBits encBits :=
  (show ComputableTidilyInDegree (fun x => f (g x)) encBits encBits 3 1 by
    fun_prop (disch := lia)).computableTidilyInPolyTime

-- A recognizably functional scan gets linear time and constant workspace.
example : ComputableTidilyInO (fun l : List Bool => l.foldl (· ^^ ·) false)
    encBits encBool List.length (fun _ => 0) := by
  fun_prop

example : ComputableTidilyInO (List.foldl (fun state bit => state ^^ bit) false)
    encBits (encFramed encBool) (fun l => l.length) (fun _ => 0) := by
  fun_prop

-- The finite-state rule works for arbitrary fixed transition tables and encodings.
example {σ : Type} [Finite σ] (enc : σ ↪ List Bool) (step : σ → Bool → σ) (init : σ) :
    ComputableTidilyInO (fun l => l.foldl step init) encBits enc List.length (fun _ => 0) := by
  fun_prop

-- Emitting each mapped bit uses no work-tape cells, even though the output grows.
example (f : Bool → Bool) :
    ComputableTidilyInTimeAndSpace (fun l : List Bool => l.map f) encBits encBits
      (fun l => 4 * l.length + 8) (fun _ => 0) := by
  fun_prop

-- The same growing-list expression has a streaming implementation after a functional rewrite.
example (f : Bool → Bool) :
    ComputableTidilyInTimeAndSpace (fun l : List Bool =>
      l.foldl (fun acc b => acc ++ [f b]) []) encBits encBits
      (fun l => 4 * l.length + 8) (fun _ => 0) := by
  simpa only [List.foldl_append_eq_append, List.nil_append, ← List.flatMap_def,
    ← List.map_eq_flatMap] using ComputableTidilyInTimeAndSpace.map_bits f

-- The numerical loop contract also handles a genuinely growing stored accumulator.
-- Its invariant is one stored bit per consumed input bit. The cost at index i uses i, not the
-- final input length; summing it accounts for the cumulative copying of growing prefixes.
example : (∃ c, ComputableTidilyInTimeAndSpace (fun l : List Bool =>
      l.foldl (fun acc b => acc ++ [b]) []) encBits encBits
      (fun l => c * (l.length + 1) ^ 2) (fun l => c * (l.length + 1))) ∧
      ∀ l : List Bool, (l.foldl (fun acc b => acc ++ [b]) []).length = l.length := by
  have hstep : ComputableTidilyInLinearTimeAndSpace
      (fun p : List Bool × Bool => p.1 ++ [p.2]) (encPair encBits encBool) encBits :=
    (PairEncoding.fst (enc₁ := encBits) encBool).append
      (PairEncoding.snd (enc₂ := encBool) encBits) (fun _ => rfl)
  obtain ⟨k, hk⟩ := hstep
  obtain ⟨⟨c, h⟩, hpost⟩ := hk.foldl_bits_stream_sum_spec (step := fun acc b => acc ++ [b]) []
    (fun _ i state => state.length = i) (by simp)
    (by intro l i hi state hs; simpa using hs)
    (R := fun _ i => k * (2 * i + 3) + 2 * i + 2)
    (Q := fun l => k * (2 * l.length + 3))
    (B := List.length)
    (by
      intro l i hi state hs
      simp only [length_encPair, encBits_apply, encBool_apply, List.length_singleton,
        List.length_append, hs]
      exact ⟨by lia, Nat.mul_le_mul_left k (by lia)⟩)
    (by intro l i hi state hs; simpa [hs] using hi)
  refine ⟨⟨c * (3 * k + 3), h.mono (fun l => ?_) (fun l => ?_)⟩, hpost⟩
  · have hsum (n : ℕ) : (∑ i ∈ Finset.range n, (k * (2 * i + 3) + 2 * i + 2)) =
        (k + 1) * n ^ 2 + (2 * k + 1) * n := by
      induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ]; nlinarith
    rw [hsum, Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith


-- Resetting an accumulator charges only the prefixes actually retained between resets.
-- Long runs cost more; short runs need not pay the largest state's cost on every round.
private def resetStep (state : List Bool) (bit : Bool) : List Bool :=
  if bit then [] else state ++ [false]

example : ∃ c, ComputableTidilyInTimeAndSpace (fun l => l.foldl resetStep []) encBits encBits
    (fun l => c * ((∑ i ∈ Finset.range l.length,
      (((l.take i).foldl resetStep []).length + 1)) + 1))
    (fun l => c * (l.length + 1)) := by
  have hgrowth (state : List Bool) (bit : Bool) :
      (resetStep state bit).length ≤ state.length + 1 := by cases bit <;> simp [resetStep]
  have hlength (l state : List Bool) :
      (l.foldl resetStep state).length ≤ state.length + l.length := by
    induction l generalizing state with
    | nil => simp
    | cons b l ih =>
      have h := ih (resetStep state b)
      have hg := hgrowth state b
      simpa only [List.foldl_cons, List.length_cons] using (show
        (l.foldl resetStep (resetStep state b)).length ≤ state.length + (l.length + 1) by lia)
  have happend : ComputableTidilyInLinearTimeAndSpace
      (fun p : List Bool × Bool => p.1 ++ [false]) (encPair encBits encBool) encBits :=
    (PairEncoding.fst (enc₁ := encBits) encBool).append
      (ComputableTidilyInLinearTimeAndSpace.const (encMid := encBool) false) (fun _ => rfl)
  have hstep : ComputableTidilyInLinearTimeAndSpace
      (fun p : List Bool × Bool => resetStep p.1 p.2) (encPair encBits encBool) encBits :=
    (PairEncoding.snd (enc₂ := encBool) encBits).ite
      (ComputableTidilyInLinearTimeAndSpace.const []) (happend.restrict _)
  obtain ⟨k, hk⟩ := hstep
  obtain ⟨c, h⟩ := hk.foldl_bits_stream_sum (step := resetStep) []
    (R := fun l i => (3 * k + 2) * (((l.take i).foldl resetStep []).length + 1))
    (Q := fun l => k * (2 * l.length + 3)) (B := List.length)
    (fun l i hi => by
      have hg := hgrowth ((l.take i).foldl resetStep []) l[i]
      simp only [length_encPair, encBits_apply, encBool_apply, List.length_singleton,
        List.take_succ_eq_append_getElem hi, List.foldl_append, List.foldl_cons, List.foldl_nil]
      nlinarith)
    (fun l i hi => by
      have hl := hlength (l.take i) []
      simp only [List.length_nil, Nat.zero_add, List.length_take] at hl
      apply Nat.mul_le_mul_left k
      simp only [length_encPair, encBits_apply, encBool_apply, List.length_singleton]
      lia)
    (fun l i hi => by
      have hl := hlength (l.take i) []
      simpa only [encBits_apply, List.length_nil, Nat.zero_add, List.length_take] using
        hl.trans (by simp))
  have hn (l : List Bool) : l.length ≤ ∑ i ∈ Finset.range l.length,
      (((l.take i).foldl resetStep []).length + 1) := by
    simpa using (Finset.sum_le_sum (s := Finset.range l.length)
      (f := fun _ => 1) (g := fun i => ((l.take i).foldl resetStep []).length + 1)
      (fun _ _ => Nat.le_add_left 1 _))
  refine ⟨c * (3 * k + 3), h.mono (fun l => ?_) (fun l => ?_)⟩
  · rw [← Finset.mul_sum, Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    have hl := hn l
    nlinarith
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith

-- An empty input still retains and emits the nonempty initial state.
example : ¬ (∀ l : List Bool, ∀ i ≤ l.length,
    (encBits ((l.take i).foldl (fun state _ => state) [true])).length ≤ 0) := by
  intro h
  have := h [] 0 (by simp)
  simp at this

-- A one-bit input charges the successor state even when the initial state is empty.
example : ¬ (∀ l : List Bool, ∀ i ≤ l.length,
    (encBits ((l.take i).foldl (fun state bit => state ++ [bit]) [])).length ≤ 0) := by
  intro h
  have := h [true] 1 (by simp)
  simp at this

end ComplexityTests.Quantitative
