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
-- Its meaningful invariant is that one bit has been accumulated per consumed input bit.
example : (∃ c, ComputableTidilyInTimeAndSpace (fun l : List Bool =>
      l.foldl (fun acc b => acc ++ [b]) []) encBits encBits
      (fun l => c * (l.length + 1) ^ 2) (fun l => c * (l.length + 1))) ∧
      ∀ l : List Bool, (l.foldl (fun acc b => acc ++ [b]) []).length = l.length := by
  have hstep : ComputableTidilyInLinearTimeAndSpace
      (fun p : List Bool × Bool => p.1 ++ [p.2]) (encPair encBits encBool) encBits :=
    (PairEncoding.fst (enc₁ := encBits) encBool).append
      (PairEncoding.snd (enc₂ := encBool) encBits) (fun _ => rfl)
  obtain ⟨k, hk⟩ := hstep
  obtain ⟨⟨c, h⟩, hpost⟩ := hk.foldl_bits_stream_spec (step := fun acc b => acc ++ [b]) []
    (fun _ i state => state.length = i) (by simp)
    (by intro l i hi state hs; simpa using hs)
    (R := fun l => k * (2 * l.length + 3)) (Q := fun l => k * (2 * l.length + 3))
    (B := List.length)
    (by
      intro l i hi state hs
      constructor <;> apply Nat.mul_le_mul_left k <;> simp only [length_encPair,
        encBits_apply, encBool_apply, List.length_singleton] <;> lia)
    (by intro l i hi state hs; simpa [hs] using hi)
  refine ⟨⟨c * (3 * k + 3), h.mono (fun l => ?_) (fun l => ?_)⟩, hpost⟩
  · have hround : k * (2 * l.length + 3) + l.length + 1 ≤
        (3 * k + 3) * (l.length + 1) := by nlinarith
    have hmul := Nat.mul_le_mul_left l.length hround
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith

end ComplexityTests.Quantitative
