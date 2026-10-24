/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (spike for #739, not for merge)

public import Complexity.Computability.WordRAM.Turing
public import Complexity.Computability.Complexity.Classes.P
import Complexity.Tactic.PolyTime.Init

/-!
# Word-RAM deciders give membership in `P` (spike, #739)

A fixed word-RAM program that decides `A` in polynomially many instructions, on a word encoding
computable in polynomial time from the bit-string encoding, places `A` in `P`.

## Main results

* `Cslib.WordRAM.Program.DecidesInTime.mem_P`: a fixed polynomial-time word-RAM decider.
* `Cslib.WordRAM.UniformDecidableInPolyTime.mem_P`: the same for the uniform predicate.

## References

* [S. A. Cook and R. A. Reckhow, *Time bounded random access machines*][CookReckhow1973]
-/

@[expose] public section

namespace Cslib.WordRAM

open Turing.MultiTapeTM

variable {B : Basis} {r : ℕ} {α : Type} {encIn : α ↪ List Bool}

/-- **A polynomial-time word-RAM decider places its problem in `P`.** -/
theorem Program.DecidesInTime.mem_P (hB : B.PolyTimeOps) {p : Program B r}
    {encode : α → List ℕ} {A : Set α} {size : α → ℕ} {T : ℕ → ℕ} {k : ℕ}
    (hT : PolynomiallyBounded T)
    (hsize : PolyBounded (fun a => (encIn a).length) size)
    (hencode : Turing.MultiTapeTM.ComputableInPolyTime encode encIn (encList encNat))
    (h : p.DecidesInTime (fun _ => encode) A (fun a _ => T (size a))
      (fun a w => logWidth k (size a) ≤ w)) :
    A ∈ Cslib.Complexity.P encIn := by
  classical
  let f : α → ℕ := fun a => if a ∈ A then 1 else 0
  have hf : p.ComputesInTime (fun _ => encode) (fun a _ => T (size a))
      (fun a w => logWidth k (size a) ≤ w) f := by
    intro a w hw hi
    obtain ⟨v, n, hv, hn, hle, hiff⟩ := h a w hw hi
    have hfv : f a = v := by
      by_cases ha : a ∈ A
      · simp only [f, ha, ite_true]
        exact (hiff.mpr ha).symm
      · have : v ≠ 1 := fun h1 => ha (hiff.mp h1)
        simp only [f, ha, ite_false]
        omega
    exact ⟨n, hfv ▸ hv, hn⟩
  have hpoly := hf.computableInPolyTime hB hT hsize hencode
  refine ⟨fun a => decide (f a = 1), .of_tidy ((ComputableTidilyInPolyTime.decide_eq encNat).comp
    (hpoly.tidy.prod (ComputableTidilyInPolyTime.const 1))), fun a => ?_⟩
  by_cases ha : a ∈ A <;> simp [f, ha]

/-- **Uniform polynomial-time word-RAM decidability places a problem in `P`.** The word-RAM
predicate `UniformDecidableInTime` with a polynomial bound in `size`, at every width above a
logarithmic threshold. -/
theorem UniformDecidableInTime.mem_P (hB : B.PolyTimeOps) {encode : α → List ℕ} {A : Set α}
    {size : α → ℕ} {T : ℕ → ℕ} {k : ℕ} (hT : PolynomiallyBounded T)
    (h : UniformDecidableInTime B A (fun _ => encode) (fun a _ => T (size a))
      (fun a w => logWidth k (size a) ≤ w))
    (hsize : PolyBounded (fun a => (encIn a).length) size)
    (hencode : Turing.MultiTapeTM.ComputableInPolyTime encode encIn (encList encNat)) :
    A ∈ Cslib.Complexity.P encIn := by
  obtain ⟨r, p, hp⟩ := h
  exact Program.DecidesInTime.mem_P hB hT hsize hencode hp

end Cslib.WordRAM
