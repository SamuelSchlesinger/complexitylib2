/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Hadamard
import Complexity.Foundations.LinearAlgebra.Matrix.Lindsey
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Monochromatic rectangles for the Hadamard code

The existing `BitString.hadamardCode x y` is the inner product modulo two. If it is constant on
`A × B`, the rectangle has at most `2 ^ Fintype.card ι` entries. Empty sides, zero coordinates,
and both constant values are included.

The proof specializes Lindsey's bilinear bound to the identity matrix after the standard ring
equivalence between Boolean values and `ZMod 2`; it introduces no alternative inner product.

## Main results

* `Cslib.BitString.card_mul_le_two_pow_of_hadamardCode_eq`: the Hadamard rectangle bound.

## References

* [S. Jukna, *Extremal Combinatorics*, Ch. 14][Jukna2011]
* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Lemma 2.4]
  [ThresholdCircuitRepresentations2026]
-/

@[expose] public section

open Matrix Finset

namespace Cslib.BitString

/-- A rectangle on which the inner product modulo two is constant has at most
`2 ^ Fintype.card ι` entries. Neither side is required to be nonempty. -/
theorem card_mul_le_two_pow_of_hadamardCode_eq {ι : Type*} [Fintype ι]
    (A B : Finset (ι → Bool)) (b : Bool)
    (h : ∀ x ∈ A, ∀ y ∈ B, hadamardCode x y = b) :
    A.card * B.card ≤ 2 ^ Fintype.card ι := by
  classical
  let e : Bool ≃+* ZMod 2 := (ZMod.ringEquivOfPrime Bool Nat.prime_two (by decide)).symm
  let f : (ι → Bool) ↪ (ι → ZMod 2) :=
    ⟨fun x i => e (x i), fun _ _ h => funext fun i => e.injective (congrFun h i)⟩
  have hdot (x y : ι → Bool) : f x ⬝ᵥ f y = e (hadamardCode x y) :=
    (e.toRingHom.map_dotProduct x y).symm
  have hsign (b : Bool) : (-1 : ℝ) ^ (e b).val = signVal b := by
    cases b <;> norm_num [show false = (0 : Bool) from rfl,
      show true = (1 : Bool) from rfl, show (1 : ZMod 2).val = 1 from rfl, signVal]
  have hs : (∑ x ∈ A, ∑ y ∈ B, (-1 : ℝ) ^ (f x ⬝ᵥ f y).val) =
      A.card * B.card * signVal b := by
    calc
      _ = ∑ x ∈ A, ∑ y ∈ B, signVal b := by
        refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
        rw [hdot, h x hx y hy, hsign]
      _ = _ := by simp [mul_assoc]
  have hL := Matrix.sq_sum_bilinear_mul_two_pow_rank_le
    (1 : Matrix ι ι (ZMod 2)) (A.map f) (B.map f) (fun _ => 1) (fun _ => 1)
    (fun _ => by norm_num) (fun _ => by norm_num)
  simp only [Finset.sum_map, Matrix.one_mulVec, Matrix.rank_one, Finset.card_map,
    one_mul] at hL
  rw [hs] at hL
  have hp : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hL' : ((A.card : ℝ) * B.card) ^ 2 ≤ A.card * B.card * 2 ^ Fintype.card ι := by
    apply (mul_le_mul_iff_left₀ hp).mp
    calc
      _ = ((A.card : ℝ) * B.card * signVal b) ^ 2 * 2 ^ Fintype.card ι := by
        cases b <;> simp [signVal]
      _ ≤ _ := hL
      _ = _ := by ring
  have : (A.card : ℝ) * B.card ≤ 2 ^ Fintype.card ι := by
    nlinarith [sq_nonneg ((A.card : ℝ) * B.card - 2 ^ Fintype.card ι)]
  exact_mod_cast this

end Cslib.BitString
