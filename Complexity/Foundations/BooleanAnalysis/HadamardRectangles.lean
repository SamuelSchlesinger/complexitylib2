/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Basic
public import Complexity.Foundations.Data.BitString.Sign
public import Mathlib.Data.Matrix.Mul
import Complexity.Foundations.LinearAlgebra.Matrix.Lindsey
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Monochromatic rectangles for the inner product

Lindsey's lemma bounds the signed sum of the inner product modulo two `x ⬝ᵥ y` over a rectangle
`A × B` of bit strings indexed by `ι` by `√(|A| |B| 2 ^ |ι|)` in absolute value
(`BitString.sq_sum_signVal_dotProduct_le`). So if `x ⬝ᵥ y` is constant on `A × B`, the
rectangle has at most `2 ^ Fintype.card ι` entries. Empty sides, zero coordinates, and both
constant values are included.

The proof specializes Lindsey's bilinear bound to the identity matrix after the standard ring
equivalence between Boolean values and `ZMod 2`; it introduces no alternative inner product.

## Main results

* `Cslib.BitString.sq_sum_signVal_dotProduct_le`: Lindsey's lemma for signed sums of the inner
  product over rectangles.
* `Cslib.BitString.card_mul_le_two_pow_of_dotProduct_eq`: the monochromatic inner-product rectangle
  bound.

## References

* [S. Jukna, *Extremal Combinatorics*, Ch. 14][Jukna2011]
* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Lemma 2.4]
  [ThresholdCircuitRepresentations2026]
-/

@[expose] public section

open Matrix Finset

namespace Cslib.BitString

variable {ι : Type*} [Fintype ι]

/-- **Lindsey's lemma for the inner product**: the signed sum of the inner product modulo two over
a rectangle `A × B` of bit strings indexed by `ι` is at most `√(|A| |B| 2 ^ |ι|)` in absolute
value. -/
theorem sq_sum_signVal_dotProduct_le (A B : Finset (ι → Bool)) :
    (∑ x ∈ A, ∑ y ∈ B, signVal (x ⬝ᵥ y)) ^ 2 ≤ #A * #B * 2 ^ Fintype.card ι := by
  classical
  let e : Bool ≃+* ZMod 2 := (ZMod.ringEquivOfPrime Bool Nat.prime_two (by decide)).symm
  let g : (ι → Bool) ↪ (ι → ZMod 2) :=
    ⟨fun x i => e (x i), fun _ _ h => funext fun i => e.injective (congrFun h i)⟩
  have hdot (x y : ι → Bool) : g x ⬝ᵥ g y = e (x ⬝ᵥ y) :=
    (e.toRingHom.map_dotProduct x y).symm
  have hsign (b : Bool) : (-1 : ℝ) ^ (e b).val = signVal b := by
    cases b <;> norm_num [show false = (0 : Bool) from rfl,
      show true = (1 : Bool) from rfl, show (1 : ZMod 2).val = 1 from rfl, signVal]
  have hL := Matrix.sq_sum_bilinear_mul_two_pow_rank_le
    (1 : Matrix ι ι (ZMod 2)) (A.map g) (B.map g) (fun _ => 1) (fun _ => 1)
    (fun _ => by norm_num) (fun _ => by norm_num)
  simp only [sum_map, Matrix.one_mulVec, Matrix.rank_one, card_map, one_mul, hdot,
    hsign] at hL
  have hp : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  refine (mul_le_mul_iff_left₀ hp).mp ?_
  linarith

/-- A rectangle on which the inner product modulo two is constant has at most
`2 ^ Fintype.card ι` entries. Neither side is required to be nonempty. -/
theorem card_mul_le_two_pow_of_dotProduct_eq (A B : Finset (ι → Bool)) (b : Bool)
    (h : ∀ x ∈ A, ∀ y ∈ B, x ⬝ᵥ y = b) :
    A.card * B.card ≤ 2 ^ Fintype.card ι := by
  have hs : ∑ x ∈ A, ∑ y ∈ B, signVal (x ⬝ᵥ y) = #A * #B * signVal b := by
    calc
      _ = ∑ x ∈ A, ∑ y ∈ B, signVal b := sum_congr rfl fun x hx => sum_congr rfl fun y hy => by
        rw [h x hx y hy]
      _ = _ := by simp [mul_assoc]
  have hL := sq_sum_signVal_dotProduct_le A B
  rw [hs, mul_pow, show signVal b ^ 2 = 1 by cases b <;> norm_num, mul_one, sq] at hL
  have : (#A : ℝ) * #B ≤ 2 ^ Fintype.card ι := by
    rcases (Nat.cast_nonneg (α := ℝ) (#A * #B)).eq_or_lt with h0 | h0
    · rw [Nat.cast_mul] at h0
      rw [← h0]
      positivity
    · rw [Nat.cast_mul] at h0
      exact le_of_mul_le_mul_left hL h0
  exact_mod_cast this

end Cslib.BitString
