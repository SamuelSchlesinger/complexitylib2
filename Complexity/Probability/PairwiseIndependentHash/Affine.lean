/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.PairwiseIndependentHash
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
# The affine hash family

For a finite field `F` and finite types `m` and `n`, the affine maps `x ↦ A x + b` from `n → F`
to `m → F`, with seed a matrix `A` and a vector `b` (`Cslib.Probability.affineHash`), form a
pairwise independent hash family (`Cslib.Probability.isPairwiseIndependentHash_affineHash`):
for `x₁ ≠ x₂` the map `(A, b) ↦ (A x₁ + b, A x₂ + b)` is additive and onto, so all its fibers
have the same size. Over `F = ZMod 2` these are the affine maps of bit vectors used for the set
lower bound protocol and in the lemma of Valiant and Vazirani; the linear maps `x ↦ A x` over
`ZMod 2` form one of the universal classes of Carter and Wegman [CarterWegman1979].

## Main definitions

* `Cslib.Probability.affineHash`: the affine map `x ↦ A x + b` with seed `(A, b)`.

## Main results

* `Cslib.Probability.isPairwiseIndependentHash_affineHash`: the affine maps over a finite field
  form a pairwise independent hash family.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 8.2][AroraBarak09]
* [J. L. Carter, M. N. Wegman, *Universal classes of hash functions*][CarterWegman1979]
-/

@[expose] public section

namespace Cslib.Probability

open Finset
open scoped Matrix

section Def

variable {F m n : Type*} [NonUnitalNonAssocSemiring F] [Fintype n]

/-- The affine map `x ↦ A x + b` from `n → F` to `m → F`, with seed `(A, b)`. -/
def affineHash (p : Matrix m n F × (m → F)) (x : n → F) : m → F :=
  p.1 *ᵥ x + p.2

/-- The affine map with seed `(A, b)` sends `x` to `A x + b`. -/
@[simp]
theorem affineHash_apply (A : Matrix m n F) (b : m → F) (x : n → F) :
    affineHash (A, b) x = A *ᵥ x + b :=
  rfl

end Def

/-- The fibers of a surjective additive homomorphism of finite groups `G → H` all have density
`1 / #H`. -/
private theorem dens_filter_eq_of_surjective {G H : Type*} [AddGroup G] [Fintype G] [AddGroup H]
    [Fintype H] [DecidableEq H] (φ : G →+ H) (hφ : Function.Surjective φ) (a : H) :
    dens {g | φ g = a} = (Fintype.card H : ℚ≥0)⁻¹ := by
  have hfib : ∀ b, #{g | φ g = b} = #{g | φ g = a} := fun b =>
    AddMonoidHom.card_fiber_eq_of_mem_range φ (hφ b) (hφ a)
  have hcard : Fintype.card G = Fintype.card H * #{g | φ g = a} := by
    rw [← card_univ, card_eq_sum_card_fiberwise (f := φ) (t := univ) fun _ _ => mem_univ _]
    simp only [hfib, sum_const, card_univ, smul_eq_mul]
  obtain ⟨g, hg⟩ := hφ a
  have hpos : #{g | φ g = a} ≠ 0 := (card_pos.2 ⟨g, mem_filter.2 ⟨mem_univ _, hg⟩⟩).ne'
  rw [dens_eq_card_div_card, hcard, Nat.cast_mul, div_mul_cancel_right₀ (Nat.cast_ne_zero.2 hpos)]

variable {F m n : Type*} [Field F] [Fintype n]

/-- Evaluation of the affine maps at `x`, as an additive homomorphism of the seed. -/
private def affineHashAt (x : n → F) : Matrix m n F × (m → F) →+ m → F :=
  (Matrix.mulVec.addMonoidHomLeft x).comp (AddMonoidHom.fst _ _) + AddMonoidHom.snd _ _

private theorem affineHashAt_apply (x : n → F) (p : Matrix m n F × (m → F)) :
    affineHashAt x p = affineHash p x :=
  rfl

variable [Fintype F] [DecidableEq F] [Fintype m] [DecidableEq m] [DecidableEq n]

/-- **The affine hash family is pairwise independent**: over a finite field `F`, the affine maps
`x ↦ A x + b` from `n → F` to `m → F`, for a uniformly random matrix `A` and vector `b`, form a
pairwise independent hash family. -/
theorem isPairwiseIndependentHash_affineHash :
    IsPairwiseIndependentHash (affineHash : Matrix m n F × (m → F) → (n → F) → m → F) where
  dens_filter_apply_eq x y := by
    simp only [← affineHashAt_apply]
    refine dens_filter_eq_of_surjective _ (fun y => ⟨(0, y), ?_⟩) y
    rw [affineHashAt_apply, affineHash_apply, Matrix.zero_mulVec, zero_add]
  dens_filter_apply_eq_and_apply_eq {x₁ x₂} hx y₁ y₂ := by
    have hφ : Function.Surjective ((affineHashAt (m := m) x₁).prod (affineHashAt x₂)) := by
      rintro ⟨z₁, z₂⟩
      obtain ⟨k, hk⟩ := Function.ne_iff.1 hx
      have hd : x₁ k - x₂ k ≠ 0 := sub_ne_zero.2 hk
      let A : Matrix m n F :=
        Matrix.of fun r c => if c = k then (z₁ r - z₂ r) / (x₁ k - x₂ k) else 0
      have hA : A *ᵥ (x₁ - x₂) = z₁ - z₂ := by
        ext r
        simp only [A, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.sub_apply, ite_mul, zero_mul,
          sum_ite_eq', mem_univ, ite_true]
        exact div_mul_cancel₀ _ hd
      refine ⟨(A, z₁ - A *ᵥ x₁), Prod.ext ?_ ?_⟩
      · simp only [AddMonoidHom.prod_apply, affineHashAt_apply, affineHash_apply]
        abel
      · simp only [AddMonoidHom.prod_apply, affineHashAt_apply, affineHash_apply]
        rw [Matrix.mulVec_sub] at hA
        linear_combination -hA
    have := dens_filter_eq_of_surjective _ hφ (y₁, y₂)
    simp only [AddMonoidHom.prod_apply, affineHashAt_apply, Prod.mk.injEq, Fintype.card_prod,
      Nat.cast_mul] at this
    rw [this, sq]

end Cslib.Probability
