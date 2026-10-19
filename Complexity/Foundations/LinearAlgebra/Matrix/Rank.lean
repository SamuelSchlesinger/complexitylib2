/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, subadditivity of matrix rank)

public import Complexity.Init
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Subadditivity of matrix rank

Over a field, the column space of `A + B` lies in the sum of the column spaces of `A` and `B`, so
the rank of a sum of matrices is at most the sum of their ranks (`Matrix.rank_add_le`). Negation
does not change the rank (`Matrix.rank_neg`), and scaling does not increase it, over any commutative
semiring with the strong rank condition (`Matrix.rank_smul_le`).

## Main results

* `Matrix.rank_add_le`, `Matrix.rank_sub_le`: rank is subadditive.
* `Matrix.rank_neg`: negation preserves rank.
* `Matrix.rank_smul_le`: scaling does not increase rank.

## References

These are standard facts of linear algebra; they are used to compare the ranks of communication
matrices in [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997].
-/

@[expose] public section

namespace Matrix

variable {m n K : Type*} [Fintype n]

/-- Negation does not change the rank of a matrix. -/
@[simp] theorem rank_neg {R : Type*} [CommRing R] (A : Matrix m n R) : (-A).rank = A.rank := by
  rw [← neg_one_smul R A]
  exact rank_smul_of_mem_nonZeroDivisors A isUnit_one.neg.mem_nonZeroDivisors

/-- Scaling a matrix does not increase its rank, over any commutative semiring with the strong rank
condition, such as a nontrivial commutative ring: `c • A = A (c • 1)`. -/
theorem rank_smul_le {R : Type*} [CommSemiring R] [StrongRankCondition R] (c : R)
    (A : Matrix m n R) : (c • A).rank ≤ A.rank := by
  classical
  simpa [Matrix.mul_smul] using rank_mul_le_left A (c • (1 : Matrix n n R))

variable [Field K]

/-- **Subadditivity of rank**: the rank of a sum of matrices over a field is at most the sum of
their ranks. -/
theorem rank_add_le (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  rw [rank, rank, rank, mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- The rank of a difference of matrices over a field is at most the sum of their ranks. -/
theorem rank_sub_le (A B : Matrix m n K) : (A - B).rank ≤ A.rank + B.rank := by
  simpa [sub_eq_add_neg] using rank_add_le A (-B)

end Matrix
