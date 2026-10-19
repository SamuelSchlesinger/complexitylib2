/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.Rank
import Complexity.Foundations.LinearAlgebra.Matrix.Rank

/-!
# Rank bounds from the leaves of a protocol

A protocol computing `f` partitions the inputs into the rectangles of its leaves, so any matrix
whose entry at `x` and `y` depends only on `f x y`, through a relabelling `g` of the outputs, is a
sum of `p.leaves` matrices of rank at most one: its rank is at most the number of leaves
(`Protocol.rank_of_comp_le_leaves`) and so at most `2 ^ d` for a protocol sending `d` bits
[Kushilevitz and Nisan, Chapter 1][KushilevitzNisan1997]. This applies in particular to the
*sign matrix* of a Boolean function, with entries `-1` where `f` is true and `1` elsewhere
(`signMatrix`), whose rank differs from that of the communication matrix by at most one
(`rank_signMatrix_le`, `rank_communicationMatrix_le_rank_signMatrix`).

When `f` is false somewhere, some leaf is labelled `false`, so the rank of the communication
matrix, which is at most the number of leaves labelled `true`, is less than the number of leaves
(`Protocol.rank_communicationMatrix_lt_leaves`) and less than `2 ^ d`
(`Protocol.rank_communicationMatrix_lt_two_pow`). A protocol that is only correct on a rectangle
`A × B` bounds the rank of the corresponding submatrix
(`Protocol.Solves.rank_communicationMatrix_le`).

## Main definitions

* `Cslib.Communication.signMatrix`: the `±1` sign matrix of a Boolean function.

## Main results

* `Cslib.Communication.rank_signMatrix_le`,
  `Cslib.Communication.rank_communicationMatrix_le_rank_signMatrix`: the ranks of the sign matrix
  and of the communication matrix differ by at most one.
* `Cslib.Communication.Protocol.rank_of_comp_le_leaves`: the rank bound for any relabelling of the
  outputs.
* `Cslib.Communication.Protocol.rank_signMatrix_le_leaves`: the rank bound for sign matrices.
* `Cslib.Communication.Protocol.rank_communicationMatrix_lt_leaves`,
  `Cslib.Communication.Protocol.rank_communicationMatrix_lt_two_pow`: the strict rank bound for
  functions that are false somewhere.
* `Cslib.Communication.Protocol.Solves.rank_communicationMatrix_le`: the rank bound on a
  rectangle.

## References

* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Communication

open Finset

variable {X Y Z : Type*}

/-! ### Sign matrices -/

/-- The sign matrix of a Boolean function `f` over `R`: rows are indexed by Alice's inputs,
columns by Bob's inputs, and the entry at `x` and `y` is `-1` if `f x y` and `1` otherwise. -/
def signMatrix (R : Type*) [One R] [Neg R] (f : X → Y → Bool) : Matrix X Y R :=
  Matrix.of fun x y => if f x y then -1 else 1

/-- The entries of the sign matrix. -/
@[simp] theorem signMatrix_apply (R : Type*) [One R] [Neg R] (f : X → Y → Bool) (x : X) (y : Y) :
    signMatrix R f x y = if f x y then -1 else 1 :=
  rfl

/-- The sign matrix is `J - 2 M_f`, for the all-ones matrix `J` and the communication matrix
`M_f`. -/
theorem signMatrix_eq_sub (R : Type*) [Ring R] (f : X → Y → Bool) :
    signMatrix R f = Matrix.of (fun _ _ => 1) - (2 : R) • communicationMatrix R f := by
  ext x y
  by_cases h : f x y <;> norm_num [h]

/-- The all-ones matrix has rank at most one. -/
private theorem rank_of_one_le [Fintype Y] (R : Type*) [CommSemiring R] [StrongRankCondition R] :
    (Matrix.of fun (_ : X) (_ : Y) => (1 : R)).rank ≤ 1 := by
  simpa [Matrix.vecMulVec] using Matrix.rank_vecMulVec_le (fun _ : X => (1 : R)) fun _ : Y => 1

section Field

variable [Fintype Y] {R : Type*} [Field R]

/-- The rank of the sign matrix exceeds that of the communication matrix by at most one. -/
theorem rank_signMatrix_le (f : X → Y → Bool) :
    (signMatrix R f).rank ≤ (communicationMatrix R f).rank + 1 := by
  rw [signMatrix_eq_sub, add_comm]
  exact (Matrix.rank_sub_le _ _).trans
    (add_le_add (rank_of_one_le R) (Matrix.rank_smul_le _ _))

/-- When `2` is invertible, the rank of the communication matrix exceeds that of the sign matrix
by at most one, since `M_f = (J - S_f) / 2`. -/
theorem rank_communicationMatrix_le_rank_signMatrix [NeZero (2 : R)] (f : X → Y → Bool) :
    (communicationMatrix R f).rank ≤ (signMatrix R f).rank + 1 := by
  have h : communicationMatrix R f = (2 : R)⁻¹ • (Matrix.of (fun _ _ => 1) - signMatrix R f) := by
    rw [signMatrix_eq_sub, sub_sub_cancel, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  rw [h, add_comm]
  exact (Matrix.rank_smul_le _ _).trans ((Matrix.rank_sub_le _ _).trans
    (add_le_add_left (rank_of_one_le R) _))

end Field

/-! ### Rank bounds for protocols -/

namespace Protocol

section Semiring

variable {R : Type*} [CommSemiring R] [StrongRankCondition R]

/-- **The rank bound on a rectangle.** If a protocol computes `f` on `A × B`, the rank of the
communication matrix of `f` restricted to `A × B` is at most the number of leaves labelled
`true`. -/
theorem Solves.rank_communicationMatrix_le {p : Protocol X Y Bool}
    {f : X → Y → Bool} {A : Set X} {B : Set Y} [Fintype B]
    (hp : p.Solves (fun x y b => f x y = b) A B) :
    (communicationMatrix R fun (x : A) (y : B) => f x y).rank ≤
      #{i | p.leafOutput i = true} := by
  classical
  set T : Finset (Fin p.leaves) := {i | p.leafOutput i = true}
  let U : Matrix A T R := Matrix.of fun x i => if x.1 ∈ p.leafAlice i then 1 else 0
  let V : Matrix T B R := Matrix.of fun i y => if y.1 ∈ p.leafBob i then 1 else 0
  have hUV : communicationMatrix R (fun (x : A) (y : B) => f x y) = U * V := by
    ext x y
    simp only [communicationMatrix_apply, Matrix.mul_apply, U, V, Matrix.of_apply, ite_mul,
      one_mul, zero_mul, ← ite_and]
    rw [sum_coe_sort T fun i => if x.1 ∈ p.leafAlice i ∧ y.1 ∈ p.leafBob i then (1 : R) else 0]
    simp only [← leaf_eq_iff, sum_ite_eq, T, mem_filter, mem_univ, true_and,
      ← run_eq_leafOutput_leaf, hp x.1 x.2 y.1 y.2]
  rw [hUV]
  exact (Matrix.rank_mul_le_left U V).trans ((Matrix.rank_le_card_width U).trans_eq
    (Fintype.card_coe T))

section Comp

variable [Fintype Y] {f : X → Y → Z} {p : Protocol X Y Z}

/-- **The rank bound for relabelled outputs.** If a protocol computes `f`, then for every
relabelling `g` of the outputs, the matrix with entry `g (f x y)` at `x` and `y` has rank at most
the number of leaves. -/
theorem rank_of_comp_le_leaves (hp : p.run = f) (g : Z → R) :
    (Matrix.of fun x y => g (f x y)).rank ≤ p.leaves := by
  classical
  let U : Matrix X (Fin p.leaves) R := Matrix.of fun x i => if x ∈ p.leafAlice i then 1 else 0
  let V : Matrix (Fin p.leaves) Y R :=
    Matrix.of fun i y => if y ∈ p.leafBob i then g (p.leafOutput i) else 0
  have hUV : (Matrix.of fun x y => g (f x y)) = U * V := by
    ext x y
    simp only [Matrix.mul_apply, U, V, Matrix.of_apply, ite_mul, one_mul, zero_mul, ← ite_and]
    simp only [← leaf_eq_iff, sum_ite_eq, mem_univ, ite_true, ← run_eq_leafOutput_leaf, hp]
  rw [hUV]
  exact (Matrix.rank_mul_le_left U V).trans ((Matrix.rank_le_card_width U).trans_eq
    (Fintype.card_fin _))

/-- If a protocol computes `f` with `d` bits, then for every relabelling `g` of the outputs, the
matrix with entry `g (f x y)` at `x` and `y` has rank at most `2 ^ d`. -/
theorem rank_of_comp_le_two_pow (hp : p.run = f) (g : Z → R) :
    (Matrix.of fun x y => g (f x y)).rank ≤ 2 ^ p.depth :=
  (rank_of_comp_le_leaves hp g).trans p.leaves_le_two_pow_depth

end Comp

section Strict

variable [Fintype Y] {f : X → Y → Bool} {p : Protocol X Y Bool}

/-- **The strict rank bound.** If a protocol computes a function `f` that is false somewhere, the
rank of the communication matrix of `f` is less than the number of leaves. -/
theorem rank_communicationMatrix_lt_leaves (hp : p.run = f) (h : ∃ x y, f x y = false) :
    (communicationMatrix R f).rank < p.leaves := by
  classical
  obtain ⟨x, y, hxy⟩ := h
  refine (rank_communicationMatrix_le hp).trans_lt
    ((card_lt_card (filter_ssubset.mpr ⟨p.leaf x y, mem_univ _, ?_⟩)).trans_eq (card_fin _))
  rw [← run_eq_leafOutput_leaf, hp, hxy]
  decide

/-- If a protocol sending `d` bits computes a function `f` that is false somewhere, the rank of the
communication matrix of `f` is less than `2 ^ d`. -/
theorem rank_communicationMatrix_lt_two_pow (hp : p.run = f) (h : ∃ x y, f x y = false) :
    (communicationMatrix R f).rank < 2 ^ p.depth :=
  (rank_communicationMatrix_lt_leaves hp h).trans_le p.leaves_le_two_pow_depth

end Strict

end Semiring

section Sign

variable [Fintype Y] {R : Type*} [CommRing R] [StrongRankCondition R] {f : X → Y → Bool}
  {p : Protocol X Y Bool}

/-- The rank of the sign matrix of a function computed by a protocol is at most the number of
leaves. -/
theorem rank_signMatrix_le_leaves (hp : p.run = f) : (signMatrix R f).rank ≤ p.leaves :=
  rank_of_comp_le_leaves hp fun b => if b then -1 else 1

/-- The rank of the sign matrix of a function computed by a protocol sending `d` bits is at most
`2 ^ d`. -/
theorem rank_signMatrix_le_two_pow (hp : p.run = f) : (signMatrix R f).rank ≤ 2 ^ p.depth :=
  (rank_signMatrix_le_leaves hp).trans p.leaves_le_two_pow_depth

end Sign

end Protocol

end Cslib.Communication
