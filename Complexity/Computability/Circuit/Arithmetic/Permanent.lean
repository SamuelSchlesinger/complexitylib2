/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.Determinant
public import Complexity.Computability.Circuit.Arithmetic.VNP
public import Complexity.Computability.Circuit.Formula
public import Mathlib.LinearAlgebra.Matrix.Permanent
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# The permanent polynomial family, Ryser's formula, VNP membership and projection closure

The *permanent family* `permFamily K` over a commutative semiring `K` consists of the permanents of
the generic `n × n` matrices `genericMatrix K n` in `n * n` variables. Like the determinant family
`detFamily K`, it is a p-family of degree at most `n` (`totalDegree_permanent_genericMatrix_le`,
`isPFamily_permFamily`).

Over every commutative ring `R`, Ryser's inclusion-exclusion formula (`Matrix.permanent_eq_ryser`)
expresses the permanent of an `n × n` matrix `A` as a signed sum over the `2 ^ n` subsets of
columns:

`A.permanent = ∑ S : Finset n, (-1) ^ (Fintype.card n - S.card) * ∏ i, ∑ j ∈ S, A i j`.

Writing the subset `S ⊆ Fin n` in terms of its `{0, 1}`-valued indicator variables expresses the
generic permanent as a `booleanSum` of a polynomial family in `VP K`, proving that
`permFamily K ∈ VNP K` over every commutative ring `K` (`permFamily_mem_VNP`) [Valiant1979Algebra;
Bürgisser, Proposition 2.12][Burgisser2000].

We also establish the fundamental projection closure properties of `permFamily K` over every
commutative semiring `K` [Valiant1979Algebra; Bürgisser, Lemma 2.9][Burgisser2000]:
* constants and variables are projections of `1 × 1` and `2 × 2` permanents;
* block-triangular and block-diagonal permanents factor as products of the diagonal blocks
  (`Matrix.permanent_fromBlocks_zero₂₁`, `Matrix.permanent_fromBlocks_zero₁₂`,
  `Matrix.permanent_fromBlocks_zero`), so products of permanent projections are permanent
  projections (`IsProjection.permanent_mul`);
* rooted permanent representations (`IsRootedPermProjection`) are closed under constants,
  variables, addition (`IsRootedPermProjection.add`) and multiplication
  (`IsRootedPermProjection.mul`), so every arithmetic formula `F` of size `s` computes a polynomial
  that is a projection of the `(s + 1) × (s + 1)` generic permanent
  (`Formula.isProjection_permanent`).

Valiant's full algebraic completeness theorem (that every family in `VNP K` is a p-projection of
`permFamily K` over fields of characteristic different from two) is not proved here.

## Main definitions

* `Cslib.Circuits.Arithmetic.permFamily`: the permanent polynomial family over `K`.
* `Cslib.Circuits.Arithmetic.ryserPoly`, `Cslib.Circuits.Arithmetic.ryserFamily`,
  `Cslib.Circuits.Arithmetic.ryserCircuit`: the inner polynomial, family and polynomial-size
  circuit for Ryser's formula.
* `Cslib.Circuits.Arithmetic.IsSubstEntry`, `Cslib.Circuits.Arithmetic.IsSubstMatrix`:
  variable-or-constant specialization entries and matrices.
* `Cslib.Circuits.Arithmetic.IsRootedPermProjection`: rooted permanent representations of
  polynomials.

## Main results

* `Matrix.permanent_fromBlocks_zero₂₁`, `Matrix.permanent_fromBlocks_zero₁₂`,
  `Matrix.permanent_fromBlocks_zero`: block-triangular and block-diagonal permanent factorization.
* `Matrix.permanent_succ_column_zero`, `Matrix.permanent_succ_row_zero`: Laplace expansion of the
  permanent along column `0` and row `0`.
* `Matrix.permanent_eq_ryser_bool`, `Matrix.permanent_eq_ryser`: Ryser's inclusion-exclusion
  formula for the permanent.
* `Cslib.Circuits.Arithmetic.isPFamily_permFamily`: `permFamily K` is a p-family.
* `Cslib.Circuits.Arithmetic.ryserFamily_mem_VP`: `ryserFamily R ∈ VP R`.
* `Cslib.Circuits.Arithmetic.permFamily_mem_VNP`: `permFamily R ∈ VNP R` over every commutative
  ring `R`.
* `Cslib.Circuits.Arithmetic.IsProjection.permanent_mul`,
  `Cslib.Circuits.Arithmetic.isProjection_permanent_mono`,
  `Cslib.Circuits.Arithmetic.isProjection_permanent_finset_prod`: multiplicative closure and
  dimension monotonicity of permanent projections.
* `Cslib.Circuits.Arithmetic.IsRootedPermProjection.add`,
  `Cslib.Circuits.Arithmetic.IsRootedPermProjection.mul`: additive and multiplicative closure of
  rooted permanent representations.
* `Cslib.Circuits.Formula.isProjection_permanent`: every arithmetic formula `F` of size `s`
  computes a projection of `(genericMatrix K (s + 1)).permanent`.

## References

* [L. G. Valiant, *Completeness classes in algebra*][Valiant1979Algebra]
* [P. Bürgisser, *Completeness and Reduction in Algebraic Complexity Theory*][Burgisser2000],
  Chapter 2
-/

@[expose] public section

/-! ### Ryser's formula and block-triangular permanents -/

namespace Matrix

open Equiv Equiv.Perm Finset Fintype

section BlockTriangular

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {R : Type*} [CommSemiring R]

/-- Reindexing both rows and columns of a square matrix by the same equivalence preserves its
permanent. -/
@[simp] theorem permanent_submatrix_equiv {m' : Type*} [Fintype m'] [DecidableEq m'] (e : m' ≃ m)
    (A : Matrix m m R) : (A.submatrix e e).permanent = A.permanent := by
  rw [permanent, permanent, ← (Equiv.permCongr e).sum_comp]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← e.prod_comp]
  exact Finset.prod_congr rfl fun i _ => by simp [submatrix_apply, Equiv.permCongr_apply]

/-- Reindexing a square matrix by an equivalence preserves its permanent. -/
theorem permanent_reindex_self {m' : Type*} [Fintype m'] [DecidableEq m'] (e : m ≃ m')
    (A : Matrix m m R) : (A.reindex e e).permanent = A.permanent :=
  permanent_submatrix_equiv e.symm A

/-- Reindexing the rows and columns of a square matrix by any two equivalences preserves its
permanent. -/
theorem permanent_submatrix_equiv_equiv {m' : Type*} [Fintype m'] [DecidableEq m']
    (e₁ e₂ : m' ≃ m) (A : Matrix m m R) : (A.submatrix e₁ e₂).permanent = A.permanent := by
  have h : A.submatrix e₁ e₂ = (A.submatrix e₂ e₂).submatrix (e₁.trans e₂.symm) id := by
    ext i j
    simp [submatrix_apply]
  rw [h, permanent_permute_cols, permanent_submatrix_equiv]

/-- Multilinearity of the permanent in a column. -/
@[simp] theorem permanent_updateCol_add (M : Matrix m m R) (j : m) (u v : m → R) :
    (M.updateCol j (u + v)).permanent =
      (M.updateCol j u).permanent + (M.updateCol j v).permanent := by
  simp only [permanent, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), updateCol_self,
    Pi.add_apply, add_mul, Finset.sum_add_distrib]
  congr 1 <;>
    refine Finset.sum_congr rfl fun p _ =>
      congrArg (_ * ·) (Finset.prod_congr rfl fun i hi => ?_) <;>
    simp only [ne_eq, Finset.ne_of_mem_erase hi, not_false_eq_true, updateCol_ne]

/-- Multilinearity of the permanent in a row. -/
@[simp] theorem permanent_updateRow_add (M : Matrix m m R) (i : m) (u v : m → R) :
    (M.updateRow i (u + v)).permanent =
      (M.updateRow i u).permanent + (M.updateRow i v).permanent := by
  rw [← permanent_transpose, ← updateCol_transpose, permanent_updateCol_add,
    updateCol_transpose, updateCol_transpose, permanent_transpose, permanent_transpose]

/-- If two matrices `M₁, M₂` agree with `M` outside row `r` and their `r`-th rows sum to row `r`
of `M`, then `M.permanent = M₁.permanent + M₂.permanent`. -/
theorem permanent_add_of_row_eq (M M₁ M₂ : Matrix m m R) (r : m)
    (hr : ∀ j, M r j = M₁ r j + M₂ r j)
    (h₁ : ∀ i ≠ r, ∀ j, M₁ i j = M i j)
    (h₂ : ∀ i ≠ r, ∀ j, M₂ i j = M i j) :
    M.permanent = M₁.permanent + M₂.permanent := by
  have hM : M = M.updateRow r (M₁ r + M₂ r) := by
    ext i j
    by_cases hir : i = r
    · subst hir; simp [hr j]
    · simp [hir]
  have hM₁ : M₁ = M.updateRow r (M₁ r) := by
    ext i j
    by_cases hir : i = r
    · subst hir; simp
    · simp [hir, h₁ i hir j]
  have hM₂ : M₂ = M.updateRow r (M₂ r) := by
    ext i j
    by_cases hir : i = r
    · subst hir; simp
    · simp [hir, h₂ i hir j]
  conv_lhs => rw [hM]
  rw [permanent_updateRow_add, ← hM₁, ← hM₂]

/-- Applying a ring homomorphism to the permanent of a matrix is the permanent of the mapped
matrix. -/
theorem _root_.RingHom.map_permanent {S : Type*} [CommSemiring S] (f : R →+* S)
    (M : Matrix m m R) : f M.permanent = (M.map f).permanent := by
  simp [permanent, map_sum, map_prod]

/-- Applying an algebra homomorphism to the permanent of a matrix is the permanent of the mapped
matrix. -/
theorem _root_.AlgHom.map_permanent {R₀ A B : Type*} [CommSemiring R₀] [CommSemiring A]
    [CommSemiring B] [Algebra R₀ A] [Algebra R₀ B] (f : A →ₐ[R₀] B) (M : Matrix m m A) :
    f M.permanent = (M.map f).permanent :=
  f.toRingHom.map_permanent M

set_option backward.isDefEq.respectTransparency false in
/-- The permanent of a `2 × 2` block matrix with the lower-left block equal to zero is the product
of the permanents of the diagonal blocks. -/
@[simp] theorem permanent_fromBlocks_zero₂₁ (A : Matrix m m R) (B : Matrix m n R)
    (D : Matrix n n R) : (fromBlocks A B 0 D).permanent = A.permanent * D.permanent := by
  classical
  simp_rw [permanent]
  convert
    Eq.symm <|
      sum_subset (M := R) (subset_univ ((sumCongrHom m n).range : Set (Perm (m ⊕ n))).toFinset) ?_
  · simp_rw [Finset.sum_mul_sum, ← sum_product', univ_product_univ]
    refine sum_nbij (fun σ => σ.fst.sumCongr σ.snd) ?_ ?_ ?_ ?_
    · intro σ₁₂ _
      simp
    · intro σ₁ _ σ₂ _ h
      have h2 : ∀ x, Perm.sumCongr σ₁.fst σ₁.snd x = Perm.sumCongr σ₂.fst σ₂.snd x :=
        DFunLike.congr_fun h
      simp only [Sum.map_inr, Sum.map_inl, Perm.sumCongr_apply, Sum.forall, Sum.inl.injEq,
        Sum.inr.injEq] at h2
      ext x
      · exact h2.left x
      · exact h2.right x
    · intro σ hσ
      rw [mem_coe, Set.mem_toFinset] at hσ
      obtain ⟨σ₁₂, hσ₁₂⟩ := hσ
      exact ⟨σ₁₂, mem_univ _, by simpa using hσ₁₂⟩
    · simp only [forall_prop_of_true, Prod.forall, mem_univ]
      intro σ₁ σ₂
      rw [Fintype.prod_sum_type]
      simp_rw [Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl, fromBlocks_apply₁₁,
        fromBlocks_apply₂₂]
  · rintro σ - hσn
    have h1 : ¬∀ x, ∃ y, Sum.inl y = σ (Sum.inl x) := by
      rw [Set.mem_toFinset] at hσn
      simpa only [Set.MapsTo, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] using
        mt mem_sumCongrHom_range_of_perm_mapsTo_inl hσn
    obtain ⟨a, ha⟩ := not_forall.mp h1
    rcases hx : σ (Sum.inl a) with a2 | b
    · exact absurd hx.symm ((not_exists.mp ha) a2)
    · rw [Finset.prod_eq_zero (Finset.mem_univ (Sum.inl a))]
      rw [hx, fromBlocks_apply₂₁, zero_apply]

/-- The permanent of a `2 × 2` block matrix with the upper-right block equal to zero is the product
of the permanents of the diagonal blocks. -/
@[simp] theorem permanent_fromBlocks_zero₁₂ (A : Matrix m m R) (C : Matrix n m R)
    (D : Matrix n n R) : (fromBlocks A 0 C D).permanent = A.permanent * D.permanent := by
  rw [← permanent_transpose, fromBlocks_transpose, transpose_zero, permanent_fromBlocks_zero₂₁,
    permanent_transpose, permanent_transpose]

/-- The permanent of a block-diagonal `2 × 2` matrix is the product of the permanents of its
diagonal blocks. -/
theorem permanent_fromBlocks_zero (A : Matrix m m R) (D : Matrix n n R) :
    (fromBlocks A (0 : Matrix m n R) 0 D).permanent = A.permanent * D.permanent :=
  permanent_fromBlocks_zero₂₁ A 0 D

/-- Involution on `(Unit ⊕ m) ⊕ (Unit ⊕ n)` swapping the two root elements `inl (inl ())` and
`inr (inl ())`. -/
def swapRootEquiv (m n : Type*) : ((Unit ⊕ m) ⊕ (Unit ⊕ n)) ≃ ((Unit ⊕ m) ⊕ (Unit ⊕ n)) where
  toFun
    | .inl (.inl u) => .inr (.inl u)
    | .inl (.inr i) => .inl (.inr i)
    | .inr (.inl u) => .inl (.inl u)
    | .inr (.inr j) => .inr (.inr j)
  invFun
    | .inl (.inl u) => .inr (.inl u)
    | .inl (.inr i) => .inl (.inr i)
    | .inr (.inl u) => .inl (.inl u)
    | .inr (.inr j) => .inr (.inr j)
  left_inv x := by rcases x with (⟨⟨⟩⟩ | i) | (⟨⟨⟩⟩ | j) <;> rfl
  right_inv x := by rcases x with (⟨⟨⟩⟩ | i) | (⟨⟨⟩⟩ | j) <;> rfl

/-- Rooted permanent multiplication block matrix on `Unit ⊕ (m ⊕ (Unit ⊕ n))`. -/
def rootedMul (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R) (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R) :
    Matrix (Unit ⊕ (m ⊕ (Unit ⊕ n))) (Unit ⊕ (m ⊕ (Unit ⊕ n))) R :=
  (fromBlocks M₁ 0 (fromBlocks (1 : Matrix Unit Unit R) 0 0 0) M₂).submatrix
    (Equiv.sumAssoc Unit m (Unit ⊕ n)).symm
    ((Equiv.sumAssoc Unit m (Unit ⊕ n)).symm.trans (swapRootEquiv m n))

/-- The permanent of `rootedMul M₁ M₂` is the product of the permanents of `M₁` and `M₂`. -/
theorem permanent_rootedMul (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R)
    (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R) :
    (rootedMul M₁ M₂).permanent = M₁.permanent * M₂.permanent := by
  rw [rootedMul, permanent_submatrix_equiv_equiv, permanent_fromBlocks_zero₁₂]

/-- If the internal blocks of `M₁` and `M₂` have permanent `1`, then so does the internal block of
`rootedMul M₁ M₂`. -/
theorem permanent_toBlocks₂₂_rootedMul (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R)
    (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R)
    (h₁ : M₁.toBlocks₂₂.permanent = 1) (h₂ : M₂.toBlocks₂₂.permanent = 1) :
    (rootedMul M₁ M₂).toBlocks₂₂.permanent = 1 := by
  have hblk : (rootedMul M₁ M₂).toBlocks₂₂ =
      fromBlocks M₁.toBlocks₂₂ (of fun i => Sum.elim (M₁.toBlocks₂₁ i) 0) 0
        (fromBlocks (1 : Matrix Unit Unit R) M₂.toBlocks₁₂ 0 M₂.toBlocks₂₂) := by
    ext (i₁ | (⟨⟩ | i₂)) (j₁ | (⟨⟩ | j₂)) <;> rfl
  rw [hblk, permanent_fromBlocks_zero₂₁, permanent_fromBlocks_zero₂₁, permanent_one,
    h₁, h₂, mul_one, mul_one]

/-- Rooted permanent addition block matrix on `Unit ⊕ (m ⊕ (Unit ⊕ n))`. -/
def rootedAdd (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R) (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R) :
    Matrix (Unit ⊕ (m ⊕ (Unit ⊕ n))) (Unit ⊕ (m ⊕ (Unit ⊕ n))) R :=
  (fromBlocks
    M₁
    (fromBlocks M₂.toBlocks₁₁ M₂.toBlocks₁₂ 0 0)
    (fromBlocks (1 : Matrix Unit Unit R) 0 0 0)
    (fromBlocks (1 : Matrix Unit Unit R) 0 M₂.toBlocks₂₁ M₂.toBlocks₂₂)).submatrix
    (Equiv.sumAssoc Unit m (Unit ⊕ n)).symm
    (Equiv.sumAssoc Unit m (Unit ⊕ n)).symm

/-- If the internal blocks of `M₁` and `M₂` have permanent `1`, then so does the internal block of
`rootedAdd M₁ M₂`. -/
theorem permanent_toBlocks₂₂_rootedAdd (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R)
    (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R)
    (h₁ : M₁.toBlocks₂₂.permanent = 1) (h₂ : M₂.toBlocks₂₂.permanent = 1) :
    (rootedAdd M₁ M₂).toBlocks₂₂.permanent = 1 := by
  have hblk : (rootedAdd M₁ M₂).toBlocks₂₂ =
      fromBlocks M₁.toBlocks₂₂ 0 0
        (fromBlocks (1 : Matrix Unit Unit R) 0 M₂.toBlocks₂₁ M₂.toBlocks₂₂) := by
    ext (i₁ | (⟨⟩ | i₂)) (j₁ | (⟨⟩ | j₂)) <;> rfl
  rw [hblk, permanent_fromBlocks_zero, permanent_fromBlocks_zero₁₂, permanent_one,
    h₁, h₂, mul_one, mul_one]

/-- If the internal blocks of `M₁` and `M₂` have permanent `1`, then the permanent of
`rootedAdd M₁ M₂` is the sum of the permanents of `M₁` and `M₂`. -/
theorem permanent_rootedAdd (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R)
    (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R)
    (h₁ : M₁.toBlocks₂₂.permanent = 1) (h₂ : M₂.toBlocks₂₂.permanent = 1) :
    (rootedAdd M₁ M₂).permanent = M₁.permanent + M₂.permanent := by
  rw [rootedAdd, permanent_submatrix_equiv]
  let B₁ : Matrix ((Unit ⊕ m) ⊕ (Unit ⊕ n)) ((Unit ⊕ m) ⊕ (Unit ⊕ n)) R :=
    fromBlocks M₁ (fromBlocks M₂.toBlocks₁₁ M₂.toBlocks₁₂ 0 0) 0
      (fromBlocks (1 : Matrix Unit Unit R) 0 M₂.toBlocks₂₁ M₂.toBlocks₂₂)
  let B₂ : Matrix ((Unit ⊕ m) ⊕ (Unit ⊕ n)) ((Unit ⊕ m) ⊕ (Unit ⊕ n)) R :=
    fromBlocks M₁ (fromBlocks M₂.toBlocks₁₁ M₂.toBlocks₁₂ 0 0)
      (fromBlocks (1 : Matrix Unit Unit R) 0 0 0)
      (fromBlocks (0 : Matrix Unit Unit R) 0 M₂.toBlocks₂₁ M₂.toBlocks₂₂)
  rw [permanent_add_of_row_eq _ B₁ B₂ (Sum.inr (Sum.inl ()))
    (fun j => by rcases j with (⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂) <;> simp [B₁, B₂])
    (fun i hi j => by
      rcases i with (⟨⟨⟩⟩ | i₁) | (⟨⟨⟩⟩ | i₂)
      · rcases j with (⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂) <;> rfl
      · rcases j with (⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂) <;> rfl
      · exact (hi rfl).elim
      · rcases j with (⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂) <;> rfl)
    (fun i hi j => by
      rcases i with (⟨⟨⟩⟩ | i₁) | (⟨⟨⟩⟩ | i₂)
      · rcases j with (⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂) <;> rfl
      · rcases j with (⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂) <;> rfl
      · exact (hi rfl).elim
      · rcases j with (⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂) <;> rfl)]
  have hB₁ : B₁.permanent = M₁.permanent := by
    rw [permanent_fromBlocks_zero₂₁, permanent_fromBlocks_zero₁₂, permanent_one, h₂, mul_one,
      mul_one]
  have hB₂_swap : B₂.submatrix (swapRootEquiv m n) (Equiv.refl _) =
      fromBlocks (fromBlocks (1 : Matrix Unit Unit R) 0 M₁.toBlocks₂₁ M₁.toBlocks₂₂) 0
        (fromBlocks M₁.toBlocks₁₁ M₁.toBlocks₁₂ 0 0) M₂ := by
    ext ((⟨⟨⟩⟩ | i₁) | (⟨⟨⟩⟩ | i₂)) ((⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂)) <;> rfl
  have hB₂ : B₂.permanent = M₂.permanent := by
    rw [← permanent_submatrix_equiv_equiv (swapRootEquiv m n) (Equiv.refl _), hB₂_swap,
      permanent_fromBlocks_zero₁₂, permanent_fromBlocks_zero₁₂, permanent_one, h₁, mul_one,
      one_mul]
  rw [hB₁, hB₂]

/-- **Laplace expansion of the permanent along column 0.** -/
theorem permanent_succ_column_zero {k : ℕ} (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    A.permanent = ∑ i : Fin (k + 1), A i 0 * (A.submatrix i.succAbove Fin.succ).permanent := by
  rw [Matrix.permanent, Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product, Matrix.submatrix]
  refine Finset.sum_congr rfl fun i _ => Fin.cases ?_ (fun i => ?_) i
  · simp [Fin.prod_univ_succ, Matrix.permanent, Finset.mul_sum]
  · rw [← permanent_permute_cols i.cycleRange, Matrix.permanent, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [Fin.prod_univ_succ, Fin.succAbove_cycleRange]

/-- **Laplace expansion of the permanent along row 0.** -/
theorem permanent_succ_row_zero {k : ℕ} (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    A.permanent = ∑ j : Fin (k + 1), A 0 j * (A.submatrix Fin.succ j.succAbove).permanent := by
  rw [← permanent_transpose A, permanent_succ_column_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← permanent_transpose]
  simp only [transpose_apply, transpose_submatrix, transpose_transpose]

end BlockTriangular

section Ryser

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- Boolean-indicator form of Ryser's inclusion-exclusion formula for the permanent. -/
theorem permanent_eq_ryser_bool (A : Matrix n n R) :
    A.permanent =
      ∑ e : n → Bool,
        (∏ j : n, if e j then (1 : R) else -1) *
          ∏ i : n, ∑ j : n, if e j then A i j else 0 := by
  have hprod (e : n → Bool) :
      (∏ i : n, ∑ j : n, if e j then A i j else 0) =
        ∑ f : n → n, (if ∀ i, e (f i) = true then (1 : R) else 0) * ∏ i : n, A i (f i) := by
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    split_ifs with hf
    · rw [one_mul]
      exact Finset.prod_congr rfl fun i _ => by simp [hf i]
    · rw [zero_mul]
      push Not at hf
      obtain ⟨i, hi⟩ := hf
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have hstep1 :
      (∑ e : n → Bool,
        (∏ j : n, if e j then (1 : R) else -1) *
          ∏ i : n, ∑ j : n, if e j then A i j else 0) =
      ∑ f : n → n,
        (∑ e : n → Bool,
          (∏ j : n, if e j then (1 : R) else -1) *
            (if ∀ i, e (f i) = true then (1 : R) else 0)) *
          ∏ i : n, A i (f i) := by
    calc _ = ∑ e : n → Bool, ∑ f : n → n,
          ((∏ j : n, if e j then (1 : R) else -1) *
            (if ∀ i, e (f i) = true then (1 : R) else 0)) * ∏ i : n, A i (f i) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [hprod e, Finset.mul_sum]
          exact Finset.sum_congr rfl fun f _ => (mul_assoc _ _ _).symm
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun f _ => (Finset.sum_mul _ _ _).symm
  rw [hstep1]
  have hfactor (f : n → n) (e : n → Bool) :
      (∏ j : n, if e j then (1 : R) else -1) *
          (if ∀ i, e (f i) = true then (1 : R) else 0) =
        ∏ j : n, if e j then (1 : R) else if j ∈ univ.image f then 0 else -1 := by
    split_ifs with hf
    · rw [mul_one]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hej : e j = true
      · simp [hej]
      · have hj : j ∉ univ.image f := by
          intro hmem
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
          exact hej (hf i)
        simp [hej, hj]
    · rw [mul_zero]
      push Not at hf
      obtain ⟨i, hi⟩ := hf
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ (f i)) ?_
      have hmem : f i ∈ univ.image f := Finset.mem_image_of_mem f (Finset.mem_univ i)
      simp [hi, hmem]
  have hsum_e (f : n → n) :
      (∑ e : n → Bool,
          (∏ j : n, if e j then (1 : R) else -1) *
            (if ∀ i, e (f i) = true then (1 : R) else 0)) =
        if Function.Surjective f then (1 : R) else 0 := by
    simp_rw [hfactor]
    rw [← Fintype.prod_sum (fun (j : n) (b : Bool) =>
      if b = true then (1 : R) else if j ∈ univ.image f then 0 else -1)]
    have h1 (j : n) :
        (∑ b : Bool, if b = true then (1 : R) else if j ∈ univ.image f then 0 else -1) =
          if j ∈ univ.image f then (1 : R) else 0 := by
      rw [Fintype.sum_bool]
      by_cases hj : j ∈ univ.image f <;> simp [hj]
    simp_rw [h1]
    split_ifs with hsurj
    · refine Finset.prod_eq_one fun j _ => ?_
      obtain ⟨i, rfl⟩ := hsurj j
      have hmem : f i ∈ univ.image f := Finset.mem_image_of_mem f (Finset.mem_univ i)
      simp [hmem]
    · unfold Function.Surjective at hsurj
      push Not at hsurj
      obtain ⟨j, hj⟩ := hsurj
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      have hj' : j ∉ univ.image f := by simpa using hj
      simp [hj']
  have hstep2 :
      (∑ f : n → n,
        (∑ e : n → Bool,
          (∏ j : n, if e j then (1 : R) else -1) *
            (if ∀ i, e (f i) = true then (1 : R) else 0)) *
          ∏ i : n, A i (f i)) =
      ∑ f : n → n, (if Function.Surjective f then (1 : R) else 0) * ∏ i : n, A i (f i) :=
    Finset.sum_congr rfl fun f _ => by rw [hsum_e f]
  rw [hstep2, ← permanent_transpose, permanent]
  have hbij :
      (∑ σ : Perm n, ∏ i : n, Aᵀ (σ i) i) =
        ∑ f ∈ univ.filter (fun f : n → n => Function.Surjective f), ∏ i : n, A i (f i) := by
    refine Finset.sum_bij (fun (σ : Perm n) _ => (σ : n → n)) ?_ ?_ ?_ ?_
    · intro σ _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.surjective⟩
    · intro σ₁ _ σ₂ _ h
      exact DFunLike.coe_injective h
    · intro f hf
      have hsurj : Function.Surjective f := (Finset.mem_filter.mp hf).2
      exact ⟨Equiv.ofBijective f (Finite.surjective_iff_bijective.mp hsurj),
        Finset.mem_univ _, rfl⟩
    · intro σ _
      rfl
  rw [hbij, Finset.sum_filter]
  refine Finset.sum_congr rfl fun f _ => ?_
  split_ifs <;> ring

/-- **Ryser's formula** for the permanent over every commutative ring
[Bürgisser, Proposition 2.12][Burgisser2000]:
`A.permanent = ∑ S : Finset n, (-1) ^ (Fintype.card n - S.card) * ∏ i, ∑ j ∈ S, A i j`. -/
theorem permanent_eq_ryser (A : Matrix n n R) :
    A.permanent =
      ∑ S : Finset n, (-1 : R) ^ (Fintype.card n - S.card) * ∏ i : n, ∑ j ∈ S, A i j := by
  rw [permanent_eq_ryser_bool]
  let eFinset : Finset n ≃ (n → Bool) :=
    { toFun := fun S j => decide (j ∈ S)
      invFun := fun e => univ.filter fun j => e j = true
      left_inv := fun S => by ext j; simp
      right_inv := fun e => by funext j; simp }
  rw [← eFinset.sum_comp]
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 1
  · have hsign :
        (∏ j : n, if eFinset S j = true then (1 : R) else -1) =
          ∏ j ∈ Sᶜ, (-1 : R) := by
      rw [← Finset.prod_compl_mul_prod S]
      have hS1 : ∏ j ∈ S, (if eFinset S j = true then (1 : R) else -1) = 1 :=
        Finset.prod_eq_one fun j hj => by simp [eFinset, hj]
      have hSc : ∏ j ∈ Sᶜ, (if eFinset S j = true then (1 : R) else -1) = ∏ j ∈ Sᶜ, (-1 : R) :=
        Finset.prod_congr rfl fun j hj => by
          have : j ∉ S := Finset.mem_compl.mp hj
          simp [eFinset, this]
      rw [hS1, hSc, mul_one]
    rw [hsign, Finset.prod_const, Finset.card_compl]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp [eFinset]

end Ryser

end Matrix

/-! ### Arithmetic circuit combinators, the permanent family and `permFamily ∈ VNP` -/

namespace Cslib.Circuits.Arithmetic

open MvPolynomial Finset

universe u

variable {K : Type u} [CommSemiring K] {n m : ℕ}

/-! #### Constructive arithmetic circuit combinators -/

section Combinators

variable {R : Type u} [CommSemiring R]

/-- The 1-gate arithmetic circuit computing the constant `a`. -/
def constCircuit (a : R) : Circuit (arithSignature R) n 1 :=
  Circuit.oneGate (.const a) Fin.elim0

omit [CommSemiring R] in
@[simp] theorem size_constCircuit (a : R) : (constCircuit (n := n) a).size = 1 := rfl

@[simp] theorem polynomial_constCircuit (a : R) :
    (constCircuit (n := n) a).polynomial 0 = C a := rfl

/-- The 0-gate arithmetic circuit reading input variable `i`. -/
def varCircuit (i : Fin n) : Circuit (arithSignature R) n 1 :=
  Circuit.wiring (arithSignature R) fun _ => i

omit [CommSemiring R] in
@[simp] theorem size_varCircuit (i : Fin n) : (varCircuit (R := R) i).size = 0 := rfl

@[simp] theorem polynomial_varCircuit (i : Fin n) :
    (varCircuit (R := R) i).polynomial 0 = X i := rfl

/-- The arithmetic circuit adding the outputs of `c₁` and `c₂`. -/
def addCircuit (c₁ c₂ : Circuit (arithSignature R) n 1) : Circuit (arithSignature R) n 1 :=
  (Circuit.oneGate (σ := arithSignature R) .add ![0, 1]).comp (c₁.append c₂)

omit [CommSemiring R] in
@[simp] theorem size_addCircuit (c₁ c₂ : Circuit (arithSignature R) n 1) :
    (addCircuit c₁ c₂).size = c₁.size + c₂.size + 1 := rfl

@[simp] theorem polynomial_addCircuit (c₁ c₂ : Circuit (arithSignature R) n 1) :
    (addCircuit c₁ c₂).polynomial 0 = c₁.polynomial 0 + c₂.polynomial 0 := by
  simp only [addCircuit, Circuit.polynomial, Circuit.eval_comp, Circuit.eval_append,
    Circuit.eval_oneGate, arithInterpretationWith, Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

/-- The arithmetic circuit multiplying the outputs of `c₁` and `c₂`. -/
def mulCircuit (c₁ c₂ : Circuit (arithSignature R) n 1) : Circuit (arithSignature R) n 1 :=
  (Circuit.oneGate (σ := arithSignature R) .mul ![0, 1]).comp (c₁.append c₂)

omit [CommSemiring R] in
@[simp] theorem size_mulCircuit (c₁ c₂ : Circuit (arithSignature R) n 1) :
    (mulCircuit c₁ c₂).size = c₁.size + c₂.size + 1 := rfl

@[simp] theorem polynomial_mulCircuit (c₁ c₂ : Circuit (arithSignature R) n 1) :
    (mulCircuit c₁ c₂).polynomial 0 = c₁.polynomial 0 * c₂.polynomial 0 := by
  simp only [mulCircuit, Circuit.polynomial, Circuit.eval_comp, Circuit.eval_append,
    Circuit.eval_oneGate, arithInterpretationWith, Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

/-- Reindex the input variables of an arithmetic circuit along `ρ : Fin m → Fin n` with zero
additional gates. -/
def reindexCircuit (ρ : Fin m → Fin n) (c : Circuit (arithSignature R) m 1) :
    Circuit (arithSignature R) n 1 :=
  c.comp (Circuit.wiring (arithSignature R) ρ)

omit [CommSemiring R] in
@[simp] theorem size_reindexCircuit (ρ : Fin m → Fin n) (c : Circuit (arithSignature R) m 1) :
    (reindexCircuit ρ c).size = c.size :=
  Nat.zero_add c.size

@[simp] theorem polynomial_reindexCircuit (ρ : Fin m → Fin n)
    (c : Circuit (arithSignature R) m 1) :
    (reindexCircuit ρ c).polynomial 0 = MvPolynomial.rename ρ (c.polynomial 0) := by
  have hrename : MvPolynomial.rename ρ = aeval (X ∘ ρ : Fin m → MvPolynomial (Fin n) R) :=
    MvPolynomial.algHom_ext fun i => by simp
  rw [hrename, c.aeval_polynomial_mvPolynomial (X ∘ ρ) 0,
    reindexCircuit, Circuit.polynomial, Circuit.eval_comp, Circuit.eval_wiring]

/-- Sum a finite family of single-output arithmetic circuits. -/
def finSumCircuit : {k : ℕ} → (Fin k → Circuit (arithSignature R) n 1) →
    Circuit (arithSignature R) n 1
  | 0, _ => constCircuit 0
  | k + 1, cs => addCircuit (finSumCircuit fun j => cs j.castSucc) (cs (Fin.last k))

@[simp] theorem size_finSumCircuit :
    {k : ℕ} → (cs : Fin k → Circuit (arithSignature R) n 1) →
      (finSumCircuit cs).size = 1 + ∑ j : Fin k, ((cs j).size + 1)
  | 0, _ => by simp [finSumCircuit]
  | k + 1, cs => by
    rw [finSumCircuit, size_addCircuit, size_finSumCircuit, Fin.sum_univ_castSucc]
    omega

@[simp] theorem polynomial_finSumCircuit :
    {k : ℕ} → (cs : Fin k → Circuit (arithSignature R) n 1) →
      (finSumCircuit cs).polynomial 0 = ∑ j : Fin k, (cs j).polynomial 0
  | 0, _ => by simp [finSumCircuit]
  | k + 1, cs => by
    rw [finSumCircuit, polynomial_addCircuit, polynomial_finSumCircuit, Fin.sum_univ_castSucc]

/-- Multiply a finite family of single-output arithmetic circuits. -/
def finProdCircuit : {k : ℕ} → (Fin k → Circuit (arithSignature R) n 1) →
    Circuit (arithSignature R) n 1
  | 0, _ => constCircuit 1
  | k + 1, cs => mulCircuit (finProdCircuit fun j => cs j.castSucc) (cs (Fin.last k))

@[simp] theorem size_finProdCircuit :
    {k : ℕ} → (cs : Fin k → Circuit (arithSignature R) n 1) →
      (finProdCircuit cs).size = 1 + ∑ j : Fin k, ((cs j).size + 1)
  | 0, _ => by simp [finProdCircuit]
  | k + 1, cs => by
    rw [finProdCircuit, size_mulCircuit, size_finProdCircuit, Fin.sum_univ_castSucc]
    omega

@[simp] theorem polynomial_finProdCircuit :
    {k : ℕ} → (cs : Fin k → Circuit (arithSignature R) n 1) →
      (finProdCircuit cs).polynomial 0 = ∏ j : Fin k, (cs j).polynomial 0
  | 0, _ => by simp [finProdCircuit]
  | k + 1, cs => by
    rw [finProdCircuit, polynomial_mulCircuit, polynomial_finProdCircuit, Fin.prod_univ_castSucc]

end Combinators

section RingCombinators

variable {R : Type u} [CommRing R]

/-- The arithmetic circuit negating `c` by multiplying by `-1`. -/
def negCircuit (c : Circuit (arithSignature R) n 1) : Circuit (arithSignature R) n 1 :=
  mulCircuit (constCircuit (-1)) c

@[simp] theorem size_negCircuit (c : Circuit (arithSignature R) n 1) :
    (negCircuit c).size = 1 + c.size + 1 := rfl

@[simp] theorem polynomial_negCircuit (c : Circuit (arithSignature R) n 1) :
    (negCircuit c).polynomial 0 = -c.polynomial 0 := by
  simp [negCircuit]

/-- The arithmetic circuit subtracting `c₂` from `c₁`. -/
def subCircuit (c₁ c₂ : Circuit (arithSignature R) n 1) : Circuit (arithSignature R) n 1 :=
  addCircuit c₁ (negCircuit c₂)

@[simp] theorem size_subCircuit (c₁ c₂ : Circuit (arithSignature R) n 1) :
    (subCircuit c₁ c₂).size = c₁.size + (1 + c₂.size + 1) + 1 := rfl

@[simp] theorem polynomial_subCircuit (c₁ c₂ : Circuit (arithSignature R) n 1) :
    (subCircuit c₁ c₂).polynomial 0 = c₁.polynomial 0 - c₂.polynomial 0 := by
  simp [subCircuit, sub_eq_add_neg]

end RingCombinators

/-! #### The permanent polynomial family -/

/-- The generic permanent has total degree at most `n`. -/
theorem totalDegree_permanent_genericMatrix_le (n : ℕ) :
    (genericMatrix K n).permanent.totalDegree ≤ n := by
  rw [Matrix.permanent]
  refine totalDegree_finsetSum_le fun σ _ => ?_
  refine (totalDegree_finsetProd _ _).trans ?_
  calc _ ≤ ∑ _i : Fin n, 1 :=
        Finset.sum_le_sum fun i _ => (totalDegree_monomial_le _ _).trans (by simp)
    _ = n := by simp

/-- The permanent family over `K` [Valiant1979Algebra; Bürgisser, Chapter 2][Burgisser2000]: its
`n`-th member is the permanent of `genericMatrix K n`, a polynomial in `n * n` variables. -/
noncomputable def permFamily (K : Type u) [CommSemiring K] : PolynomialFamily K where
  vars n := n * n
  poly n := (genericMatrix K n).permanent

@[simp] theorem permFamily_vars (n : ℕ) : (permFamily K).vars n = n * n := rfl

@[simp] theorem permFamily_poly (n : ℕ) : (permFamily K).poly n = (genericMatrix K n).permanent :=
  rfl

/-- The permanent family over `K` is a p-family (`vars n = n ^ 2` and `totalDegree ≤ n`). -/
theorem isPFamily_permFamily : (permFamily K).IsPFamily :=
  ⟨PolynomiallyBounded.id.mul PolynomiallyBounded.id,
    PolynomiallyBounded.id.mono_of_le (totalDegree_permanent_genericMatrix_le (K := K))⟩

/-- Evaluating the permanent of `genericMatrix K n` at `x` gives the permanent of the matrix of
values `x (finProdFinEquiv (i, j))`. -/
theorem aeval_permanent_genericMatrix {A : Type*} [CommSemiring A] [Algebra K A]
    (x : Fin (n * n) → A) :
    aeval x (genericMatrix K n).permanent =
      (Matrix.of fun i j : Fin n => x (finProdFinEquiv (i, j))).permanent := by
  rw [AlgHom.map_permanent]
  congr 1
  ext i j
  simp [genericMatrix]

/-- Applying a projection `ρ` to `(genericMatrix K m).permanent` gives the permanent of the
specialized matrix. -/
theorem projection_permanent_genericMatrix {σ : Type*} (ρ : Fin (m * m) → σ ⊕ K) :
    projection ρ (genericMatrix K m).permanent =
      (Matrix.of fun i j : Fin m =>
        Sum.elim X (fun a => C a) (ρ (finProdFinEquiv (i, j)))).permanent :=
  aeval_permanent_genericMatrix _

/-! #### Ryser's polynomial family and `permFamily ∈ VNP` -/

section RyserVNP

variable {R : Type u} [CommRing R]

/-- The inner polynomial of Ryser's formula in `n * n + n` variables: the first `n * n` variables
are the entries of `genericMatrix R n` and the last `n` variables are `{0, 1}`-valued column
indicators. -/
noncomputable def ryserPoly (R : Type u) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin (n * n + n)) R :=
  (∏ j : Fin n, (2 * X (Fin.natAdd (n * n) j) - 1)) *
    ∏ i : Fin n, ∑ j : Fin n,
      X (Fin.natAdd (n * n) j) * X (Fin.castAdd n (finProdFinEquiv (i, j)))

private theorem totalDegree_X_le' {σ : Type*} (i : σ) :
    (X i : MvPolynomial σ R).totalDegree ≤ 1 :=
  (totalDegree_monomial_le _ _).trans (by simp)

/-- The Ryser inner polynomial has total degree at most `3 * n`. -/
theorem totalDegree_ryserPoly_le (n : ℕ) : (ryserPoly R n).totalDegree ≤ 3 * n := by
  rw [ryserPoly]
  refine (totalDegree_mul _ _).trans ?_
  have h1 : (∏ j : Fin n, (2 * X (Fin.natAdd (n * n) j) - 1 :
      MvPolynomial (Fin (n * n + n)) R)).totalDegree ≤ n := by
    refine (totalDegree_finsetProd _ _).trans ?_
    calc _ ≤ ∑ _j : Fin n, 1 := Finset.sum_le_sum fun j _ => ?_
      _ = n := by simp
    rw [sub_eq_add_neg, show (2 : MvPolynomial (Fin (n * n + n)) R) = C 2 from (map_ofNat C 2).symm]
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_mul _ _).trans (by simpa using totalDegree_X_le' _)
    · rw [← map_one C, ← map_neg C, totalDegree_C]
      omega
  have h2 : (∏ i : Fin n, ∑ j : Fin n,
      (X (Fin.natAdd (n * n) j) * X (Fin.castAdd n (finProdFinEquiv (i, j))) :
        MvPolynomial (Fin (n * n + n)) R)).totalDegree ≤ 2 * n := by
    refine (totalDegree_finsetProd _ _).trans ?_
    calc _ ≤ ∑ _i : Fin n, 2 := Finset.sum_le_sum fun i _ => ?_
      _ = 2 * n := by simp [mul_comm]
    refine totalDegree_finsetSum_le fun j _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    exact Nat.add_le_add (totalDegree_X_le' _) (totalDegree_X_le' _)
  omega

/-- The polynomial family of Ryser inner polynomials over `R`. -/
noncomputable def ryserFamily (R : Type u) [CommRing R] : PolynomialFamily R where
  vars n := n * n + n
  poly n := ryserPoly R n

/-- The Ryser inner polynomial family is a p-family. -/
theorem isPFamily_ryserFamily : (ryserFamily R).IsPFamily :=
  ⟨(PolynomiallyBounded.id.mul PolynomiallyBounded.id).add PolynomiallyBounded.id,
    ((PolynomiallyBounded.const 3).mul PolynomiallyBounded.id).mono_of_le
      (totalDegree_ryserPoly_le (R := R))⟩

/-- Explicit polynomial-size arithmetic circuit computing `ryserPoly R n`. -/
def ryserCircuit (R : Type u) [CommRing R] (n : ℕ) :
    Circuit (arithSignature R) (n * n + n) 1 :=
  mulCircuit
    (finProdCircuit fun j : Fin n =>
      subCircuit
        (mulCircuit (constCircuit 2) (varCircuit (Fin.natAdd (n * n) j)))
        (constCircuit 1))
    (finProdCircuit fun i : Fin n =>
      finSumCircuit fun j : Fin n =>
        mulCircuit
          (varCircuit (Fin.natAdd (n * n) j))
          (varCircuit (Fin.castAdd n (finProdFinEquiv (i, j)))))

@[simp] theorem polynomial_ryserCircuit (n : ℕ) :
    (ryserCircuit R n).polynomial 0 = ryserPoly R n := by
  simp only [ryserCircuit, polynomial_mulCircuit, polynomial_finProdCircuit,
    polynomial_finSumCircuit, polynomial_subCircuit, polynomial_constCircuit,
    polynomial_varCircuit, map_ofNat, map_one, ryserPoly]

/-- The size of `ryserCircuit R n` is `2 * n ^ 2 + 9 * n + 3`. -/
theorem size_ryserCircuit (n : ℕ) :
    (ryserCircuit R n).size = 1 + n * 7 + (1 + n * (1 + n * 2 + 1)) + 1 := by
  simp only [ryserCircuit, size_mulCircuit, size_finProdCircuit, size_finSumCircuit,
    size_subCircuit, size_constCircuit, size_varCircuit, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- The Ryser inner polynomial family belongs to `VP R`. -/
theorem ryserFamily_mem_VP : ryserFamily R ∈ VP R := by
  refine ⟨isPFamily_ryserFamily, ryserCircuit R, ?_, polynomial_ryserCircuit⟩
  have hpb : PolynomiallyBounded (fun n => 1 + n * 7 + (1 + n * (1 + n * 2 + 1)) + 1) :=
    (((PolynomiallyBounded.const 1).add
      (PolynomiallyBounded.id.mul (PolynomiallyBounded.const 7))).add
      ((PolynomiallyBounded.const 1).add
        (PolynomiallyBounded.id.mul
          (((PolynomiallyBounded.const 1).add
            (PolynomiallyBounded.id.mul (PolynomiallyBounded.const 2))).add
            (PolynomiallyBounded.const 1))))).add (PolynomiallyBounded.const 1)
  exact hpb.mono_of_le fun n => (size_ryserCircuit (R := R) n).le

/-- Summing `ryserPoly R n` over all `{0, 1}` assignments to the `n` indicator variables yields
the permanent of `genericMatrix R n`. -/
theorem booleanSum_ryserPoly (n : ℕ) :
    booleanSum n (ryserPoly R n) = (genericMatrix R n).permanent := by
  rw [Matrix.permanent_eq_ryser_bool, booleanSum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [ryserPoly, map_mul, map_prod, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_sub, map_mul, map_ofNat, map_one, projection_X]
    simp only [booleanAssignment, Fin.append_right, Sum.elim_inr]
    cases e j <;> norm_num
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, projection_X, projection_X]
    simp only [booleanAssignment, Fin.append_right, Fin.append_left, Sum.elim_inr, Sum.elim_inl]
    cases e j <;> simp [genericMatrix]

/-- **The permanent family belongs to `VNP`** over every commutative ring `R`
[Valiant1979Algebra; Bürgisser, Proposition 2.12][Burgisser2000]. -/
theorem permFamily_mem_VNP : permFamily R ∈ VNP R :=
  ⟨fun n => n, ryserPoly R, ryserFamily_mem_VP, fun n => (booleanSum_ryserPoly n).symm⟩

end RyserVNP

/-! #### Projection closure properties of the permanent and formula universality -/

section ProjectionClosure

variable {σ : Type*}

/-- A polynomial in `MvPolynomial σ K` is a projection substitution entry if it is either a
variable `X i` or a constant `C c`. -/
def IsSubstEntry (p : MvPolynomial σ K) : Prop :=
  ∃ s : σ ⊕ K, Sum.elim X (fun a => C a) s = p

namespace IsSubstEntry

theorem C (c : K) : IsSubstEntry (MvPolynomial.C c : MvPolynomial σ K) :=
  ⟨Sum.inr c, rfl⟩

theorem X (i : σ) : IsSubstEntry (MvPolynomial.X i : MvPolynomial σ K) :=
  ⟨Sum.inl i, rfl⟩

theorem zero : IsSubstEntry (0 : MvPolynomial σ K) :=
  ⟨Sum.inr 0, map_zero _⟩

theorem one : IsSubstEntry (1 : MvPolynomial σ K) :=
  ⟨Sum.inr 1, map_one _⟩

end IsSubstEntry

/-- A matrix over `MvPolynomial σ K` is a specialization of a generic matrix if every entry is a
variable `X i` or a constant `C c`. -/
def IsSubstMatrix {α β : Type*} (M : Matrix α β (MvPolynomial σ K)) : Prop :=
  ∀ i j, IsSubstEntry (M i j)

namespace IsSubstMatrix

theorem zero {α β : Type*} : IsSubstMatrix (0 : Matrix α β (MvPolynomial σ K)) :=
  fun _ _ => .zero

theorem one {α : Type*} [DecidableEq α] : IsSubstMatrix (1 : Matrix α α (MvPolynomial σ K)) :=
  fun i j => by
    rw [Matrix.one_apply]
    split_ifs <;> [exact .one; exact .zero]

theorem fromBlocks {α₁ α₂ β₁ β₂ : Type*}
    {A : Matrix α₁ β₁ (MvPolynomial σ K)} {B : Matrix α₁ β₂ (MvPolynomial σ K)}
    {C : Matrix α₂ β₁ (MvPolynomial σ K)} {D : Matrix α₂ β₂ (MvPolynomial σ K)}
    (hA : IsSubstMatrix A) (hB : IsSubstMatrix B) (hC : IsSubstMatrix C) (hD : IsSubstMatrix D) :
    IsSubstMatrix (Matrix.fromBlocks A B C D) := by
  rintro (i | i) (j | j)
  · exact hA i j
  · exact hB i j
  · exact hC i j
  · exact hD i j

theorem submatrix {α β α' β' : Type*} {M : Matrix α β (MvPolynomial σ K)}
    (hM : IsSubstMatrix M) (f : α' → α) (g : β' → β) :
    IsSubstMatrix (M.submatrix f g) :=
  fun i j => hM (f i) (g j)

theorem toBlocks₁₁ {α₁ α₂ β₁ β₂ : Type*} {M : Matrix (α₁ ⊕ α₂) (β₁ ⊕ β₂) (MvPolynomial σ K)}
    (hM : IsSubstMatrix M) : IsSubstMatrix M.toBlocks₁₁ :=
  fun i j => hM (.inl i) (.inl j)

theorem toBlocks₁₂ {α₁ α₂ β₁ β₂ : Type*} {M : Matrix (α₁ ⊕ α₂) (β₁ ⊕ β₂) (MvPolynomial σ K)}
    (hM : IsSubstMatrix M) : IsSubstMatrix M.toBlocks₁₂ :=
  fun i j => hM (.inl i) (.inr j)

theorem toBlocks₂₁ {α₁ α₂ β₁ β₂ : Type*} {M : Matrix (α₁ ⊕ α₂) (β₁ ⊕ β₂) (MvPolynomial σ K)}
    (hM : IsSubstMatrix M) : IsSubstMatrix M.toBlocks₂₁ :=
  fun i j => hM (.inr i) (.inl j)

theorem toBlocks₂₂ {α₁ α₂ β₁ β₂ : Type*} {M : Matrix (α₁ ⊕ α₂) (β₁ ⊕ β₂) (MvPolynomial σ K)}
    (hM : IsSubstMatrix M) : IsSubstMatrix M.toBlocks₂₂ :=
  fun i j => hM (.inr i) (.inr j)

theorem rootedMul {α β : Type*}
    {M₁ : Matrix (Unit ⊕ α) (Unit ⊕ α) (MvPolynomial σ K)}
    {M₂ : Matrix (Unit ⊕ β) (Unit ⊕ β) (MvPolynomial σ K)}
    (h₁ : IsSubstMatrix M₁) (h₂ : IsSubstMatrix M₂) :
    IsSubstMatrix (Matrix.rootedMul M₁ M₂) :=
  (h₁.fromBlocks .zero (IsSubstMatrix.one.fromBlocks .zero .zero .zero) h₂).submatrix _ _

theorem rootedAdd {α β : Type*}
    {M₁ : Matrix (Unit ⊕ α) (Unit ⊕ α) (MvPolynomial σ K)}
    {M₂ : Matrix (Unit ⊕ β) (Unit ⊕ β) (MvPolynomial σ K)}
    (h₁ : IsSubstMatrix M₁) (h₂ : IsSubstMatrix M₂) :
    IsSubstMatrix (Matrix.rootedAdd M₁ M₂) :=
  (h₁.fromBlocks (h₂.toBlocks₁₁.fromBlocks h₂.toBlocks₁₂ .zero .zero)
    (IsSubstMatrix.one.fromBlocks .zero .zero .zero)
    (IsSubstMatrix.one.fromBlocks .zero h₂.toBlocks₂₁ h₂.toBlocks₂₂)).submatrix _ _

/-- The permanent of any specialization matrix indexed by `α ≃ Fin m` is a projection of
`(genericMatrix K m).permanent`. -/
theorem isProjection_permanent {α : Type*} [Fintype α] [DecidableEq α]
    {M : Matrix α α (MvPolynomial σ K)} (hM : IsSubstMatrix M) {m : ℕ} (e : Fin m ≃ α) :
    IsProjection M.permanent (genericMatrix K m).permanent := by
  choose ρ hρ using hM
  refine ⟨fun idx =>
    let pq := finProdFinEquiv.symm idx
    ρ (e pq.1) (e pq.2), ?_⟩
  rw [projection_permanent_genericMatrix, ← M.permanent_submatrix_equiv e]
  exact congrArg Matrix.permanent (Matrix.ext fun i j => by simpa using hρ (e i) (e j))

end IsSubstMatrix

/-- A polynomial `P` is a projection of `(genericMatrix K m).permanent` if and only if it is the
permanent of an `m × m` specialization matrix. -/
theorem isProjection_permanent_iff_exists_substMatrix {P : MvPolynomial σ K} {m : ℕ} :
    IsProjection P (genericMatrix K m).permanent ↔
      ∃ M : Matrix (Fin m) (Fin m) (MvPolynomial σ K), IsSubstMatrix M ∧ M.permanent = P := by
  constructor
  · rintro ⟨ρ, rfl⟩
    refine ⟨Matrix.of fun i j => Sum.elim X (fun a => C a) (ρ (finProdFinEquiv (i, j))),
      fun i j => ⟨ρ (finProdFinEquiv (i, j)), rfl⟩,
      (projection_permanent_genericMatrix ρ).symm⟩
  · rintro ⟨M, hM, rfl⟩
    exact hM.isProjection_permanent (Equiv.refl _)

/-- Every constant polynomial `C c` is a projection of the `1 × 1` generic permanent. -/
theorem isProjection_permanent_C (c : K) :
    IsProjection (C c : MvPolynomial σ K) (genericMatrix K 1).permanent :=
  isProjection_permanent_iff_exists_substMatrix.mpr
    ⟨Matrix.of fun _ _ => C c, fun _ _ => .C c, Matrix.permanent_unique _⟩

/-- Every variable `X i` is a projection of the `1 × 1` generic permanent. -/
theorem isProjection_permanent_X (i : σ) :
    IsProjection (X i : MvPolynomial σ K) (genericMatrix K 1).permanent :=
  isProjection_permanent_iff_exists_substMatrix.mpr
    ⟨Matrix.of fun _ _ => X i, fun _ _ => .X i, Matrix.permanent_unique _⟩

/-- The constant polynomial `1` is a projection of the `m × m` generic permanent for every `m`. -/
theorem isProjection_permanent_one (m : ℕ) :
    IsProjection (1 : MvPolynomial σ K) (genericMatrix K m).permanent :=
  isProjection_permanent_iff_exists_substMatrix.mpr ⟨1, .one, Matrix.permanent_one⟩

/-- **Multiplicative closure of permanent projections**: if `P` is a projection of the `m × m`
generic permanent and `Q` is a projection of the `k × k` generic permanent, then `P * Q` is a
projection of the `(m + k) × (m + k)` generic permanent. -/
theorem IsProjection.permanent_mul {P Q : MvPolynomial σ K} {m k : ℕ}
    (hP : IsProjection P (genericMatrix K m).permanent)
    (hQ : IsProjection Q (genericMatrix K k).permanent) :
    IsProjection (P * Q) (genericMatrix K (m + k)).permanent := by
  obtain ⟨M₁, hM₁, rfl⟩ := isProjection_permanent_iff_exists_substMatrix.mp hP
  obtain ⟨M₂, hM₂, rfl⟩ := isProjection_permanent_iff_exists_substMatrix.mp hQ
  rw [← Matrix.permanent_fromBlocks_zero M₁ M₂]
  exact (hM₁.fromBlocks .zero .zero hM₂).isProjection_permanent finSumFinEquiv.symm

/-- **Monotonicity of permanent projections in the matrix dimension**: if `m ≤ k` and `P` is a
projection of `(genericMatrix K m).permanent`, then `P` is a projection of
`(genericMatrix K k).permanent`. -/
theorem isProjection_permanent_mono {P : MvPolynomial σ K} {m k : ℕ} (hmk : m ≤ k)
    (hP : IsProjection P (genericMatrix K m).permanent) :
    IsProjection P (genericMatrix K k).permanent := by
  have hmul := hP.permanent_mul (isProjection_permanent_one (K := K) (σ := σ) (k - m))
  rwa [mul_one, Nat.add_sub_of_le hmk] at hmul

/-- Finite products of permanent projections are permanent projections of the sum of dimensions. -/
theorem isProjection_permanent_finset_prod {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial σ K) (d : ι → ℕ)
    (hf : ∀ i ∈ s, IsProjection (f i) (genericMatrix K (d i)).permanent) :
    IsProjection (∏ i ∈ s, f i) (genericMatrix K (∑ i ∈ s, d i)).permanent := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact isProjection_permanent_one (K := K) (σ := σ) 0
  | cons a s has ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    exact (hf a (Finset.mem_cons_self a s)).permanent_mul
      (ih fun i hi => hf i (Finset.mem_cons_of_mem hi))

/-- A polynomial `P` has a *rooted permanent representation* of internal dimension `m` if it is
the permanent of a `(1 + m) × (1 + m)` specialization matrix `M` on `Unit ⊕ Fin m` whose internal
block `M.toBlocks₂₂` has permanent `1`. -/
def IsRootedPermProjection (m : ℕ) (P : MvPolynomial σ K) : Prop :=
  ∃ M : Matrix (Unit ⊕ Fin m) (Unit ⊕ Fin m) (MvPolynomial σ K),
    IsSubstMatrix M ∧ M.toBlocks₂₂.permanent = 1 ∧ M.permanent = P

namespace IsRootedPermProjection

/-- A rooted permanent representation of internal dimension `m` gives a projection of the
`(m + 1) × (m + 1)` generic permanent. -/
theorem to_isProjection_permanent {m : ℕ} {P : MvPolynomial σ K}
    (h : IsRootedPermProjection m P) :
    IsProjection P (genericMatrix K (m + 1)).permanent := by
  obtain ⟨M, hM, -, rfl⟩ := h
  have e : Fin (m + 1) ≃ Unit ⊕ Fin m :=
    (finCongr (Nat.add_comm m 1)).trans
      (finSumFinEquiv.symm.trans (Equiv.sumCongr finOneEquiv (Equiv.refl _)))
  exact hM.isProjection_permanent e

/-- Every single-entry substitution `P` (a variable or constant) has a rooted permanent
representation of internal dimension `0`. -/
theorem of_isSubstEntry {P : MvPolynomial σ K} (hP : IsSubstEntry P) :
    IsRootedPermProjection 0 P := by
  refine ⟨Matrix.fromBlocks (Matrix.of fun _ _ => P) 0 0 0,
    IsSubstMatrix.fromBlocks (fun _ _ => hP) .zero .zero .zero,
    Matrix.permanent_isEmpty, ?_⟩
  rw [Matrix.permanent_fromBlocks_zero, Matrix.permanent_unique, Matrix.permanent_isEmpty, mul_one]
  rfl

/-- Every constant `C c` has a rooted permanent representation of internal dimension `0`. -/
theorem C (c : K) : IsRootedPermProjection 0 (MvPolynomial.C c : MvPolynomial σ K) :=
  .of_isSubstEntry (.C c)

/-- Every variable `X i` has a rooted permanent representation of internal dimension `0`. -/
theorem X (i : σ) : IsRootedPermProjection 0 (MvPolynomial.X i : MvPolynomial σ K) :=
  .of_isSubstEntry (.X i)

/-- Equivalence `Fin (m₁ + 1 + m₂) ≃ Fin m₁ ⊕ (Unit ⊕ Fin m₂)` used to flatten internal blocks of
rooted permanent representations. -/
def innerEquiv (m₁ m₂ : ℕ) : Fin (m₁ + 1 + m₂) ≃ Fin m₁ ⊕ (Unit ⊕ Fin m₂) :=
  (finCongr (Nat.add_assoc m₁ 1 m₂)).trans
    (finSumFinEquiv.symm.trans
      (Equiv.sumCongr (Equiv.refl _)
        (finSumFinEquiv.symm.trans (Equiv.sumCongr finOneEquiv (Equiv.refl _)))))

/-- Equivalence `Unit ⊕ Fin (m₁ + 1 + m₂) ≃ Unit ⊕ (Fin m₁ ⊕ (Unit ⊕ Fin m₂))`. -/
def outerEquiv (m₁ m₂ : ℕ) :
    Unit ⊕ Fin (m₁ + 1 + m₂) ≃ Unit ⊕ (Fin m₁ ⊕ (Unit ⊕ Fin m₂)) :=
  Equiv.sumCongr (Equiv.refl Unit) (innerEquiv m₁ m₂)

/-- **Additive closure of rooted permanent representations**: if `P` and `Q` have rooted permanent
representations of internal dimensions `m₁` and `m₂`, then `P + Q` has one of internal dimension
`m₁ + 1 + m₂`. -/
theorem add {m₁ m₂ : ℕ} {P Q : MvPolynomial σ K}
    (hP : IsRootedPermProjection m₁ P) (hQ : IsRootedPermProjection m₂ Q) :
    IsRootedPermProjection (m₁ + 1 + m₂) (P + Q) := by
  obtain ⟨M₁, hM₁, hU₁, rfl⟩ := hP
  obtain ⟨M₂, hM₂, hU₂, rfl⟩ := hQ
  refine ⟨(Matrix.rootedAdd M₁ M₂).submatrix (outerEquiv m₁ m₂) (outerEquiv m₁ m₂),
    (hM₁.rootedAdd hM₂).submatrix _ _, ?_, ?_⟩
  · have hblk : ((Matrix.rootedAdd M₁ M₂).submatrix
        (outerEquiv m₁ m₂) (outerEquiv m₁ m₂)).toBlocks₂₂ =
        (Matrix.rootedAdd M₁ M₂).toBlocks₂₂.submatrix (innerEquiv m₁ m₂) (innerEquiv m₁ m₂) := rfl
    rw [hblk, Matrix.permanent_submatrix_equiv, Matrix.permanent_toBlocks₂₂_rootedAdd M₁ M₂ hU₁ hU₂]
  · rw [Matrix.permanent_submatrix_equiv, Matrix.permanent_rootedAdd M₁ M₂ hU₁ hU₂]

/-- **Multiplicative closure of rooted permanent representations**: if `P` and `Q` have rooted
permanent representations of internal dimensions `m₁` and `m₂`, then `P * Q` has one of internal
dimension `m₁ + 1 + m₂`. -/
theorem mul {m₁ m₂ : ℕ} {P Q : MvPolynomial σ K}
    (hP : IsRootedPermProjection m₁ P) (hQ : IsRootedPermProjection m₂ Q) :
    IsRootedPermProjection (m₁ + 1 + m₂) (P * Q) := by
  obtain ⟨M₁, hM₁, hU₁, rfl⟩ := hP
  obtain ⟨M₂, hM₂, hU₂, rfl⟩ := hQ
  refine ⟨(Matrix.rootedMul M₁ M₂).submatrix (outerEquiv m₁ m₂) (outerEquiv m₁ m₂),
    (hM₁.rootedMul hM₂).submatrix _ _, ?_, ?_⟩
  · have hblk : ((Matrix.rootedMul M₁ M₂).submatrix
        (outerEquiv m₁ m₂) (outerEquiv m₁ m₂)).toBlocks₂₂ =
        (Matrix.rootedMul M₁ M₂).toBlocks₂₂.submatrix (innerEquiv m₁ m₂) (innerEquiv m₁ m₂) := rfl
    rw [hblk, Matrix.permanent_submatrix_equiv, Matrix.permanent_toBlocks₂₂_rootedMul M₁ M₂ hU₁ hU₂]
  · rw [Matrix.permanent_submatrix_equiv, Matrix.permanent_rootedMul M₁ M₂]

end IsRootedPermProjection

/-- Every arithmetic formula `F` computes a polynomial with a rooted permanent representation of
internal dimension at most `F.size`. -/
theorem _root_.Cslib.Circuits.Formula.exists_isRootedPermProjection
    (F : Formula (arithSignature K) n) :
    ∃ m ≤ F.size, IsRootedPermProjection m (F.eval (arithInterpretationWith K C) X) := by
  induction F with
  | input i =>
    exact ⟨0, le_rfl, .X i⟩
  | gate op args ih =>
    cases op with
    | const c =>
      exact ⟨0, Nat.zero_le _, .C c⟩
    | add =>
      obtain ⟨m₀, hm₀, h₀⟩ := ih 0
      obtain ⟨m₁, hm₁, h₁⟩ := ih 1
      refine ⟨m₀ + 1 + m₁, ?_, h₀.add h₁⟩
      rw [Formula.size_gate]
      change m₀ + 1 + m₁ ≤ (∑ j : Fin 2, (args j).size) + 1
      rw [Fin.sum_univ_two]
      omega
    | mul =>
      obtain ⟨m₀, hm₀, h₀⟩ := ih 0
      obtain ⟨m₁, hm₁, h₁⟩ := ih 1
      refine ⟨m₀ + 1 + m₁, ?_, h₀.mul h₁⟩
      rw [Formula.size_gate]
      change m₀ + 1 + m₁ ≤ (∑ j : Fin 2, (args j).size) + 1
      rw [Fin.sum_univ_two]
      omega

/-- **Valiant's formula universality for the permanent** [Valiant1979Algebra; Bürgisser,
Lemma 2.9][Burgisser2000]: the polynomial computed by any arithmetic formula `F` of size `s` is a
projection of the `(s + 1) × (s + 1)` generic permanent. -/
theorem _root_.Cslib.Circuits.Formula.isProjection_permanent
    (F : Formula (arithSignature K) n) :
    IsProjection (F.eval (arithInterpretationWith K C) X)
      (genericMatrix K (F.size + 1)).permanent := by
  obtain ⟨m, hm, hroot⟩ := F.exists_isRootedPermProjection
  exact isProjection_permanent_mono (Nat.add_le_add_right hm 1) hroot.to_isProjection_permanent

/-- The formal polynomial `(F.toCircuit).polynomial 0` of any arithmetic formula `F` is a
projection of `(genericMatrix K (F.size + 1)).permanent`. -/
theorem _root_.Cslib.Circuits.Formula.isProjection_permanent_toCircuit
    (F : Formula (arithSignature K) n) :
    IsProjection (F.toCircuit.polynomial 0) (genericMatrix K (F.size + 1)).permanent := by
  simpa [Circuit.polynomial] using F.isProjection_permanent

end ProjectionClosure

end Cslib.Circuits.Arithmetic
