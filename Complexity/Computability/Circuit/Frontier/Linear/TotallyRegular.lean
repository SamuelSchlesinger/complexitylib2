/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Totally regular matrices and Cauchy matrices

A matrix is *totally regular* when every square submatrix, on distinct rows and distinct
columns, is nonsingular. For the linear map `x ↦ M x` of a totally regular matrix, no small set
of outputs is blind to a large set of inputs: a vector supported on a set `C` of columns that
`M` maps to zero on a set `R` of at least `|C|` rows is zero
(`Matrix.TotallyRegular.eq_zero_of_mulVec_eq_zero`).

*Cauchy matrices* `M i j = 1 / (x i - y j)`, with distinct `x i`, distinct `y j` and
`x i ≠ y j`, are totally regular: every square submatrix is again a Cauchy matrix, and a square
Cauchy matrix is nonsingular (`Matrix.det_cauchy_ne_zero`). The proof avoids Cauchy's
determinant formula: a vector `v` in the kernel gives a polynomial of degree less than `k`, the
Lagrange interpolant of `v j / w j` at the nodes `y j` (where the `w j` are the nodal weights),
that vanishes at the `k` points `x i`.

The explicit family `1 / (i - (N + j))` for `0 ≤ i, j < N` is totally regular over every field
of characteristic zero (`Matrix.totallyRegular_cauchyNat`) and over `ZMod q` for every prime
`q ≥ 2 N` (`Matrix.totallyRegular_cauchyNat_zmod`).

## Main definitions

* `Matrix.TotallyRegular`: every square submatrix is nonsingular.
* `Matrix.cauchy`: the Cauchy matrix with nodes `x` and `y`.
* `Matrix.cauchyNat`: the Cauchy matrix with nodes `0, ..., N - 1` and `N, ..., 2 N - 1`.

## Main results

* `Matrix.TotallyRegular.eq_zero_of_mulVec_eq_zero`: square submatrices act injectively.
* `Matrix.TotallyRegular.submatrix`, `Matrix.TotallyRegular.transpose`: closure properties.
* `Matrix.det_cauchy_ne_zero`: square Cauchy matrices are nonsingular.
* `Matrix.totallyRegular_cauchy`: Cauchy matrices are totally regular.
-/

@[expose] public section

namespace Matrix

variable {m n m' n' R : Type*}

section CommRing

variable [CommRing R]

/-- A matrix is *totally regular* when every square submatrix, on distinct rows and distinct
columns, is nonsingular. -/
def TotallyRegular (M : Matrix m n R) : Prop :=
  ∀ (k : ℕ) (r : Fin k → m) (c : Fin k → n), Function.Injective r → Function.Injective c →
    (M.submatrix r c).det ≠ 0

namespace TotallyRegular

variable {M : Matrix m n R}

/-- A submatrix of a totally regular matrix, on distinct rows and distinct columns, is totally
regular. -/
theorem submatrix (hM : M.TotallyRegular) {r : m' → m} {c : n' → n}
    (hr : Function.Injective r) (hc : Function.Injective c) : (M.submatrix r c).TotallyRegular :=
  fun k r' c' hr' hc' => by
    simpa only [submatrix_submatrix] using hM k (r ∘ r') (c ∘ c') (hr.comp hr') (hc.comp hc')

/-- The transpose of a totally regular matrix is totally regular. -/
theorem transpose (hM : M.TotallyRegular) : Mᵀ.TotallyRegular := fun k r c hr hc => by
  rw [← transpose_submatrix, det_transpose]
  exact hM k c r hc hr

/-- Every entry of a totally regular matrix is nonzero: it is a `1 × 1` submatrix. -/
theorem apply_ne_zero (hM : M.TotallyRegular) (i : m) (j : n) : M i j ≠ 0 := by
  simpa [det_unique] using hM 1 (fun _ => i) (fun _ => j)
    (Function.injective_of_subsingleton _) (Function.injective_of_subsingleton _)

/-- **Square submatrices act injectively.** If `M` is totally regular, `v` is supported on a set
`C` of columns, and `M v` vanishes on a set `R` of rows with `|C| ≤ |R|`, then `v = 0`. -/
theorem eq_zero_of_mulVec_eq_zero [Fintype n] [NoZeroDivisors R] (hM : M.TotallyRegular)
    {rows : Finset m} {cols : Finset n} (hcard : cols.card ≤ rows.card) {v : n → R}
    (hv : ∀ j ∉ cols, v j = 0) (hMv : ∀ i ∈ rows, (M *ᵥ v) i = 0) : v = 0 := by
  classical
  obtain ⟨rows', hrows', hcard'⟩ := Finset.exists_subset_card_eq hcard
  set k := cols.card
  let r : Fin k → m := fun i => rows'.equivFin.symm (Fin.cast hcard'.symm i)
  let c : Fin k → n := fun j => cols.equivFin.symm j
  have hr : Function.Injective r := fun i i' h => by
    simpa [r, Fin.cast_inj] using rows'.equivFin.symm.injective (Subtype.ext h)
  have hc : Function.Injective c := fun j j' h => cols.equivFin.symm.injective (Subtype.ext h)
  -- On the rows `r`, the vector `M v` is the submatrix on `r` and `c` applied to `v ∘ c`.
  have hsum : ∀ i : m, (M *ᵥ v) i = ∑ j : Fin k, M i (c j) * v (c j) := by
    intro i
    simp only [mulVec, dotProduct]
    rw [← Finset.sum_subset (Finset.subset_univ cols) fun j _ hj => by simp [hv j hj],
      ← Finset.sum_coe_sort cols]
    exact (Equiv.sum_comp cols.equivFin.symm fun j : cols => M i j * v j).symm
  have hzero : M.submatrix r c *ᵥ (v ∘ c) = 0 := by
    funext i
    simp only [mulVec, dotProduct, submatrix_apply, Function.comp_apply, Pi.zero_apply]
    rw [← hsum]
    exact hMv _ (hrows' (rows'.equivFin.symm _).2)
  have hvc := Matrix.eq_zero_of_mulVec_eq_zero (hM k r c hr hc) hzero
  funext j
  by_cases hj : j ∈ cols
  · simpa [c] using congrFun hvc (cols.equivFin ⟨j, hj⟩)
  · exact hv j hj

end TotallyRegular

end CommRing

/-! ### Cauchy matrices -/

section Cauchy

variable {F : Type*} [Field F]

/-- The *Cauchy matrix* with nodes `x` and `y`: `M i j = 1 / (x i - y j)`. -/
def cauchy (x : m → F) (y : n → F) : Matrix m n F :=
  of fun i j => (x i - y j)⁻¹

@[simp] theorem cauchy_apply (x : m → F) (y : n → F) (i : m) (j : n) :
    cauchy x y i j = (x i - y j)⁻¹ :=
  rfl

/-- A submatrix of a Cauchy matrix is the Cauchy matrix of the restricted nodes. -/
@[simp] theorem submatrix_cauchy (x : m → F) (y : n → F) (r : m' → m) (c : n' → n) :
    (cauchy x y).submatrix r c = cauchy (x ∘ r) (y ∘ c) :=
  rfl

/-- **Square Cauchy matrices are nonsingular.** If `∑ j, v j / (x i - y j) = 0` for every `i`,
then the polynomial interpolating `v j / w j` at the nodes `y j`, where the `w j` are the nodal
weights, vanishes at the `k` points `x i`. Its degree is less than `k`, so it is zero, and so is
`v`. -/
theorem det_cauchy_ne_zero [Fintype n] [DecidableEq n] {x y : n → F}
    (hx : Function.Injective x) (hy : Function.Injective y) (hxy : ∀ i j, x i ≠ y j) :
    (cauchy x y).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  have hweight : ∀ j, Lagrange.nodalWeight Finset.univ y j ≠ 0 := fun j =>
    Lagrange.nodalWeight_ne_zero hy.injOn (Finset.mem_univ j)
  let w : n → F := fun j => (Lagrange.nodalWeight Finset.univ y j)⁻¹ * v j
  have hP : Lagrange.interpolate Finset.univ y w = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ hx.injOn
      (Lagrange.degree_interpolate_lt w hy.injOn) fun i _ => ?_
    rw [Lagrange.eval_interpolate_not_at_node w fun j _ => hxy i j]
    have hsum : ∑ j, Lagrange.nodalWeight Finset.univ y j * (x i - y j)⁻¹ * w j =
        (cauchy x y *ᵥ v) i := by
      simp only [mulVec, dotProduct, cauchy_apply, w]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp [hweight j]
    rw [hsum, hv, Pi.zero_apply, mul_zero]
  refine hv0 (funext fun j => ?_)
  have h := Lagrange.eval_interpolate_at_node w hy.injOn (Finset.mem_univ j)
  rw [hP, Polynomial.eval_zero] at h
  simpa [w, hweight j] using h.symm

/-- **Cauchy matrices are totally regular**: every square submatrix is again a square Cauchy
matrix. -/
theorem totallyRegular_cauchy {x : m → F} {y : n → F} (hx : Function.Injective x)
    (hy : Function.Injective y) (hxy : ∀ i j, x i ≠ y j) : (cauchy x y).TotallyRegular :=
  fun _ r c hr hc => by
    rw [submatrix_cauchy]
    exact det_cauchy_ne_zero (hx.comp hr) (hy.comp hc) fun i j => hxy (r i) (c j)

variable (F) in
/-- The explicit `N × N` Cauchy matrix `M i j = 1 / (i - (N + j))`, with nodes `0, ..., N - 1`
and `N, ..., 2 N - 1`. -/
def cauchyNat (N : ℕ) : Matrix (Fin N) (Fin N) F :=
  cauchy (fun i : Fin N => ((i : ℕ) : F)) fun j : Fin N => ((N + j : ℕ) : F)

/-- **The explicit Cauchy matrices are totally regular** over fields of characteristic zero. -/
theorem totallyRegular_cauchyNat [CharZero F] (N : ℕ) : (cauchyNat F N).TotallyRegular :=
  totallyRegular_cauchy (fun i i' h => Fin.ext (by exact_mod_cast h))
    (fun j j' h => Fin.ext (Nat.add_left_cancel (by exact_mod_cast h)))
    fun i j h => by
      have : (i : ℕ) = N + j := by exact_mod_cast h
      omega

/-- **The explicit Cauchy matrices are totally regular** over `ZMod q`, for every prime
`q ≥ 2 N`. -/
theorem totallyRegular_cauchyNat_zmod {q : ℕ} [Fact q.Prime] {N : ℕ} (hq : 2 * N ≤ q) :
    (cauchyNat (ZMod q) N).TotallyRegular := by
  have hcast : ∀ a b : ℕ, a < q → b < q → ((a : ZMod q) = b ↔ a = b) := fun a b ha hb => by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  refine totallyRegular_cauchy (fun i i' h => Fin.ext ?_) (fun j j' h => Fin.ext ?_)
    fun i j h => ?_
  · exact (hcast _ _ (by omega) (by omega)).mp h
  · have := (hcast _ _ (by omega) (by omega)).mp h
    omega
  · have := (hcast _ _ (by omega) (by omega)).mp h
    omega

end Cauchy

end Matrix
