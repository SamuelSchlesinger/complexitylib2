/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.Classes.Promise.Basic
public import Cslib.Probability.PMF
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Learning With Errors and Regev's Worst-Case-to-Average-Case Quantum Reduction

This module formalizes full-rank Euclidean lattices, successive minima (`λ₁` and `λ_n`), the dual
lattice and Banaszczyk's transference bounds, the worst-case lattice problems `GapSVP` and `SIVP`,
the continuous and rounded discrete Gaussian noise distributions, the Search-LWE problem under
Regev's smoothing condition `α q > 2 √n`, and Regev's iterative quantum reduction [Regev2009]
from worst-case `SIVP` and `GapSVP` to average-case `SearchLWE`.

## Main definitions

* `Cslib.Crypto.LatticeBasis`: a full-rank `n`-dimensional lattice basis in `ℝ^n`.
* `Cslib.Crypto.latticeSpan`, `Cslib.Crypto.dualBasis`: the generated lattice and its dual basis
  `(B⁻¹)ᵀ`.
* `Cslib.Crypto.lambda1`, `Cslib.Crypto.lambdaN`: the shortest nonzero vector length `λ₁(L)` and
  the `n`-th successive minimum `λ_n(L)`.
* `Cslib.Crypto.GapSVP`, `Cslib.Crypto.SIVPWitness`, `Cslib.Crypto.SIVPSolver`: worst-case promise
  and search problems on lattices.
* `Cslib.Crypto.gaussianPdf`, `Cslib.Crypto.discreteGaussianProb`,
  `Cslib.Crypto.discreteGaussianPMF`: the 1D Gaussian density and the rounded discrete Gaussian
  noise distribution on `ZMod q`.
* `Cslib.Crypto.RegevParameters`: Regev's parameter regime `0 < n`, `2 ≤ q`, `0 < α < 1`, and
  `2 * √n < α * q`.
* `Cslib.Crypto.LWESample`, `Cslib.Crypto.lweSamplePMF`, `Cslib.Crypto.SearchLWEOracle`: the LWE
  sample distribution and search oracle.
* `Cslib.Crypto.DualBDDInstance`, `Cslib.Crypto.DiscreteGaussianSuperposition`,
  `Cslib.Crypto.RegevQuantumStepOracle`: bounded distance decoding on the dual lattice, discrete
  Gaussian superposition states, and the iterative quantum width-reduction step.

## Main results

* `Cslib.Crypto.lambda1_pos`, `Cslib.Crypto.lambda1_le_lambdaN`: positivity and ordering of the
  successive minima for every full-rank lattice.
* `Cslib.Crypto.one_le_lambda1_mul_lambdaN_dualBasis`,
  `Cslib.Crypto.banaszczyk_transference_bounds`: primal-dual transference bounds.
* `Cslib.Crypto.regevParameters_explicit`, `Cslib.Crypto.regevParameters_all_pos`: explicit
  polynomial moduli `q = n ^ 2 + 5` and inverse-polynomial noise rates satisfying
  `RegevParameters`.
* `Cslib.Crypto.dualBDD_innerProduct_eq`, `Cslib.Crypto.dualBDD_noise_le`,
  `Cslib.Crypto.solveDualBDDModQ_eq_secretCoords`: Regev's classical reduction from bounded
  distance decoding on `L*` at radius `α q / (√2 r)` to `SearchLWE`.
* `Cslib.Crypto.regevShrinkFactor_lt_one`, `Cslib.Crypto.terminalGaussianState_width_le`:
  iterating the quantum step under `2 * √n < α * q` shrinks the Gaussian width below the stopping
  threshold `2 √n / (α λ₁(L*))`.
* `Cslib.Crypto.regev_lwe_to_sivp`, `Cslib.Crypto.regev_lwe_to_gapsvp`,
  `Cslib.Crypto.regev_lwe_to_sivp_gapsvp`: Regev's worst-case-to-average-case reduction yielding
  both worst-case `SIVP` and worst-case `GapSVP` with approximation factor `2 n / α` (and
  `O(n log n / α)`).

## References

* [O. Regev, *On lattices, learning with errors, random linear codes, and cryptography*][Regev2009]
* [W. Banaszczyk, *New bounds in some transference theorems in the geometry of
  numbers*][Banaszczyk1993]
-/

@[expose] public section

namespace Cslib.Crypto

open Cslib.Complexity
open scoped Matrix BigOperators ENNReal

noncomputable section

/-! ### Part 1: Euclidean Norms, Full-Rank Lattices, Successive Minima, `GapSVP`, and `SIVP` -/

/-- The Euclidean (`ℓ₂`) norm of a vector in `ℝ^n`. -/
def euclideanNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, (v i) ^ 2)

/-- The Euclidean norm is nonnegative. -/
theorem euclideanNorm_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ euclideanNorm v :=
  Real.sqrt_nonneg _

/-- The square of the Euclidean norm is the sum of squared coordinates. -/
theorem euclideanNorm_sq {n : ℕ} (v : Fin n → ℝ) :
    (euclideanNorm v) ^ 2 = ∑ i : Fin n, (v i) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Each coordinate is bounded in absolute value by the Euclidean norm. -/
theorem abs_apply_le_euclideanNorm {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |v i| ≤ euclideanNorm v := by
  rw [← Real.sqrt_sq_eq_abs, euclideanNorm]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))

/-- Positive homogeneity of the Euclidean norm for nonnegative scalars. -/
theorem euclideanNorm_smul {n : ℕ} {c : ℝ} (hc : 0 ≤ c) (v : Fin n → ℝ) :
    euclideanNorm (fun i => c * v i) = c * euclideanNorm v := by
  unfold euclideanNorm
  have h : (∑ i : Fin n, (c * v i) ^ 2) = c ^ 2 * ∑ i : Fin n, (v i) ^ 2 := by
    calc
      ∑ i : Fin n, (c * v i) ^ 2 = ∑ i : Fin n, c ^ 2 * (v i) ^ 2 :=
        Finset.sum_congr rfl fun i _ => mul_pow c (v i) 2
      _ = c ^ 2 * ∑ i : Fin n, (v i) ^ 2 := (Finset.mul_sum _ _ _).symm
  rw [h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- The Euclidean norm of a scaled standard basis vector is the scale factor. -/
theorem euclideanNorm_single {n : ℕ} {c : ℝ} (hc : 0 ≤ c) (i : Fin n) :
    euclideanNorm (fun j => if j = i then c else 0) = c := by
  unfold euclideanNorm
  have h : (∑ j : Fin n, (if j = i then c else 0) ^ 2) = c ^ 2 := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  rw [h, Real.sqrt_sq hc]

/-- **Cauchy–Schwarz inequality** for the dot product and Euclidean norm on `ℝ^n`. -/
theorem abs_dotProduct_le_euclideanNorm_mul {n : ℕ} (v w : Fin n → ℝ) :
    |v ⬝ᵥ w| ≤ euclideanNorm v * euclideanNorm w := by
  calc
    |v ⬝ᵥ w| = |∑ i : Fin n, v i * w i| := rfl
    _ ≤ ∑ i : Fin n, |v i * w i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, |v i| * |w i| :=
      Finset.sum_congr rfl fun i _ => abs_mul (v i) (w i)
    _ ≤ Real.sqrt (∑ i : Fin n, |v i| ^ 2) * Real.sqrt (∑ i : Fin n, |w i| ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => |v i|) (fun i => |w i|)
    _ = euclideanNorm v * euclideanNorm w := by
      simp only [euclideanNorm, sq_abs]

/-- Every nonzero integer vector in `ℤ^n` has Euclidean norm at least `1`. -/
theorem one_le_euclideanNorm_intCast {n : ℕ} {z : Fin n → ℤ} (hz : z ≠ 0) :
    1 ≤ euclideanNorm (fun i => (z i : ℝ)) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
  have h1 : (1 : ℝ) ≤ |(z i : ℝ)| := by
    have h1' : (1 : ℤ) ≤ |z i| := Int.one_le_abs hi
    exact_mod_cast h1'
  exact h1.trans (abs_apply_le_euclideanNorm (fun j => (z j : ℝ)) i)

/-- Strictly positive entrywise norm bound `1 + ∑ i, ∑ j, |M i j|` for a matrix `M`. -/
def matrixEntrySum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  1 + ∑ i : Fin n, ∑ j : Fin n, |M i j|

theorem matrixEntrySum_pos {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    0 < matrixEntrySum M := by
  unfold matrixEntrySum
  have h : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, |M i j| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  linarith

theorem abs_mulVec_apply_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (i : Fin n) :
    |(M.mulVec v) i| ≤ matrixEntrySum M * euclideanNorm v := by
  have hrow : |(M.mulVec v) i| ≤ (∑ j : Fin n, |M i j|) * euclideanNorm v := by
    calc
      |(M.mulVec v) i| = |∑ j : Fin n, M i j * v j| := rfl
      _ ≤ ∑ j : Fin n, |M i j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |M i j| * |v j| :=
        Finset.sum_congr rfl fun j _ => abs_mul (M i j) (v j)
      _ ≤ ∑ j : Fin n, |M i j| * euclideanNorm v :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (abs_apply_le_euclideanNorm v j) (abs_nonneg _)
      _ = (∑ j : Fin n, |M i j|) * euclideanNorm v := (Finset.sum_mul _ _ _).symm
  have hle : ∑ j : Fin n, |M i j| ≤ matrixEntrySum M := by
    unfold matrixEntrySum
    have hsingle : ∑ j : Fin n, |M i j| ≤ ∑ i' : Fin n, ∑ j : Fin n, |M i' j| :=
      Finset.single_le_sum (f := fun i' => ∑ j : Fin n, |M i' j|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    linarith
  exact hrow.trans (mul_le_mul_of_nonneg_right hle (euclideanNorm_nonneg v))

theorem inv_matrixEntrySum_le_mulVec_intCast {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.det ≠ 0) {z : Fin n → ℤ} (hz : z ≠ 0) :
    (matrixEntrySum M⁻¹)⁻¹ ≤ euclideanNorm (M.mulVec (fun j => (z j : ℝ))) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
  let zR : Fin n → ℝ := fun j => (z j : ℝ)
  have hzR : zR = M⁻¹.mulVec (M.mulVec zR) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hM),
      Matrix.one_mulVec]
  have h1 : (1 : ℝ) ≤ |zR i| := by
    have h1' : (1 : ℤ) ≤ |z i| := Int.one_le_abs hi
    simpa only [zR, Int.cast_abs, Int.cast_one] using (Int.cast_le (R := ℝ)).mpr h1'
  have h2 : |zR i| ≤ matrixEntrySum M⁻¹ * euclideanNorm (M.mulVec zR) := by
    rw [congr_fun hzR i]
    exact abs_mulVec_apply_le M⁻¹ (M.mulVec zR) i
  exact (inv_le_iff_one_le_mul₀' (matrixEntrySum_pos M⁻¹)).mpr (h1.trans h2)

/-- A full-rank `n`-dimensional lattice basis in `ℝ^n`, represented by a nonsingular column basis
matrix `B : Matrix (Fin n) (Fin n) ℝ`. -/
@[ext]
structure LatticeBasis (n : ℕ) where
  /-- The nonsingular basis matrix whose columns generate the lattice. -/
  matrix : Matrix (Fin n) (Fin n) ℝ
  /-- Full-rank condition: the basis matrix has nonzero determinant. -/
  det_ne_zero : matrix.det ≠ 0

/-- The discrete subgroup `L(B) = { B z | z ∈ ℤ^n } ⊆ ℝ^n` generated by a lattice basis `B`. -/
def latticeSpan {n : ℕ} (B : LatticeBasis n) : Set (Fin n → ℝ) :=
  Set.range (fun z : Fin n → ℤ => B.matrix.mulVec (fun i => (z i : ℝ)))

/-- The dual lattice basis `B* = (B⁻¹)ᵀ`, generating `L* = { u ∈ ℝ^n | ∀ v ∈ L, ⟨u, v⟩ ∈ ℤ }`. -/
def dualBasis {n : ℕ} (B : LatticeBasis n) : LatticeBasis n where
  matrix := (B.matrix⁻¹)ᵀ
  det_ne_zero := by
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact inv_ne_zero B.det_ne_zero

/-- Taking the dual lattice basis twice recovers the original basis. -/
@[simp]
theorem dualBasis_dualBasis {n : ℕ} (B : LatticeBasis n) :
    dualBasis (dualBasis B) = B := by
  ext i j
  have hu : IsUnit B.matrix.det := isUnit_iff_ne_zero.mpr B.det_ne_zero
  change (((B.matrix⁻¹)ᵀ⁻¹)ᵀ) i j = B.matrix i j
  rw [← Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
    Matrix.nonsing_inv_nonsing_inv _ hu]

/-- Primal-dual inner product duality: `(B v) ⬝ᵥ (B* w) = v ⬝ᵥ w`. -/
theorem mulVec_dotProduct_dualBasis {n : ℕ} (B : LatticeBasis n) (v w : Fin n → ℝ) :
    (B.matrix.mulVec v) ⬝ᵥ ((dualBasis B).matrix.mulVec w) = v ⬝ᵥ w := by
  have hu : IsUnit B.matrix.det := isUnit_iff_ne_zero.mpr B.det_ne_zero
  change (B.matrix.mulVec v) ⬝ᵥ ((B.matrix⁻¹)ᵀ.mulVec w) = v ⬝ᵥ w
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

/-- The set of Euclidean norms of nonzero lattice vectors in `L(B)`. -/
def nonzeroLatticeNorms {n : ℕ} (B : LatticeBasis n) : Set ℝ :=
  { r : ℝ | ∃ z : Fin n → ℤ, z ≠ 0 ∧ r = euclideanNorm (B.matrix.mulVec (fun i => (z i : ℝ))) }

/-- The first successive minimum `λ₁(B)`: the infimum of Euclidean norms of nonzero vectors in
`L(B)`. -/
def lambda1 {n : ℕ} (B : LatticeBasis n) : ℝ :=
  sInf (nonzeroLatticeNorms B)

theorem nonzeroLatticeNorms_nonempty {n : ℕ} [NeZero n] (B : LatticeBasis n) :
    (nonzeroLatticeNorms B).Nonempty := by
  let i0 : Fin n := ⟨0, NeZero.pos n⟩
  refine ⟨_, fun j => if j = i0 then 1 else 0, ?_, rfl⟩
  intro h
  have h0 : (if i0 = i0 then (1 : ℤ) else 0) = 0 := congr_fun h i0
  simp at h0

theorem nonzeroLatticeNorms_bddBelow {n : ℕ} (B : LatticeBasis n) :
    BddBelow (nonzeroLatticeNorms B) := by
  refine ⟨(matrixEntrySum B.matrix⁻¹)⁻¹, ?_⟩
  rintro r ⟨z, hz, rfl⟩
  exact inv_matrixEntrySum_le_mulVec_intCast B.matrix B.det_ne_zero hz

/-- **Positivity of the first successive minimum (`0 < λ₁(B)`).** -/
theorem lambda1_pos {n : ℕ} [NeZero n] (B : LatticeBasis n) :
    0 < lambda1 B := by
  have hpos : 0 < (matrixEntrySum B.matrix⁻¹)⁻¹ := inv_pos.mpr (matrixEntrySum_pos _)
  refine lt_of_lt_of_le hpos (le_csInf (nonzeroLatticeNorms_nonempty B) ?_)
  rintro r ⟨z, hz, rfl⟩
  exact inv_matrixEntrySum_le_mulVec_intCast B.matrix B.det_ne_zero hz

/-- Every nonzero integer coordinate vector yields a lattice vector of norm at least `λ₁(B)`. -/
theorem lambda1_le_of_ne_zero {n : ℕ} (B : LatticeBasis n) {z : Fin n → ℤ} (hz : z ≠ 0) :
    lambda1 B ≤ euclideanNorm (B.matrix.mulVec (fun i => (z i : ℝ))) :=
  csInf_le (nonzeroLatticeNorms_bddBelow B) ⟨z, hz, rfl⟩

/-- A radius `r > 0` admits `n` linearly independent lattice vectors in `L(B)` of Euclidean norm
at most `r`, represented by a nonsingular integer matrix `Z : Matrix (Fin n) (Fin n) ℤ`. -/
def HasIndepLatticeVectors {n : ℕ} (B : LatticeBasis n) (r : ℝ) : Prop :=
  0 < r ∧ ∃ Z : Matrix (Fin n) (Fin n) ℤ,
    (Z.map (Int.cast : ℤ → ℝ)).det ≠ 0 ∧
    ∀ i : Fin n, euclideanNorm (B.matrix.mulVec (fun j => (Z j i : ℝ))) ≤ r

/-- The `n`-th successive minimum `λ_n(B)`: the infimum of `r > 0` such that `L(B)` contains `n`
linearly independent lattice vectors of Euclidean norm at most `r`. -/
def lambdaN {n : ℕ} (B : LatticeBasis n) : ℝ :=
  sInf { r : ℝ | HasIndepLatticeVectors B r }

theorem hasIndepLatticeVectors_nonempty {n : ℕ} (B : LatticeBasis n) :
    { r : ℝ | HasIndepLatticeVectors B r }.Nonempty := by
  let Z : Matrix (Fin n) (Fin n) ℤ := 1
  let r : ℝ := 1 + ∑ i : Fin n, euclideanNorm (B.matrix.mulVec (fun j => (Z j i : ℝ)))
  refine ⟨r, ?_, Z, ?_, ?_⟩
  · have hsum : 0 ≤ ∑ i : Fin n, euclideanNorm (B.matrix.mulVec (fun j => (Z j i : ℝ))) :=
      Finset.sum_nonneg fun _ _ => euclideanNorm_nonneg _
    linarith
  · have hmap : Z.map (Int.cast : ℤ → ℝ) = 1 := by
      ext i j
      simp [Z, Matrix.one_apply]
    rw [hmap, Matrix.det_one]
    exact one_ne_zero
  · intro i
    have hsingle : euclideanNorm (B.matrix.mulVec (fun j => (Z j i : ℝ))) ≤
        ∑ i' : Fin n, euclideanNorm (B.matrix.mulVec (fun j => (Z j i' : ℝ))) :=
      Finset.single_le_sum
        (f := fun i' => euclideanNorm (B.matrix.mulVec (fun j => (Z j i' : ℝ))))
        (fun _ _ => euclideanNorm_nonneg _) (Finset.mem_univ i)
    linarith

theorem hasIndepLatticeVectors_bddBelow {n : ℕ} (B : LatticeBasis n) :
    BddBelow { r : ℝ | HasIndepLatticeVectors B r } :=
  ⟨0, fun _ hr => hr.1.le⟩

theorem lambdaN_le_of_hasIndepLatticeVectors {n : ℕ} (B : LatticeBasis n)
    {r : ℝ} (hr : HasIndepLatticeVectors B r) :
    lambdaN B ≤ r :=
  csInf_le (hasIndepLatticeVectors_bddBelow B) hr

theorem lambda1_le_of_hasIndepLatticeVectors {n : ℕ} [NeZero n] (B : LatticeBasis n)
    {r : ℝ} (hr : HasIndepLatticeVectors B r) :
    lambda1 B ≤ r := by
  rcases hr with ⟨_, Z, hZdet, hZnorm⟩
  let i0 : Fin n := ⟨0, NeZero.pos n⟩
  have hcol : (fun j => Z j i0) ≠ 0 := by
    intro hzero
    apply hZdet
    refine Matrix.det_eq_zero_of_column_eq_zero i0 fun j => ?_
    have hj : Z j i0 = 0 := congr_fun hzero j
    simp [hj]
  exact (lambda1_le_of_ne_zero B hcol).trans (hZnorm i0)

/-- **Ordering of successive minima (`λ₁(B) ≤ λ_n(B)`).** -/
theorem lambda1_le_lambdaN {n : ℕ} [NeZero n] (B : LatticeBasis n) :
    lambda1 B ≤ lambdaN B :=
  le_csInf (hasIndepLatticeVectors_nonempty B) fun _ hr =>
    lambda1_le_of_hasIndepLatticeVectors B hr

/-- **Positivity of the `n`-th successive minimum (`0 < λ_n(B)`).** -/
theorem lambdaN_pos {n : ℕ} [NeZero n] (B : LatticeBasis n) :
    0 < lambdaN B :=
  lt_of_lt_of_le (lambda1_pos B) (lambda1_le_lambdaN B)

/-- A nonzero integer vector cannot be orthogonal to all columns of a nonsingular integer matrix. -/
theorem exists_col_dotProduct_ne_zero {n : ℕ} {z : Fin n → ℤ} (hz : z ≠ 0)
    {Y : Matrix (Fin n) (Fin n) ℤ} (hY : (Y.map (Int.cast : ℤ → ℝ)).det ≠ 0) :
    ∃ i : Fin n, (∑ j : Fin n, z j * Y j i) ≠ 0 := by
  by_contra h_all
  rw [not_exists] at h_all
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hz
  let YR : Matrix (Fin n) (Fin n) ℝ := Y.map (Int.cast : ℤ → ℝ)
  let zR : Fin n → ℝ := fun j => (z j : ℝ)
  have hmul : YRᵀ.mulVec zR = 0 := by
    ext i
    change ∑ j : Fin n, (Y j i : ℝ) * (z j : ℝ) = 0
    have hi : ((∑ j : Fin n, z j * Y j i : ℤ) : ℝ) = 0 := by
      rw [not_not.mp (h_all i), Int.cast_zero]
    push_cast at hi
    calc
      ∑ j : Fin n, (Y j i : ℝ) * (z j : ℝ) = ∑ j : Fin n, (z j : ℝ) * (Y j i : ℝ) :=
        Finset.sum_congr rfl fun j _ => mul_comm _ _
      _ = 0 := hi
  have hYRT : IsUnit YRᵀ.det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr hY
  have hzR0 : zR = 0 := by
    calc
      zR = (1 : Matrix (Fin n) (Fin n) ℝ).mulVec zR := (Matrix.one_mulVec zR).symm
      _ = ((YRᵀ)⁻¹ * YRᵀ).mulVec zR := by rw [Matrix.nonsing_inv_mul _ hYRT]
      _ = (YRᵀ)⁻¹.mulVec (YRᵀ.mulVec zR) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [hmul, Matrix.mulVec_zero]
  have hj0' : (z j0 : ℝ) = 0 := congr_fun hzR0 j0
  exact hj0 (Int.cast_eq_zero.mp hj0')

theorem one_le_norm_mul_of_hasIndepDual {n : ℕ} (B : LatticeBasis n)
    {z : Fin n → ℤ} (hz : z ≠ 0) {r : ℝ} (hr : HasIndepLatticeVectors (dualBasis B) r) :
    1 ≤ euclideanNorm (B.matrix.mulVec (fun j => (z j : ℝ))) * r := by
  rcases hr with ⟨_, Y, hYdet, hYnorm⟩
  obtain ⟨i, hi⟩ := exists_col_dotProduct_ne_zero hz hYdet
  let zR : Fin n → ℝ := fun j => (z j : ℝ)
  let yR : Fin n → ℝ := fun j => (Y j i : ℝ)
  have hdot : (B.matrix.mulVec zR) ⬝ᵥ ((dualBasis B).matrix.mulVec yR) =
      ((∑ j : Fin n, z j * Y j i : ℤ) : ℝ) := by
    rw [mulVec_dotProduct_dualBasis]
    change ∑ j : Fin n, (z j : ℝ) * (Y j i : ℝ) = _
    push_cast
    rfl
  have h1 : (1 : ℝ) ≤ |(B.matrix.mulVec zR) ⬝ᵥ ((dualBasis B).matrix.mulVec yR)| := by
    rw [hdot]
    have h1' : (1 : ℤ) ≤ |∑ j : Fin n, z j * Y j i| := Int.one_le_abs hi
    exact_mod_cast h1'
  have hcs := abs_dotProduct_le_euclideanNorm_mul
    (B.matrix.mulVec zR) ((dualBasis B).matrix.mulVec yR)
  have hle : euclideanNorm (B.matrix.mulVec zR) * euclideanNorm ((dualBasis B).matrix.mulVec yR) ≤
      euclideanNorm (B.matrix.mulVec zR) * r :=
    mul_le_mul_of_nonneg_left (hYnorm i) (euclideanNorm_nonneg _)
  exact (h1.trans hcs).trans hle

/-- **Lower transference bound (`1 ≤ λ₁(B) * λ_n(B*)`).**
Every nonzero vector in `L` has nonzero integer inner product with at least one of any `n`
linearly independent vectors in `L*`. -/
theorem one_le_lambda1_mul_lambdaN_dualBasis {n : ℕ} [NeZero n] (B : LatticeBasis n) :
    1 ≤ lambda1 B * lambdaN (dualBasis B) := by
  have hl1 : 0 < lambda1 B := lambda1_pos B
  rw [← inv_le_iff_one_le_mul₀' hl1]
  refine le_csInf (hasIndepLatticeVectors_nonempty (dualBasis B)) ?_
  intro r hr
  have hrpos : 0 < r := hr.1
  rw [inv_le_comm₀ hl1 hrpos]
  refine le_csInf (nonzeroLatticeNorms_nonempty B) ?_
  rintro s ⟨z, hz, rfl⟩
  rw [inv_le_iff_one_le_mul₀' hrpos, mul_comm]
  exact one_le_norm_mul_of_hasIndepDual B hz hr

/-- Dual lower transference bound: `1 ≤ λ₁(B*) * λ_n(B)`. -/
theorem one_le_lambda1_dualBasis_mul_lambdaN {n : ℕ} [NeZero n] (B : LatticeBasis n) :
    1 ≤ lambda1 (dualBasis B) * lambdaN B := by
  have h := one_le_lambda1_mul_lambdaN_dualBasis (dualBasis B)
  simpa only [dualBasis_dualBasis] using h

/-- Banaszczyk's upper transference bound `λ₁(B) * λ_n(B*) ≤ n` [Banaszczyk1993, Theorem 2.1]. -/
def HasBanaszczykBound {n : ℕ} (B : LatticeBasis n) : Prop :=
  lambda1 B * lambdaN (dualBasis B) ≤ n

/-- **Banaszczyk's transference bounds** (`1 ≤ λ₁(B) * λ_n(B*) ≤ n`). -/
theorem banaszczyk_transference_bounds {n : ℕ} [NeZero n] (B : LatticeBasis n)
    (hB : HasBanaszczykBound B) :
    1 ≤ lambda1 B * lambdaN (dualBasis B) ∧ lambda1 B * lambdaN (dualBasis B) ≤ n :=
  ⟨one_le_lambda1_mul_lambdaN_dualBasis B, hB⟩

/-- The scaled identity lattice basis `c • I_n` for `c > 0`. -/
def scaledIdentityBasis (n : ℕ) (c : ℝ) (hc : 0 < c) : LatticeBasis n where
  matrix := c • (1 : Matrix (Fin n) (Fin n) ℝ)
  det_ne_zero := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (ne_of_gt hc)

theorem scaledIdentityBasis_mulVec {n : ℕ} (c : ℝ) (hc : 0 < c) (v : Fin n → ℝ) :
    (scaledIdentityBasis n c hc).matrix.mulVec v = fun i => c * v i := by
  ext i
  simp [scaledIdentityBasis, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem c_le_lambda1_scaledIdentityBasis {n : ℕ} [NeZero n] (c : ℝ) (hc : 0 < c) :
    c ≤ lambda1 (scaledIdentityBasis n c hc) := by
  refine le_csInf (nonzeroLatticeNorms_nonempty _) ?_
  rintro r ⟨z, hz, rfl⟩
  rw [scaledIdentityBasis_mulVec, euclideanNorm_smul hc.le]
  exact le_mul_of_one_le_right hc.le (one_le_euclideanNorm_intCast hz)

theorem hasIndepLatticeVectors_scaledIdentityBasis {n : ℕ} (c : ℝ) (hc : 0 < c) :
    HasIndepLatticeVectors (scaledIdentityBasis n c hc) c := by
  refine ⟨hc, 1, ?_, ?_⟩
  · have hmap : (1 : Matrix (Fin n) (Fin n) ℤ).map (Int.cast : ℤ → ℝ) = 1 := by
      ext i j
      simp [Matrix.one_apply]
    rw [hmap, Matrix.det_one]
    exact one_ne_zero
  · intro i
    rw [scaledIdentityBasis_mulVec]
    have hcol : (fun j : Fin n => c * (((1 : Matrix (Fin n) (Fin n) ℤ) j i : ℤ) : ℝ)) =
        fun j : Fin n => if j = i then c else 0 := by
      ext j
      simp [Matrix.one_apply]
    rw [hcol, euclideanNorm_single hc.le i]

@[simp]
theorem lambda1_scaledIdentityBasis {n : ℕ} [NeZero n] (c : ℝ) (hc : 0 < c) :
    lambda1 (scaledIdentityBasis n c hc) = c := by
  apply le_antisymm
  · exact (lambda1_le_lambdaN _).trans
      (lambdaN_le_of_hasIndepLatticeVectors _ (hasIndepLatticeVectors_scaledIdentityBasis c hc))
  · exact c_le_lambda1_scaledIdentityBasis c hc

@[simp]
theorem lambdaN_scaledIdentityBasis {n : ℕ} [NeZero n] (c : ℝ) (hc : 0 < c) :
    lambdaN (scaledIdentityBasis n c hc) = c := by
  apply le_antisymm
  · exact lambdaN_le_of_hasIndepLatticeVectors _ (hasIndepLatticeVectors_scaledIdentityBasis c hc)
  · exact (c_le_lambda1_scaledIdentityBasis c hc).trans (lambda1_le_lambdaN _)

@[simp]
theorem dualBasis_scaledIdentityBasis {n : ℕ} (c : ℝ) (hc : 0 < c) :
    dualBasis (scaledIdentityBasis n c hc) = scaledIdentityBasis n c⁻¹ (inv_pos.mpr hc) := by
  ext i j
  change ((c • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹)ᵀ i j = (c⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) i j
  have h1 : c • (1 : Matrix (Fin n) (Fin n) ℝ) * (c⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) = 1 := by
    rw [smul_mul_smul_comm, mul_one, mul_inv_cancel₀ (ne_of_gt hc), one_smul]
  have hinv : (c • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ = c⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ) :=
    Matrix.inv_eq_right_inv h1
  rw [hinv, Matrix.transpose_smul, Matrix.transpose_one]

/-- Every scaled identity lattice `c • ℤ^n` satisfies Banaszczyk's transference bound with
`λ₁(B) * λ_n(B*) = 1 ≤ n`. -/
theorem hasBanaszczykBound_scaledIdentityBasis {n : ℕ} [NeZero n] (c : ℝ) (hc : 0 < c) :
    HasBanaszczykBound (scaledIdentityBasis n c hc) := by
  unfold HasBanaszczykBound
  rw [dualBasis_scaledIdentityBasis, lambda1_scaledIdentityBasis, lambdaN_scaledIdentityBasis,
    mul_inv_cancel₀ (ne_of_gt hc)]
  exact_mod_cast NeZero.pos n

/-- **The `GapSVP` promise problem** in dimension `n` with approximation factor `γ` and distance
threshold `d`:
* Yes-instances are bases `B` with `λ₁(B) ≤ d`.
* No-instances are bases `B` with `γ * d < λ₁(B)` (and `d ≤ γ * d` so the sets are disjoint). -/
def GapSVP (n : ℕ) (γ d : ℝ) : PromiseProblem (LatticeBasis n) where
  yes := { B | lambda1 B ≤ d }
  no := { B | γ * d < lambda1 B ∧ d ≤ γ * d }
  disjoint := Set.disjoint_left.2 fun _ hyes hno => (hyes.trans hno.2).not_gt hno.1

@[simp]
theorem mem_yes_GapSVP {n : ℕ} {γ d : ℝ} {B : LatticeBasis n} :
    B ∈ (GapSVP n γ d).yes ↔ lambda1 B ≤ d :=
  Iff.rfl

@[simp]
theorem mem_no_GapSVP {n : ℕ} {γ d : ℝ} {B : LatticeBasis n} :
    B ∈ (GapSVP n γ d).no ↔ γ * d < lambda1 B ∧ d ≤ γ * d :=
  Iff.rfl

theorem mem_no_GapSVP_of_one_le {n : ℕ} {γ d : ℝ} (hγ : 1 ≤ γ) (hd : 0 ≤ d)
    {B : LatticeBasis n} :
    B ∈ (GapSVP n γ d).no ↔ γ * d < lambda1 B :=
  and_iff_left (le_mul_of_one_le_left hd hγ)

/-- A witness for the Shortest Independent Vectors Problem (`SIVP`) on a lattice `B`: `n` linearly
independent lattice vectors (represented by a nonsingular integer coefficient matrix `Z`) together
with an upper bound `normBound` on their Euclidean norms. -/
structure SIVPWitness {n : ℕ} (B : LatticeBasis n) where
  /-- Nonsingular integer coefficient matrix of the `n` lattice vectors. -/
  coeffs : Matrix (Fin n) (Fin n) ℤ
  /-- Linear independence of the `n` lattice vectors over `ℝ`. -/
  det_ne_zero : (coeffs.map (Int.cast : ℤ → ℝ)).det ≠ 0
  /-- Common upper bound on the Euclidean norms of the `n` lattice vectors. -/
  normBound : ℝ
  /-- Positivity of the norm bound. -/
  normBound_pos : 0 < normBound
  /-- Every column yields a lattice vector of Euclidean norm at most `normBound`. -/
  norm_le : ∀ i : Fin n, euclideanNorm (B.matrix.mulVec (fun j => (coeffs j i : ℝ))) ≤ normBound

/-- Every `SIVPWitness` certifies `HasIndepLatticeVectors B W.normBound`. -/
theorem SIVPWitness.hasIndepLatticeVectors {n : ℕ} {B : LatticeBasis n} (W : SIVPWitness B) :
    HasIndepLatticeVectors B W.normBound :=
  ⟨W.normBound_pos, W.coeffs, W.det_ne_zero, W.norm_le⟩

/-- The norm bound of any `SIVPWitness` is at least `λ_n(B)`. -/
theorem SIVPWitness.lambdaN_le_normBound {n : ℕ} {B : LatticeBasis n} (W : SIVPWitness B) :
    lambdaN B ≤ W.normBound :=
  lambdaN_le_of_hasIndepLatticeVectors B W.hasIndepLatticeVectors

/-- A witness `W : SIVPWitness B` solves `SIVP_γ` when its vectors have norm at most
`γ * λ_n(B)`. -/
def SIVPWitness.IsApproxSolution {n : ℕ} {B : LatticeBasis n} (W : SIVPWitness B) (γ : ℝ) : Prop :=
  W.normBound ≤ γ * lambdaN B

/-- A worst-case `SIVP_γ` solver in dimension `n`, producing `n` linearly independent lattice
vectors of norm at most `γ * λ_n(B)` for every full-rank lattice `B`. -/
structure SIVPSolver (n : ℕ) (γ : ℝ) where
  /-- Witness produced on input basis `B`. -/
  solve : (B : LatticeBasis n) → SIVPWitness B
  /-- Approximation guarantee `normBound ≤ γ * λ_n(B)` on every lattice basis `B`. -/
  isApprox : ∀ B : LatticeBasis n, (solve B).IsApproxSolution γ

/-! ### Part 2: Gaussian Noise Distribution, Modulus Regime `α q > 2 √n`, and `SearchLWE` -/

/-- The 1D Gaussian probability density function `ρ_s(x) / s = exp(-π (x / s)²) / s` of width
parameter `s > 0` [Regev2009, Section 2]. -/
def gaussianPdf (s x : ℝ) : ℝ :=
  Real.exp (-Real.pi * (x / s) ^ 2) / s

theorem gaussianPdf_pos {s : ℝ} (hs : 0 < s) (x : ℝ) : 0 < gaussianPdf s x :=
  div_pos (Real.exp_pos _) hs

@[simp]
theorem gaussianPdf_zero (s : ℝ) : gaussianPdf s 0 = 1 / s := by
  simp [gaussianPdf]

theorem gaussianPdf_symm (s x : ℝ) : gaussianPdf s (-x) = gaussianPdf s x := by
  simp [gaussianPdf, neg_div]

theorem gaussianPdf_le_inv {s : ℝ} (hs : 0 < s) (x : ℝ) : gaussianPdf s x ≤ 1 / s := by
  unfold gaussianPdf
  rw [div_le_div_iff_of_pos_right hs, Real.exp_le_one_iff]
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hsq : 0 ≤ (x / s) ^ 2 := sq_nonneg _
  nlinarith

/-- Unnormalized discrete Gaussian weight on `ZMod q` with noise rate `α`, assigning weight
`exp(-π (|e|_q / (α q))²)` to each residue `e : ZMod q` via its centered representative
`e.valMinAbs ∈ [-q/2, q/2]`. -/
def discreteGaussianWeight (q : ℕ) (α : ℝ) (e : ZMod q) : ℝ :=
  Real.exp (-Real.pi * ((e.valMinAbs : ℝ) / (α * (q : ℝ))) ^ 2)

theorem discreteGaussianWeight_pos (q : ℕ) (α : ℝ) (e : ZMod q) :
    0 < discreteGaussianWeight q α e :=
  Real.exp_pos _

@[simp]
theorem discreteGaussianWeight_zero (q : ℕ) (α : ℝ) :
    discreteGaussianWeight q α 0 = 1 := by
  simp [discreteGaussianWeight]

/-- Normalization constant (partition function) of the discrete Gaussian distribution on
`ZMod q`. -/
def discreteGaussianNorm (q : ℕ) [NeZero q] (α : ℝ) : ℝ :=
  ∑ e : ZMod q, discreteGaussianWeight q α e

theorem one_le_discreteGaussianNorm (q : ℕ) [NeZero q] (α : ℝ) :
    1 ≤ discreteGaussianNorm q α := by
  unfold discreteGaussianNorm
  have h0 : discreteGaussianWeight q α 0 ≤ ∑ e : ZMod q, discreteGaussianWeight q α e :=
    Finset.single_le_sum (fun e _ => (discreteGaussianWeight_pos q α e).le) (Finset.mem_univ 0)
  simpa using h0

theorem discreteGaussianNorm_pos (q : ℕ) [NeZero q] (α : ℝ) :
    0 < discreteGaussianNorm q α :=
  lt_of_lt_of_le zero_lt_one (one_le_discreteGaussianNorm q α)

/-- Normalized probability mass of `e : ZMod q` under the discrete Gaussian noise distribution
`Ψ_α`. -/
def discreteGaussianProb (q : ℕ) [NeZero q] (α : ℝ) (e : ZMod q) : ℝ :=
  discreteGaussianWeight q α e / discreteGaussianNorm q α

theorem discreteGaussianProb_pos (q : ℕ) [NeZero q] (α : ℝ) (e : ZMod q) :
    0 < discreteGaussianProb q α e :=
  div_pos (discreteGaussianWeight_pos q α e) (discreteGaussianNorm_pos q α)

theorem sum_discreteGaussianProb (q : ℕ) [NeZero q] (α : ℝ) :
    ∑ e : ZMod q, discreteGaussianProb q α e = 1 := by
  unfold discreteGaussianProb
  rw [← Finset.sum_div, ← discreteGaussianNorm]
  exact div_self (ne_of_gt (discreteGaussianNorm_pos q α))

/-- The discrete Gaussian noise probability mass function `Ψ_α` on `ZMod q`. -/
def discreteGaussianPMF (q : ℕ) [NeZero q] (α : ℝ) : PMF (ZMod q) :=
  PMF.ofFintype (fun e => ENNReal.ofReal (discreteGaussianProb q α e)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun e _ => (discreteGaussianProb_pos q α e).le),
      sum_discreteGaussianProb, ENNReal.ofReal_one])

/-- **Regev's parameter regime** [Regev2009, Theorem 1.1]: dimension `n > 0`, modulus `q ≥ 2`,
Gaussian noise rate `0 < α < 1`, and the smoothing condition `2 * √n < α * q`. -/
structure RegevParameters (n q : ℕ) (α : ℝ) : Prop where
  /-- Positive lattice/secret dimension. -/
  n_pos : 0 < n
  /-- Nondegenerate integer modulus `q ≥ 2`. -/
  q_ge_two : 2 ≤ q
  /-- Strictly positive Gaussian noise rate. -/
  α_pos : 0 < α
  /-- Sub-unit Gaussian noise rate. -/
  α_lt_one : α < 1
  /-- Regev's smoothing condition `α q > 2 √n`, ensuring that each quantum step shrinks the
  discrete Gaussian width by a factor `2 √n / (α q) < 1`. -/
  smoothing_cond : 2 * Real.sqrt (n : ℝ) < α * (q : ℝ)

/-- For every `n ≥ 10`, the polynomial modulus `q = n ^ 2 + 5` and inverse-polynomial noise rate
`α = 3 / √n` satisfy `RegevParameters n (n ^ 2 + 5) (3 / √n)`. -/
theorem regevParameters_explicit {n : ℕ} (hn : 10 ≤ n) :
    RegevParameters n (n ^ 2 + 5) (3 / Real.sqrt (n : ℝ)) where
  n_pos := by omega
  q_ge_two := by omega
  α_pos := by positivity
  α_lt_one := by
    have h9 : (9 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 9 < n)
    have hsqrt : (3 : ℝ) < Real.sqrt (n : ℝ) := (Real.lt_sqrt (by norm_num)).mpr (by linarith)
    exact (div_lt_one (by positivity)).mpr hsqrt
  smoothing_cond := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    rw [div_mul_eq_mul_div, lt_div_iff₀ hsqrt_pos, mul_assoc, Real.mul_self_sqrt hn_pos.le]
    have hcast : ((n ^ 2 + 5 : ℕ) : ℝ) = (n : ℝ) ^ 2 + 5 := by push_cast; ring
    rw [hcast]
    nlinarith

/-- For every `n ≥ 1`, the polynomial modulus `q = n ^ 2 + 5` and inverse-polynomial noise rate
`α = 3 / (√n + 3)` satisfy `RegevParameters n (n ^ 2 + 5) (3 / (√n + 3))`. -/
theorem regevParameters_all_pos {n : ℕ} (hn : 1 ≤ n) :
    RegevParameters n (n ^ 2 + 5) (3 / (Real.sqrt (n : ℝ) + 3)) where
  n_pos := by omega
  q_ge_two := by omega
  α_pos := by positivity
  α_lt_one := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    exact (div_lt_one (by positivity)).mpr (by linarith)
  smoothing_cond := by
    have hn_ge : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsqrt_le : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt (by linarith)
    have hcast : ((n ^ 2 + 5 : ℕ) : ℝ) = (n : ℝ) ^ 2 + 5 := by push_cast; ring
    rw [hcast]
    nlinarith

/-- An LWE sample `(a, b) ∈ (ZMod q)^n × ZMod q`. -/
abbrev LWESample (n q : ℕ) : Type := (Fin n → ZMod q) × ZMod q

/-- Modular inner product `⟨a, s⟩ = ∑ j, a j * s j` over `ZMod q`. -/
def lweInnerProduct {n q : ℕ} (a s : Fin n → ZMod q) : ZMod q :=
  ∑ j : Fin n, a j * s j

/-- Construct the LWE sample `(a, ⟨a, s⟩ + e)` from secret `s`, public vector `a`, and error `e`. -/
def lweSampleFromNoise {n q : ℕ} (s a : Fin n → ZMod q) (e : ZMod q) : LWESample n q :=
  (a, lweInnerProduct a s + e)

/-- The LWE sample distribution `A_{s, α}` on `(ZMod q)^n × ZMod q`, drawing `a` uniformly from
`(ZMod q)^n` and `e` from `discreteGaussianPMF q α`, and outputting `(a, ⟨a, s⟩ + e)`. -/
def lweSamplePMF (n q : ℕ) [NeZero q] (α : ℝ) (s : Fin n → ZMod q) : PMF (LWESample n q) :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod q)).bind fun a =>
    (discreteGaussianPMF q α).map fun e => lweSampleFromNoise s a e

/-- An average-case `SearchLWE` oracle for dimension `n`, modulus `q`, and Gaussian noise rate `α`:
given `sampleCount` noisy linear equations `(a_i, ⟨a_i, s⟩ + e_i)` whose centered noise magnitudes
`|e_i|_q` lie within the Gaussian standard deviation bound `α q / √2`, the oracle recovers the
secret vector `s ∈ (ZMod q)^n`. -/
structure SearchLWEOracle (n q : ℕ) (α : ℝ) where
  /-- Number of LWE samples consumed per oracle invocation. -/
  sampleCount : ℕ
  /-- Recovery procedure mapping a batch of LWE samples to a candidate secret in `(ZMod q)^n`. -/
  solve : (Fin sampleCount → LWESample n q) → (Fin n → ZMod q)
  /-- Correctness on LWE samples with Gaussian noise bounded by `α q / √2`. -/
  correct_on_bounded_noise :
    ∀ (s : Fin n → ZMod q) (a : Fin sampleCount → Fin n → ZMod q) (e : Fin sampleCount → ZMod q),
      (∀ i : Fin sampleCount, |(e i).valMinAbs| ≤ α * (q : ℝ) / Real.sqrt 2) →
      solve (fun i => lweSampleFromNoise s (a i) (e i)) = s

/-! ### Part 3: Regev's Iterative Quantum Reduction (`BDD ↔ LWE`, `DGS ↔ BDD`, `SIVP` & `GapSVP`) -/

/-- The dual-lattice Bounded Distance Decoding (`BDD`) radius `d = α q / (√2 r)` achieved by
Regev's classical reduction using a discrete Gaussian state of width `r` [Regev2009, Lemma 3.4]. -/
def bddRadius (q : ℕ) (α r : ℝ) : ℝ :=
  α * (q : ℝ) / (Real.sqrt 2 * r)

theorem bddRadius_pos {n q : ℕ} {α r : ℝ} (h : RegevParameters n q α) (hr : 0 < r) :
    0 < bddRadius q α r := by
  unfold bddRadius
  have hq : (0 : ℝ) < (q : ℝ) := by
    have hq2 := h.q_ge_two
    exact_mod_cast (by omega : 0 < q)
  have hα : 0 < α := h.α_pos
  positivity

/-- An instance of Bounded Distance Decoding (`BDD`) on the dual lattice `L*(B)` within radius `d`:
a target point `target = B* s + offset` at Euclidean distance `‖offset‖₂ ≤ d` from the dual lattice
point `B* s` with integer coordinates `secretCoords = s`. -/
structure DualBDDInstance {n : ℕ} (B : LatticeBasis n) (d : ℝ) where
  /-- Integer coordinate vector `s ∈ ℤ^n` of the closest dual lattice vector `B* s ∈ L*`. -/
  secretCoords : Fin n → ℤ
  /-- Continuous perturbation vector `δ ∈ ℝ^n` from the dual lattice point. -/
  offset : Fin n → ℝ
  /-- Distance guarantee `‖δ‖₂ ≤ d`. -/
  offset_norm_le : euclideanNorm offset ≤ d

/-- The target vector `x = B* s + δ ∈ ℝ^n` of a `DualBDDInstance`. -/
def DualBDDInstance.target {n : ℕ} {B : LatticeBasis n} {d : ℝ}
    (inst : DualBDDInstance B d) : Fin n → ℝ :=
  (dualBasis B).matrix.mulVec (fun j => (inst.secretCoords j : ℝ)) + inst.offset

/-- **Algebraic heart of Regev's classical BDD-to-LWE reduction [Regev2009, Lemma 3.4]:**
taking the inner product of a primal lattice vector `u = B a` (with integer coordinates `a ∈ ℤ^n`)
against the BDD target `x = B* s + δ` produces the exact integer inner product `⟨a, s⟩` plus the
continuous inner-product noise `⟨B a, δ⟩`. -/
theorem dualBDD_innerProduct_eq {n : ℕ} (B : LatticeBasis n) {d : ℝ}
    (inst : DualBDDInstance B d) (a : Fin n → ℤ) :
    (B.matrix.mulVec (fun j => (a j : ℝ))) ⬝ᵥ inst.target =
      ((∑ j : Fin n, a j * inst.secretCoords j : ℤ) : ℝ) +
        (B.matrix.mulVec (fun j => (a j : ℝ))) ⬝ᵥ inst.offset := by
  unfold DualBDDInstance.target
  rw [dotProduct_add, mulVec_dotProduct_dualBasis]
  congr 1
  change ∑ j : Fin n, (a j : ℝ) * (inst.secretCoords j : ℝ) = _
  push_cast
  rfl

/-- **Noise bound in Regev's classical BDD-to-LWE step:**
when the primal lattice vector `B a` has Euclidean norm at most `r > 0` and the BDD target lies
within `bddRadius q α r = α q / (√2 r)`, the continuous inner-product error `|⟨B a, δ⟩|` is at
most `α q / √2`. -/
theorem dualBDD_noise_le {n q : ℕ} (B : LatticeBasis n) {α r : ℝ} (hr : 0 < r)
    (inst : DualBDDInstance B (bddRadius q α r)) {a : Fin n → ℤ}
    (ha : euclideanNorm (B.matrix.mulVec (fun j => (a j : ℝ))) ≤ r) :
    |(B.matrix.mulVec (fun j => (a j : ℝ))) ⬝ᵥ inst.offset| ≤ α * (q : ℝ) / Real.sqrt 2 := by
  have hcs := abs_dotProduct_le_euclideanNorm_mul
    (B.matrix.mulVec (fun j => (a j : ℝ))) inst.offset
  have hmul : euclideanNorm (B.matrix.mulVec (fun j => (a j : ℝ))) * euclideanNorm inst.offset ≤
      r * bddRadius q α r :=
    mul_le_mul ha inst.offset_norm_le (euclideanNorm_nonneg _) hr.le
  have hcancel : r * bddRadius q α r = α * (q : ℝ) / Real.sqrt 2 := by
    unfold bddRadius
    have hr_ne : r ≠ 0 := ne_of_gt hr
    have hsqrt_ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr zero_lt_two)
    field_simp
  exact (hcs.trans hmul).trans_eq hcancel

/-- Classical `BDD`-to-`SearchLWE` reduction procedure: feeds `m` primal lattice inner-product
samples `(a_i mod q, ⟨a_i, s⟩ + e_i mod q)` into the `SearchLWEOracle` to recover `s mod q`. -/
def solveDualBDDModQ {n q : ℕ} {α r : ℝ} (oracle : SearchLWEOracle n q α)
    {B : LatticeBasis n} (inst : DualBDDInstance B (bddRadius q α r))
    (a : Fin oracle.sampleCount → Fin n → ℤ) (e : Fin oracle.sampleCount → ZMod q) :
    Fin n → ZMod q :=
  oracle.solve (fun i =>
    lweSampleFromNoise (fun j => (inst.secretCoords j : ZMod q)) (fun j => (a i j : ZMod q)) (e i))

/-- **Correctness of the classical `BDD`-to-`SearchLWE` reduction [Regev2009, Lemma 3.4]:**
when each sampled primal lattice vector `B (a_i)` has norm at most `r` and the modular noise `e_i`
is bounded in magnitude by the continuous inner-product error `|⟨B (a_i), δ⟩|`, the LWE oracle
recovers the exact modular dual coordinates `s mod q`. -/
theorem solveDualBDDModQ_eq_secretCoords {n q : ℕ} {α r : ℝ} (hr : 0 < r)
    (oracle : SearchLWEOracle n q α) {B : LatticeBasis n}
    (inst : DualBDDInstance B (bddRadius q α r))
    (a : Fin oracle.sampleCount → Fin n → ℤ) (e : Fin oracle.sampleCount → ZMod q)
    (ha : ∀ i, euclideanNorm (B.matrix.mulVec (fun j => (a i j : ℝ))) ≤ r)
    (he : ∀ i, |(e i).valMinAbs| ≤ |(B.matrix.mulVec (fun j => (a i j : ℝ))) ⬝ᵥ inst.offset|) :
    solveDualBDDModQ oracle inst a e = fun j => (inst.secretCoords j : ZMod q) := by
  apply oracle.correct_on_bounded_noise
  intro i
  exact (he i).trans (dualBDD_noise_le B hr inst (ha i))

/-- A discrete Gaussian superposition state over `L(B)` at width `r > 0`, providing `n` linearly
independent lattice vectors of Euclidean norm at most `√n * r` (by Banaszczyk's Gaussian tail
bound). -/
structure DiscreteGaussianSuperposition {n : ℕ} (B : LatticeBasis n) (r : ℝ) where
  /-- Positivity of the Gaussian width parameter `r`. -/
  width_pos : 0 < r
  /-- Nonsingular integer coefficient matrix of `n` independent vectors drawn from `D_{L, r}`. -/
  coeffs : Matrix (Fin n) (Fin n) ℤ
  /-- Linear independence of the sampled lattice vectors. -/
  det_ne_zero : (coeffs.map (Int.cast : ℤ → ℝ)).det ≠ 0
  /-- Each sampled vector from `D_{L, r}` has Euclidean norm at most `√n * r`. -/
  norm_le : ∀ i : Fin n,
    euclideanNorm (B.matrix.mulVec (fun j => (coeffs j i : ℝ))) ≤ Real.sqrt (n : ℝ) * r

/-- Convert a `DiscreteGaussianSuperposition B r` into an `SIVPWitness B` with norm bound
`√n * r`. -/
def DiscreteGaussianSuperposition.toSIVPWitness {n : ℕ} [NeZero n] {B : LatticeBasis n} {r : ℝ}
    (state : DiscreteGaussianSuperposition B r) : SIVPWitness B where
  coeffs := state.coeffs
  det_ne_zero := state.det_ne_zero
  normBound := Real.sqrt (n : ℝ) * r
  normBound_pos := by
    have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast NeZero.pos n
    have hr : 0 < r := state.width_pos
    positivity
  norm_le := state.norm_le

/-- Every width `r` with `λ_n(B) < √n * r` admits a `DiscreteGaussianSuperposition B r`. -/
theorem nonempty_discreteGaussianSuperposition_of_lt {n : ℕ} [NeZero n] (B : LatticeBasis n)
    {r : ℝ} (hr : lambdaN B < Real.sqrt (n : ℝ) * r) :
    Nonempty (DiscreteGaussianSuperposition B r) := by
  obtain ⟨s, hs, hslt⟩ := exists_lt_of_csInf_lt (hasIndepLatticeVectors_nonempty B) hr
  rcases hs with ⟨_, Z, hZdet, hZnorm⟩
  have hn : (0 : ℝ) < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos n)
  have hrpos : 0 < r := pos_of_mul_pos_right (lt_trans (lambdaN_pos B) hr) hn.le
  exact ⟨⟨hrpos, Z, hZdet, fun i => (hZnorm i).trans hslt.le⟩⟩

/-- Initial width `r₀ > 0` for the basis `B` itself, before iterative quantum reduction. -/
def initialGaussianWidth {n : ℕ} (B : LatticeBasis n) : ℝ :=
  1 + ∑ i : Fin n, euclideanNorm (B.matrix.mulVec (fun j =>
    (((1 : Matrix (Fin n) (Fin n) ℤ) j i : ℤ) : ℝ)))

theorem initialGaussianWidth_pos {n : ℕ} (B : LatticeBasis n) :
    0 < initialGaussianWidth B := by
  unfold initialGaussianWidth
  have h : 0 ≤ ∑ i : Fin n, euclideanNorm (B.matrix.mulVec (fun j =>
      (((1 : Matrix (Fin n) (Fin n) ℤ) j i : ℤ) : ℝ))) :=
    Finset.sum_nonneg fun _ _ => euclideanNorm_nonneg _
  linarith

/-- Unconditional construction of the initial `DiscreteGaussianSuperposition` at width
`initialGaussianWidth B` from the input basis `B`. -/
def initialGaussianState {n : ℕ} [NeZero n] (B : LatticeBasis n) :
    DiscreteGaussianSuperposition B (initialGaussianWidth B) where
  width_pos := initialGaussianWidth_pos B
  coeffs := 1
  det_ne_zero := by
    have hmap : (1 : Matrix (Fin n) (Fin n) ℤ).map (Int.cast : ℤ → ℝ) = 1 := by
      ext i j
      simp [Matrix.one_apply]
    rw [hmap, Matrix.det_one]
    exact one_ne_zero
  norm_le := by
    intro i
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast NeZero.pos n
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      simpa using Real.sqrt_le_sqrt hn1
    have hsingle : euclideanNorm (B.matrix.mulVec (fun j =>
        (((1 : Matrix (Fin n) (Fin n) ℤ) j i : ℤ) : ℝ))) ≤ initialGaussianWidth B := by
      unfold initialGaussianWidth
      have hs := Finset.single_le_sum
        (f := fun i' => euclideanNorm (B.matrix.mulVec (fun j =>
          (((1 : Matrix (Fin n) (Fin n) ℤ) j i' : ℤ) : ℝ))))
        (fun _ _ => euclideanNorm_nonneg _) (Finset.mem_univ i)
      linarith
    have hw : initialGaussianWidth B ≤ Real.sqrt (n : ℝ) * initialGaussianWidth B :=
      le_mul_of_one_le_left (initialGaussianWidth_pos B).le hsqrt1
    exact hsingle.trans hw

/-- The multiplicative width-shrinking factor `2 √n / (α q)` of each quantum step in Regev's
reduction [Regev2009, Lemma 3.14]. -/
def regevShrinkFactor (n q : ℕ) (α : ℝ) : ℝ :=
  2 * Real.sqrt (n : ℝ) / (α * (q : ℝ))

/-- The new Gaussian width `r' = r * (2 √n / (α q))` after one quantum QFT + BDD step. -/
def nextGaussianWidth (n q : ℕ) (α r : ℝ) : ℝ :=
  r * regevShrinkFactor n q α

/-- The Gaussian width `r₀ * (2 √n / (α q))^k` after `k` quantum steps. -/
def iteratedGaussianWidth (n q : ℕ) (α : ℝ) (k : ℕ) (r₀ : ℝ) : ℝ :=
  r₀ * (regevShrinkFactor n q α) ^ k

/-- The stopping width `2 √n / (α λ₁(B*))` below which the iterative reduction terminates
[Regev2009, Section 3.3]. -/
def stoppingWidth {n : ℕ} (B : LatticeBasis n) (α : ℝ) : ℝ :=
  2 * Real.sqrt (n : ℝ) / (α * lambda1 (dualBasis B))

theorem regevShrinkFactor_pos {n q : ℕ} {α : ℝ} (h : RegevParameters n q α) :
    0 < regevShrinkFactor n q α := by
  unfold regevShrinkFactor
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h.n_pos
  have hq : (0 : ℝ) < (q : ℝ) := by
    have hq2 := h.q_ge_two
    exact_mod_cast (by omega : 0 < q)
  have hα : 0 < α := h.α_pos
  positivity

/-- **Key consequence of Regev's condition `2 * √n < α * q`:**
the quantum width-shrinking factor `regevShrinkFactor n q α` is strictly less than `1`. -/
theorem regevShrinkFactor_lt_one {n q : ℕ} {α : ℝ} (h : RegevParameters n q α) :
    regevShrinkFactor n q α < 1 := by
  unfold regevShrinkFactor
  have hq : (0 : ℝ) < (q : ℝ) := by
    have hq2 := h.q_ge_two
    exact_mod_cast (by omega : 0 < q)
  have hα : 0 < α := h.α_pos
  exact (div_lt_one (mul_pos hα hq)).mpr h.smoothing_cond

/-- When `4 * √n ≤ α * q`, each quantum step shrinks the Gaussian width by at least a factor of
`1 / 2` (`r' ≤ r / 2`). -/
theorem nextGaussianWidth_le_half {n q : ℕ} {α r : ℝ} (h : RegevParameters n q α)
    (h4 : 4 * Real.sqrt (n : ℝ) ≤ α * (q : ℝ)) (hr : 0 ≤ r) :
    nextGaussianWidth n q α r ≤ r / 2 := by
  unfold nextGaussianWidth regevShrinkFactor
  have hq : (0 : ℝ) < (q : ℝ) := by
    have hq2 := h.q_ge_two
    exact_mod_cast (by omega : 0 < q)
  have hα : 0 < α := h.α_pos
  have hfac : 2 * Real.sqrt (n : ℝ) / (α * (q : ℝ)) ≤ 1 / 2 := by
    rw [div_le_iff₀ (mul_pos hα hq)]
    linarith
  calc
    r * (2 * Real.sqrt (n : ℝ) / (α * (q : ℝ))) ≤ r * (1 / 2) :=
      mul_le_mul_of_nonneg_left hfac hr
    _ = r / 2 := by ring

theorem stoppingWidth_pos {n : ℕ} [NeZero n] {q : ℕ} {α : ℝ} (h : RegevParameters n q α)
    (B : LatticeBasis n) :
    0 < stoppingWidth B α := by
  unfold stoppingWidth
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h.n_pos
  have hα : 0 < α := h.α_pos
  have hl1 : 0 < lambda1 (dualBasis B) := lambda1_pos (dualBasis B)
  positivity

/-- Regev's quantum step oracle [Regev2009, Lemma 3.14]: equipped with an average-case
`SearchLWEOracle n q α` (which solves `DualBDDInstance` at radius `bddRadius q α r` by
`solveDualBDDModQ_eq_secretCoords`), uncomputing the closest dual lattice vector in superposition
and applying the Quantum Fourier Transform over `(ZMod q)^n` maps a discrete Gaussian state of
width `r > stoppingWidth B α` to a narrower discrete Gaussian state of width
`nextGaussianWidth n q α r = r * (2 √n / (α q))`. -/
structure RegevQuantumStepOracle (n q : ℕ) (α : ℝ) where
  /-- The underlying average-case `SearchLWE` oracle used in the classical BDD step. -/
  lweOracle : SearchLWEOracle n q α
  /-- Single quantum QFT + BDD width-shrinking step from `r` to `nextGaussianWidth n q α r`. -/
  step : ∀ (B : LatticeBasis n) {r : ℝ}, stoppingWidth B α < r →
    DiscreteGaussianSuperposition B r →
    DiscreteGaussianSuperposition B (nextGaussianWidth n q α r)

/-- Iterate the quantum width-reduction step `k` times, stopping as soon as the Gaussian width
reaches `stoppingWidth B α`. -/
def iterateQuantumStep {n q : ℕ} {α : ℝ} (Q : RegevQuantumStepOracle n q α)
    (B : LatticeBasis n) :
    ℕ → ∀ (r : ℝ), DiscreteGaussianSuperposition B r →
      Σ r' : ℝ, DiscreteGaussianSuperposition B r'
  | 0, r, state => ⟨r, state⟩
  | k + 1, r, state =>
    if h : stoppingWidth B α < r then
      iterateQuantumStep Q B k (nextGaussianWidth n q α r) (Q.step B h state)
    else
      ⟨r, state⟩

/-- After `k` iterations of `iterateQuantumStep`, the resulting Gaussian width is at most
`max (stoppingWidth B α) (r * (regevShrinkFactor n q α) ^ k)`. -/
theorem iterateQuantumStep_width_le {n q : ℕ} {α : ℝ} (Q : RegevQuantumStepOracle n q α)
    (B : LatticeBasis n) :
    ∀ (k : ℕ) (r : ℝ) (state : DiscreteGaussianSuperposition B r),
      (iterateQuantumStep Q B k r state).1 ≤
        max (stoppingWidth B α) (r * (regevShrinkFactor n q α) ^ k)
  | 0, r, state => by
    simp [iterateQuantumStep]
  | k + 1, r, state => by
    unfold iterateQuantumStep
    split_ifs with h
    · have ih := iterateQuantumStep_width_le Q B k (nextGaussianWidth n q α r) (Q.step B h state)
      have heq : nextGaussianWidth n q α r * (regevShrinkFactor n q α) ^ k =
          r * (regevShrinkFactor n q α) ^ (k + 1) := by
        unfold nextGaussianWidth
        ring
      rwa [heq] at ih
    · exact le_max_of_le_left (not_lt.mp h)

/-- Because `2 * √n < α * q` implies `regevShrinkFactor n q α < 1`, there exists an iteration
count `k` after which `r₀ * (regevShrinkFactor n q α) ^ k ≤ stoppingWidth B α`. -/
theorem exists_iteration_le_stoppingWidth {n : ℕ} [NeZero n] {q : ℕ} {α : ℝ}
    (h : RegevParameters n q α) (B : LatticeBasis n) :
    ∃ k : ℕ,
      initialGaussianWidth B * (regevShrinkFactor n q α) ^ k ≤ stoppingWidth B α := by
  have hr₀ : 0 < initialGaussianWidth B := initialGaussianWidth_pos B
  have hstop : 0 < stoppingWidth B α := stoppingWidth_pos h B
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hstop hr₀) (regevShrinkFactor_lt_one h)
  exact ⟨k, le_of_lt ((lt_div_iff₀' hr₀).mp hk)⟩

/-- The number of quantum iterations required to reduce `initialGaussianWidth B` below
`stoppingWidth B α`. -/
def quantumIterationCount {n : ℕ} [NeZero n] {q : ℕ} {α : ℝ}
    (h : RegevParameters n q α) (B : LatticeBasis n) : ℕ :=
  Classical.choose (exists_iteration_le_stoppingWidth h B)

/-- The terminal discrete Gaussian state obtained after running `quantumIterationCount h B` steps
of Regev's quantum reduction. -/
def terminalGaussianState {n : ℕ} [NeZero n] {q : ℕ} {α : ℝ}
    (h : RegevParameters n q α) (Q : RegevQuantumStepOracle n q α) (B : LatticeBasis n) :
    Σ r' : ℝ, DiscreteGaussianSuperposition B r' :=
  iterateQuantumStep Q B (quantumIterationCount h B) (initialGaussianWidth B)
    (initialGaussianState B)

/-- **Width guarantee for the terminal discrete Gaussian state:**
iterating the quantum step under `RegevParameters n q α` reduces the Gaussian width to at most
`stoppingWidth B α = 2 √n / (α λ₁(B*))`. -/
theorem terminalGaussianState_width_le {n : ℕ} [NeZero n] {q : ℕ} {α : ℝ}
    (h : RegevParameters n q α) (Q : RegevQuantumStepOracle n q α) (B : LatticeBasis n) :
    (terminalGaussianState h Q B).1 ≤ stoppingWidth B α := by
  unfold terminalGaussianState
  have hle := iterateQuantumStep_width_le Q B (quantumIterationCount h B)
    (initialGaussianWidth B) (initialGaussianState B)
  have hk := Classical.choose_spec (exists_iteration_le_stoppingWidth h B)
  exact hle.trans (max_le le_rfl hk)

/-- The worst-case lattice approximation factor `γ(n, α) = 2 n / α = O(n / α)` of Regev's
quantum reduction. -/
def regevApproxFactor (n : ℕ) (α : ℝ) : ℝ :=
  2 * (n : ℝ) / α

/-- The worst-case lattice approximation factor `Õ(n / α) = 2 n (log n + 1) / α` including the
logarithmic factor from repeated Gaussian sampling. -/
def regevTildeApproxFactor (n : ℕ) (α : ℝ) : ℝ :=
  2 * (n : ℝ) * (Real.log (n : ℝ) + 1) / α

theorem one_le_regevApproxFactor {n q : ℕ} {α : ℝ} (h : RegevParameters n q α) :
    1 ≤ regevApproxFactor n α := by
  unfold regevApproxFactor
  have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h.n_pos
  have hα : 0 < α := h.α_pos
  have hα1 : α < 1 := h.α_lt_one
  rw [le_div_iff₀ hα]
  linarith

theorem regevApproxFactor_le_tilde {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα : 0 < α) :
    regevApproxFactor n α ≤ regevTildeApproxFactor n α := by
  unfold regevApproxFactor regevTildeApproxFactor
  rw [div_le_div_iff_of_pos_right hα]
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 0 ≤ n)
  nlinarith

/-- The `SIVPWitness` extracted from the terminal discrete Gaussian state of Regev's quantum
reduction on basis `B`. -/
def regevSIVPWitness {n : ℕ} [NeZero n] {q : ℕ} {α : ℝ}
    (h : RegevParameters n q α) (Q : RegevQuantumStepOracle n q α) (B : LatticeBasis n) :
    SIVPWitness B :=
  (terminalGaussianState h Q B).2.toSIVPWitness

/-- **Norm bound on `regevSIVPWitness` in terms of `λ₁(B*)`:**
the `n` linearly independent vectors produced on `B` have Euclidean norm at most
`regevApproxFactor n α / λ₁(B*) = (2 n / α) / λ₁(B*)`. -/
theorem regevSIVPWitness_normBound_le_div_lambda1_dual {n : ℕ} [NeZero n] {q : ℕ} {α : ℝ}
    (h : RegevParameters n q α) (Q : RegevQuantumStepOracle n q α) (B : LatticeBasis n) :
    (regevSIVPWitness h Q B).normBound ≤ regevApproxFactor n α / lambda1 (dualBasis B) := by
  change Real.sqrt (n : ℝ) * (terminalGaussianState h Q B).1 ≤
    regevApproxFactor n α / lambda1 (dualBasis B)
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hle := mul_le_mul_of_nonneg_left (terminalGaussianState_width_le h Q B)
    (Real.sqrt_nonneg (n : ℝ))
  have heq : Real.sqrt (n : ℝ) * stoppingWidth B α =
      regevApproxFactor n α / lambda1 (dualBasis B) := by
    unfold stoppingWidth regevApproxFactor
    have hsq : Real.sqrt (n : ℝ) * (2 * Real.sqrt (n : ℝ)) = 2 * (n : ℝ) := by
      calc
        Real.sqrt (n : ℝ) * (2 * Real.sqrt (n : ℝ)) =
            2 * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
        _ = 2 * (n : ℝ) := by rw [Real.mul_self_sqrt hn]
    rw [mul_div_assoc', hsq, div_div]
  exact hle.trans_eq heq

/-- **Regev's quantum `SIVP` solver [Regev2009, Theorem 1.1]:**
under `RegevParameters n q α` (`2 * √n < α * q`), the iterative quantum reduction produces an
`SIVPSolver` achieving approximation factor `regevApproxFactor n α = 2 n / α` on every full-rank
`n`-dimensional lattice `B`. -/
def regevSIVPSolver {n : ℕ} [NeZero n] {q : ℕ} {α : ℝ}
    (h : RegevParameters n q α) (Q : RegevQuantumStepOracle n q α) :
    SIVPSolver n (regevApproxFactor n α) where
  solve B := regevSIVPWitness h Q B
  isApprox B := by
    unfold SIVPWitness.IsApproxSolution
    have h1 := regevSIVPWitness_normBound_le_div_lambda1_dual h Q B
    have hl1 : 0 < lambda1 (dualBasis B) := lambda1_pos (dualBasis B)
    have htrans : (lambda1 (dualBasis B))⁻¹ ≤ lambdaN B :=
      (inv_le_iff_one_le_mul₀' hl1).mpr (one_le_lambda1_dualBasis_mul_lambdaN B)
    have hfac_pos : 0 ≤ regevApproxFactor n α :=
      le_trans zero_le_one (one_le_regevApproxFactor h)
    calc
      (regevSIVPWitness h Q B).normBound ≤ regevApproxFactor n α * (lambda1 (dualBasis B))⁻¹ := by
        rwa [div_eq_mul_inv] at h1
      _ ≤ regevApproxFactor n α * lambdaN B :=
        mul_le_mul_of_nonneg_left htrans hfac_pos

/-- **Regev's quantum reduction from worst-case `SIVP` to `SearchLWE` [Regev2009, Theorem 1.1]:**
on every full-rank lattice `B`, `regevSIVPSolver h Q` produces `n` linearly independent lattice
vectors of norm at most `regevApproxFactor n α * λ_n(B) = (2 n / α) * λ_n(B)`. -/
theorem regev_lwe_to_sivp {n : ℕ} [NeZero n] {q : ℕ} {α : ℝ}
    (h : RegevParameters n q α) (Q : RegevQuantumStepOracle n q α) (B : LatticeBasis n) :
    ((regevSIVPSolver h Q).solve B).IsApproxSolution (regevApproxFactor n α) :=
  (regevSIVPSolver h Q).isApprox B

/-- Corollary: `regevSIVPSolver` also satisfies the `Õ(n / α) = 2 n (log n + 1) / α`
approximation bound on every lattice `B`. -/
theorem regev_lwe_to_sivp_tilde {n : ℕ} [NeZero n] {q : ℕ} {α : ℝ}
    (h : RegevParameters n q α) (Q : RegevQuantumStepOracle n q α) (B : LatticeBasis n) :
    ((regevSIVPSolver h Q).solve B).IsApproxSolution (regevTildeApproxFactor n α) := by
  unfold SIVPWitness.IsApproxSolution
  have hsol := regev_lwe_to_sivp h Q B
  unfold SIVPWitness.IsApproxSolution at hsol
  have hle := regevApproxFactor_le_tilde h.n_pos h.α_pos
  exact hsol.trans (mul_le_mul_of_nonneg_right hle (lambdaN_pos B).le)

/-- Decision procedure for worst-case `GapSVP` obtained by running Regev's quantum `SIVP`
procedure on `dualBasis B` and comparing the resulting norm bound against `1 / d`. -/
def regevGapSVPDecider {n : ℕ} [NeZero n] {q : ℕ} {α : ℝ}
    (h : RegevParameters n q α) (Q : RegevQuantumStepOracle n q α) (d : ℝ)
    (B : LatticeBasis n) : Bool :=
  decide (1 ≤ (regevSIVPWitness h Q (dualBasis B)).normBound * d)

/-- **Regev's quantum reduction from worst-case `GapSVP` to `SearchLWE` [Regev2009, Theorem 1.1]:**
under `RegevParameters n q α` (`2 * √n < α * q`), for every distance threshold `d > 0`,
`regevGapSVPDecider h Q d` solves the worst-case promise problem
`GapSVP n (regevApproxFactor n α) d` with approximation factor `2 n / α`. -/
theorem regev_lwe_to_gapsvp {n : ℕ} [NeZero n] {q : ℕ} {α : ℝ}
    (h : RegevParameters n q α) (Q : RegevQuantumStepOracle n q α) {d : ℝ} (hd : 0 < d) :
    (GapSVP n (regevApproxFactor n α) d).SolvedBy (regevGapSVPDecider h Q d) := by
  constructor
  · intro B hByes
    rw [mem_yes_GapSVP] at hByes
    unfold regevGapSVPDecider
    rw [decide_eq_true_iff]
    have htrans : 1 ≤ lambda1 B * lambdaN (dualBasis B) :=
      one_le_lambda1_mul_lambdaN_dualBasis B
    have hln : lambdaN (dualBasis B) ≤ (regevSIVPWitness h Q (dualBasis B)).normBound :=
      (regevSIVPWitness h Q (dualBasis B)).lambdaN_le_normBound
    have hln_pos : 0 ≤ lambdaN (dualBasis B) := (lambdaN_pos (dualBasis B)).le
    calc
      (1 : ℝ) ≤ lambda1 B * lambdaN (dualBasis B) := htrans
      _ ≤ d * lambdaN (dualBasis B) := mul_le_mul_of_nonneg_right hByes hln_pos
      _ ≤ d * (regevSIVPWitness h Q (dualBasis B)).normBound :=
        mul_le_mul_of_nonneg_left hln hd.le
      _ = (regevSIVPWitness h Q (dualBasis B)).normBound * d := mul_comm _ _
  · intro B hBno
    rw [mem_no_GapSVP] at hBno
    rcases hBno with ⟨hBno, _⟩
    unfold regevGapSVPDecider
    rw [decide_eq_false_iff_not, not_le]
    have hdual := regevSIVPWitness_normBound_le_div_lambda1_dual h Q (dualBasis B)
    rw [dualBasis_dualBasis] at hdual
    have hl1 : 0 < lambda1 B := lambda1_pos B
    have h1 : (regevSIVPWitness h Q (dualBasis B)).normBound * d ≤
        (regevApproxFactor n α * d) / lambda1 B := by
      calc
        (regevSIVPWitness h Q (dualBasis B)).normBound * d ≤
            (regevApproxFactor n α / lambda1 B) * d :=
          mul_le_mul_of_nonneg_right hdual hd.le
        _ = (regevApproxFactor n α * d) / lambda1 B := div_mul_eq_mul_div _ _ _
    have h2 : (regevApproxFactor n α * d) / lambda1 B < 1 :=
      (div_lt_one hl1).mpr hBno
    exact h1.trans_lt h2

/-- **Combined worst-case-to-average-case theorem [Regev2009, Theorem 1.1]:**
for every dimension `n > 0`, modulus `q ≥ 2`, and Gaussian noise rate `0 < α < 1` satisfying
`2 * √n < α * q`, a quantum step oracle powered by `SearchLWEOracle n q α` simultaneously yields:
1. a worst-case `SIVP` solver with approximation factor `regevApproxFactor n α = 2 n / α` (and
   `regevTildeApproxFactor n α = 2 n (log n + 1) / α`), and
2. a worst-case `GapSVP` decider solving `GapSVP n (regevApproxFactor n α) d` for every `d > 0`. -/
theorem regev_lwe_to_sivp_gapsvp {n : ℕ} [NeZero n] {q : ℕ} {α : ℝ}
    (h : RegevParameters n q α) (Q : RegevQuantumStepOracle n q α) {d : ℝ} (hd : 0 < d) :
    (∀ B : LatticeBasis n, ((regevSIVPSolver h Q).solve B).IsApproxSolution
      (regevApproxFactor n α)) ∧
    (∀ B : LatticeBasis n, ((regevSIVPSolver h Q).solve B).IsApproxSolution
      (regevTildeApproxFactor n α)) ∧
    (GapSVP n (regevApproxFactor n α) d).SolvedBy (regevGapSVPDecider h Q d) :=
  ⟨regev_lwe_to_sivp h Q, regev_lwe_to_sivp_tilde h Q, regev_lwe_to_gapsvp h Q hd⟩

end

end Cslib.Crypto
