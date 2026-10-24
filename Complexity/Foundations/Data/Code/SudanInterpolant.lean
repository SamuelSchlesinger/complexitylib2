/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Code.Sudan
public import Complexity.Foundations.LinearAlgebra.KernelVector

/-!
# Sudan interpolants of least `Y`-degree by elimination

Sudan's list decoder [Sudan1997] for the Reed–Solomon code of dimension `d + 1` needs a nonzero
bivariate polynomial `Q(X, Y)` of `(1, d)`-weighted degree at most `D` vanishing at the points
`(α i, w i)` of a received word (`Cslib.Code.Sudan.IsInterpolant`). This module computes one by
linear algebra, choosing an interpolant of least `Y`-degree: for `j = 0, 1, …, D / d` it finds a
kernel vector of the interpolation matrix restricted to the monomials of `Y`-degree at most `j`
(`Cslib.LinearAlgebra.kernelVec`), and takes the first nonzero one
(`Cslib.Code.Sudan.interpolant`). When there are more monomials than points this is an interpolant
(`Cslib.Code.Sudan.isInterpolant_interpolant`), and no interpolant has smaller `Y`-degree
(`Cslib.Code.Sudan.natDegree_interpolant_le`).

Least `Y`-degree makes every polynomial `P` of degree at most `d` with more than `D` agreements a
*simple* root of `Q`, viewed as a polynomial in `Y`: if `(Y - P)²` divided `Q`, then `Q / (Y - P)`
would be an interpolant of smaller `Y`-degree. On division by `Y - P` the bound `D` on the
weighted degree drops to `D - d` (`Cslib.Code.Sudan.add_mul_add_one_le_of_mul`, an upper bound),
so `Q = (Y - P) * S` where `S(X, P(X))` is a nonzero polynomial of degree at most `D - d`
(`Cslib.Code.Sudan.exists_eq_mul_eval_ne_zero`). Simplicity is what lets the root `P` be lifted
from a single known value by Newton iteration (`Cslib.Code.henselValue_eq`).

## Main definitions

* `Cslib.Code.Sudan.monomialsUpTo`: the monomials of bounded weighted degree and bounded
  `Y`-degree.
* `Cslib.Code.Sudan.interpMatrix`: the interpolation matrix on a set of monomials.
* `Cslib.Code.Sudan.coeffsOf`: the coefficients on a set of monomials given by a vector indexed by
  its enumeration.
* `Cslib.Code.Sudan.kernelVecUpTo`: the kernel vector of the interpolation matrix on the monomials
  of `Y`-degree at most `j`.
* `Cslib.Code.Sudan.interpolantCoeffs`: the coefficients of the first nonzero kernel vector.
* `Cslib.Code.Sudan.interpolant`: an interpolant of least `Y`-degree, by elimination.

## Main results

* `Cslib.Code.Sudan.isInterpolant_interpolant`: it is an interpolant.
* `Cslib.Code.Sudan.natDegree_interpolant_le`: it has least `Y`-degree.
* `Cslib.Code.Sudan.add_mul_add_one_le_of_mul`: division by `Y - P` lowers the weighted degree
  by `d`.
* `Cslib.Code.Sudan.exists_eq_mul_eval_ne_zero`: polynomials with large agreement are simple roots
  of an interpolant of least `Y`-degree.

## References

* [M. Sudan, *Decoding of Reed Solomon codes beyond the error-correction bound*][Sudan1997]
* [M. Sudan, L. Trevisan, S. Vadhan, *Pseudorandom generators without the XOR lemma*]
  [SudanTrevisanVadhan2001]
-/

@[expose] public section

namespace Cslib.Code.Sudan

open Finset Polynomial Cslib.LinearAlgebra
open scoped Polynomial.Bivariate

variable {F ι : Type*} [Field F]

/-! ### Bivariate polynomials from coefficients -/

/-- `bivariateOf M c` depends only on the values of `c` on `M`. -/
theorem bivariateOf_congr {M : Finset (ℕ × ℕ)} {c c' : ℕ × ℕ → F} (h : ∀ m ∈ M, c m = c' m) :
    bivariateOf M c = bivariateOf M c' :=
  sum_congr rfl fun m hm => by rw [h m hm]

/-- A bivariate polynomial whose monomials lie in `M` is `bivariateOf M` of its coefficients. -/
theorem eq_bivariateOf {Q : F[X][Y]} {M : Finset (ℕ × ℕ)}
    (h : ∀ a b, (Q.coeff b).coeff a ≠ 0 → (a, b) ∈ M) :
    Q = bivariateOf M fun m => (Q.coeff m.2).coeff m.1 := by
  ext b a
  rw [coeff_coeff_bivariateOf]
  split_ifs with hab
  · rfl
  · by_contra hne
    exact hab (h a b hne)

/-! ### The interpolation matrix -/

/-- The monomials of `(1, d)`-weighted degree at most `D` and `Y`-degree at most `j`. -/
def monomialsUpTo (d D j : ℕ) : Finset (ℕ × ℕ) := (monomials d D).filter fun m => m.2 ≤ j

variable [Fintype ι]

/-- The interpolation matrix: its rows are the points `(α i, w i)` (enumerated by
`Fintype.equivFin ι`), its columns the monomials of `M` (enumerated by `M.equivFin`), and its
entries the values of the monomials at the points. -/
noncomputable def interpMatrix (α w : ι → F) (M : Finset (ℕ × ℕ)) :
    Fin (Fintype.card ι) → Fin #M → F :=
  fun t m => α ((Fintype.equivFin ι).symm t) ^ (M.equivFin.symm m : ℕ × ℕ).1 *
    w ((Fintype.equivFin ι).symm t) ^ (M.equivFin.symm m : ℕ × ℕ).2

/-- The coefficients on `M` given by a vector indexed by the enumeration of `M`, and zero
elsewhere. -/
noncomputable def coeffsOf (M : Finset (ℕ × ℕ)) (u : Fin #M → F) (m : ℕ × ℕ) : F :=
  if h : m ∈ M then u (M.equivFin ⟨m, h⟩) else 0

/-- The product of a row of the interpolation matrix with a vector `u` is the value at the row's
point of the polynomial with coefficients `u`. -/
theorem interpMatrix_dotProduct (α w : ι → F) (M : Finset (ℕ × ℕ)) (u : Fin #M → F)
    (i : ι) :
    interpMatrix α w M (Fintype.equivFin ι i) ⬝ᵥ u =
      (bivariateOf M (coeffsOf M u)).evalEval (α i) (w i) := by
  rw [evalEval_bivariateOf, dotProduct]
  have h := Equiv.sum_comp M.equivFin.symm
    (fun m : M => α i ^ (m : ℕ × ℕ).1 * w i ^ (m : ℕ × ℕ).2 * u (M.equivFin m))
  simp only [Equiv.apply_symm_apply] at h
  rw [← Finset.sum_coe_sort M (fun m => coeffsOf M u m * α i ^ m.1 * w i ^ m.2)]
  simp only [interpMatrix, Equiv.symm_apply_apply]
  rw [h]
  refine Fintype.sum_congr _ _ fun m => ?_
  simp only [coeffsOf, Finset.coe_mem, dite_true, Subtype.coe_eta]
  ring

/-! ### The interpolant of least `Y`-degree -/

variable [DecidableEq F]

/-- The kernel vector of the interpolation matrix on the monomials of `Y`-degree at most `j`. -/
noncomputable def kernelVecUpTo (α w : ι → F) (d D j : ℕ) : Fin #(monomialsUpTo d D j) → F :=
  kernelVec (interpMatrix α w (monomialsUpTo d D j))

/-- The coefficients of the interpolant: those of the first nonzero kernel vector among
`j = 0, 1, …, D / d`. -/
noncomputable def interpolantCoeffs (α w : ι → F) (d D : ℕ) : ℕ × ℕ → F :=
  ∑ j : Fin (D / d + 1),
    firstFlags (fun j : Fin (D / d + 1) => if kernelVecUpTo α w d D j = 0 then (0 : F) else 1) j •
      coeffsOf (monomialsUpTo d D j) (kernelVecUpTo α w d D j)

/-- **An interpolant of least `Y`-degree**, computed by elimination. -/
noncomputable def interpolant (α w : ι → F) (d D : ℕ) : F[X][Y] :=
  bivariateOf (monomials d D) (interpolantCoeffs α w d D)

omit [Fintype ι] [DecidableEq F] in
/-- The monomials of an interpolant lie in `monomials d D`. -/
private theorem mem_monomials_of_isInterpolant {α w : ι → F} {d D : ℕ} (hd : 1 ≤ d)
    {Q : F[X][Y]} (hQ : IsInterpolant α w (d + 1) D Q) {a b : ℕ}
    (hab : (Q.coeff b).coeff a ≠ 0) : (a, b) ∈ monomials d D := by
  have h := hQ.weightedDegree_le a b hab
  rw [Nat.add_sub_cancel] at h
  refine mem_monomials.2 ⟨by omega, ?_, h⟩
  nlinarith

/-- An interpolant of `Y`-degree at most `j` gives a nonzero kernel vector on the monomials of
`Y`-degree at most `j`. -/
private theorem kernelVecUpTo_ne_zero {α w : ι → F} {d D : ℕ} (hd : 1 ≤ d) {Q : F[X][Y]}
    (hQ : IsInterpolant α w (d + 1) D Q) {j : ℕ} (hj : Q.natDegree ≤ j) :
    kernelVecUpTo α w d D j ≠ 0 := by
  have hsupp : ∀ a b, (Q.coeff b).coeff a ≠ 0 → (a, b) ∈ monomialsUpTo d D j := fun a b hab =>
    mem_filter.2 ⟨mem_monomials_of_isInterpolant hd hQ hab,
      (le_natDegree_of_ne_zero fun h => hab (by rw [h, coeff_zero])).trans hj⟩
  refine kernelVec_ne_zero _ ⟨fun m =>
    (Q.coeff ((monomialsUpTo d D j).equivFin.symm m : ℕ × ℕ).2).coeff
      ((monomialsUpTo d D j).equivFin.symm m : ℕ × ℕ).1, ?_, funext fun t => ?_⟩
  · obtain ⟨b, hb⟩ : ∃ b, Q.coeff b ≠ 0 := by
      by_contra h
      push Not at h
      exact hQ.ne_zero (Polynomial.ext fun b => by rw [h b, coeff_zero])
    obtain ⟨a, ha⟩ : ∃ a, (Q.coeff b).coeff a ≠ 0 := by
      by_contra h
      push Not at h
      exact hb (Polynomial.ext fun a => by rw [h a, coeff_zero])
    intro h0
    have := congrFun h0 ((monomialsUpTo d D j).equivFin ⟨(a, b), hsupp a b ha⟩)
    simp only [Equiv.symm_apply_apply, Pi.zero_apply] at this
    exact ha this
  · change interpMatrix α w (monomialsUpTo d D j) t ⬝ᵥ _ = 0
    obtain ⟨i, rfl⟩ := (Fintype.equivFin ι).surjective t
    rw [interpMatrix_dotProduct, ← hQ.evalEval_eq_zero i]
    congr 1
    refine (bivariateOf_congr fun m hm => ?_).trans (eq_bivariateOf hsupp).symm
    simp only [coeffsOf, dite_eq_left hm, Equiv.symm_apply_apply]

/-- The interpolant is `bivariateOf` of the first nonzero kernel vector, at an index `j` below
which all kernel vectors vanish. -/
private theorem exists_interpolant_eq {α w : ι → F} {d D : ℕ} (hd : 1 ≤ d)
    (hn : Fintype.card ι < #(monomials d D)) :
    ∃ j : Fin (D / d + 1), kernelVecUpTo α w d D j ≠ 0 ∧
      (∀ i < j, kernelVecUpTo α w d D i = 0) ∧
      interpolantCoeffs α w d D = coeffsOf (monomialsUpTo d D j) (kernelVecUpTo α w d D j) := by
  have hn' : Fintype.card ι < #(monomials (d + 1 - 1) D) := by rwa [Nat.add_sub_cancel]
  obtain ⟨Q₀, hQ₀⟩ := exists_isInterpolant α w hn'
  have hdeg : Q₀.natDegree ≤ D / d := by
    have := hQ₀.natDegree_mul_sub_one_le
    rw [Nat.add_sub_cancel] at this
    exact (Nat.le_div_iff_mul_le hd).2 this
  obtain h | h := sum_firstFlags_smul_eq
      (fun j : Fin (D / d + 1) => if kernelVecUpTo α w d D j = 0 then (0 : F) else 1)
      (fun j => coeffsOf (monomialsUpTo d D j) (kernelVecUpTo α w d D j))
  · exfalso
    have := congrFun h.1 ⟨Q₀.natDegree, Nat.lt_succ_of_le hdeg⟩
    simp only [Pi.zero_apply, ite_eq_left_iff, one_ne_zero, imp_false, not_not] at this
    exact kernelVecUpTo_ne_zero hd hQ₀ le_rfl this
  · obtain ⟨j, hj, hlt, hsum⟩ := h
    refine ⟨j, fun h => hj (by simp [h]), fun i hi => ?_, hsum⟩
    have := hlt i hi
    simpa using this

/-- **The elimination interpolant is an interpolant.** With `d ≥ 1` and more monomials of
`(1, d)`-weighted degree at most `D` than points, `interpolant α w d D` is a Sudan interpolant for
the dimension `d + 1`. -/
theorem isInterpolant_interpolant (α w : ι → F) {d D : ℕ} (hd : 1 ≤ d)
    (hn : Fintype.card ι < #(monomials d D)) :
    IsInterpolant α w (d + 1) D (interpolant α w d D) := by
  obtain ⟨j, hj, -, hcoeffs⟩ := exists_interpolant_eq (α := α) (w := w) hd hn
  set M := monomialsUpTo d D (j : ℕ)
  have hsub : M ⊆ monomials d D := filter_subset _ _
  have hcoeff : ∀ a b, ((interpolant α w d D).coeff b).coeff a =
      coeffsOf M (kernelVecUpTo α w d D j) (a, b) := by
    intro a b
    rw [interpolant, coeff_coeff_bivariateOf, hcoeffs]
    split_ifs with h
    · rfl
    · simp only [coeffsOf]
      rw [dite_eq_right fun h' => absurd (hsub h') h]
  refine ⟨fun h0 => hj ?_, fun a b hab => ?_, fun i => ?_⟩
  · funext m
    have := hcoeff (M.equivFin.symm m : ℕ × ℕ).1 (M.equivFin.symm m : ℕ × ℕ).2
    rw [h0] at this
    simp only [coeff_zero, coeffsOf, Prod.mk.eta, coe_mem, dite_eq_left, Subtype.coe_eta,
      Equiv.apply_symm_apply] at this
    exact this.symm
  · rw [hcoeff] at hab
    simp only [coeffsOf] at hab
    split_ifs at hab with h
    · rw [Nat.add_sub_cancel]
      exact (mem_monomials.1 (hsub h)).2.2
    · exact absurd rfl hab
  · have hzero : interpMatrix α w M (Fintype.equivFin ι i) ⬝ᵥ kernelVecUpTo α w d D j = 0 :=
      congrFun (mulVec_kernelVec _) _
    rw [interpMatrix_dotProduct, evalEval_bivariateOf] at hzero
    rw [interpolant, hcoeffs, evalEval_bivariateOf, ← hzero]
    refine (Finset.sum_subset hsub fun m _ hm => ?_).symm
    simp only [coeffsOf]
    rw [dite_eq_right fun h => absurd h hm, zero_mul, zero_mul]

/-- **The elimination interpolant has least `Y`-degree** among all Sudan interpolants. -/
theorem natDegree_interpolant_le (α w : ι → F) {d D : ℕ} (hd : 1 ≤ d)
    (hn : Fintype.card ι < #(monomials d D)) {Q : F[X][Y]}
    (hQ : IsInterpolant α w (d + 1) D Q) :
    (interpolant α w d D).natDegree ≤ Q.natDegree := by
  obtain ⟨j, -, hlt, hcoeffs⟩ := exists_interpolant_eq (α := α) (w := w) hd hn
  have hdeg : Q.natDegree ≤ D / d := by
    have := hQ.natDegree_mul_sub_one_le
    rw [Nat.add_sub_cancel] at this
    exact (Nat.le_div_iff_mul_le hd).2 this
  have hj : (j : ℕ) ≤ Q.natDegree := by
    by_contra h
    push Not at h
    exact kernelVecUpTo_ne_zero hd hQ le_rfl
      (hlt ⟨Q.natDegree, Nat.lt_succ_of_le hdeg⟩ (Fin.lt_def.2 h))
  refine (natDegree_le_iff_coeff_eq_zero.2 fun b hb => ?_).trans hj
  ext a
  rw [interpolant, coeff_coeff_bivariateOf, hcoeffs, coeff_zero]
  split_ifs
  · simp only [coeffsOf]
    split_ifs with h
    · exact absurd (mem_filter.1 h).2 (not_le.2 hb)
    · rfl
  · rfl

/-! ### Simplicity of the roots -/

omit [Fintype ι] [DecidableEq F] in
/-- **Division by `Y - P` lowers the weighted degree bound by `d`.** If `P` has degree at most `d`
and every monomial of `(Y - P) * S` has `(1, d)`-weighted degree at most `D`, then every monomial
`X ^ a * Y ^ b` of `S` has `a + d * (b + 1) ≤ D`. -/
theorem add_mul_add_one_le_of_mul {d D : ℕ} {P : F[X]} (hP : P.natDegree ≤ d) {S : F[X][Y]}
    (h : ∀ a b, (((Y - C P) * S).coeff b).coeff a ≠ 0 → a + d * b ≤ D) :
    ∀ a b, (S.coeff b).coeff a ≠ 0 → a + d * (b + 1) ≤ D := by
  classical
  -- the monomials of `S`
  let supp : Finset (ℕ × ℕ) := S.support.biUnion fun b => (S.coeff b).support.image (·, b)
  have hmem : ∀ a b, (S.coeff b).coeff a ≠ 0 ↔ (a, b) ∈ supp := by
    intro a b
    simp only [supp, mem_biUnion, mem_image, mem_support_iff, Prod.mk.injEq]
    constructor
    · intro hab
      exact ⟨b, fun h => hab (by rw [h, coeff_zero]), a, hab, rfl, rfl⟩
    · rintro ⟨b', -, a', ha', rfl, rfl⟩
      exact ha'
  intro a b hab
  have hne : supp.Nonempty := ⟨(a, b), (hmem a b).1 hab⟩
  -- the largest weighted degree, and the largest `Y`-degree attaining it
  set M₀ := supp.sup' hne fun p => p.1 + d * p.2
  have hle : ∀ p ∈ supp, p.1 + d * p.2 ≤ M₀ := fun p hp => le_sup' (fun p => p.1 + d * p.2) hp
  have htop : (supp.filter fun p => p.1 + d * p.2 = M₀).Nonempty := by
    obtain ⟨p, hp, hpeq⟩ := exists_mem_eq_sup' hne fun p => p.1 + d * p.2
    exact ⟨p, mem_filter.2 ⟨hp, hpeq.symm⟩⟩
  obtain ⟨⟨a₀, b₀⟩, hp₀, hb₀⟩ := exists_mem_eq_sup' htop Prod.snd
  obtain ⟨hp₀, hM₀⟩ := mem_filter.1 hp₀
  have hbmax : ∀ p ∈ supp, p.1 + d * p.2 = M₀ → p.2 ≤ b₀ := fun p hp hpM => by
    rw [show b₀ = (a₀, b₀).2 from rfl, ← hb₀]
    exact le_sup' Prod.snd (mem_filter.2 ⟨hp, hpM⟩)
  -- the coefficient of `X ^ a₀ * Y ^ (b₀ + 1)` in `(Y - P) * S`
  have hcoeff : (((Y - C P) * S).coeff (b₀ + 1)).coeff a₀ ≠ 0 := by
    rw [mul_comm, coeff_mul_X_sub_C, coeff_sub, mul_comm, coeff_mul]
    have hzero : ∑ x ∈ antidiagonal a₀, P.coeff x.1 * (S.coeff (b₀ + 1)).coeff x.2 = 0 := by
      refine sum_eq_zero fun ⟨i, j⟩ hij => ?_
      rw [mem_antidiagonal] at hij
      by_cases hPi : P.coeff i = 0
      · rw [hPi, zero_mul]
      by_cases hSj : (S.coeff (b₀ + 1)).coeff j = 0
      · rw [hSj, mul_zero]
      exfalso
      have hi : i ≤ d := (le_natDegree_of_ne_zero hPi).trans hP
      have hj := hle (j, b₀ + 1) ((hmem _ _).1 hSj)
      have hjM : j + d * (b₀ + 1) = M₀ := by
        simp only at hj
        rw [← hM₀] at hj ⊢
        simp only at hj ⊢
        nlinarith
      have := hbmax (j, b₀ + 1) ((hmem _ _).1 hSj) hjM
      simp only at this
      omega
    rw [hzero, sub_zero]
    exact (hmem a₀ b₀).2 hp₀
  have hD := h a₀ (b₀ + 1) hcoeff
  have hab' := hle (a, b) ((hmem a b).1 hab)
  simp only at hab' hM₀
  nlinarith

omit [Fintype ι] [DecidableEq F] in
/-- The value at `(x, y)` of `(Y - P) * S`. -/
private theorem evalEval_X_sub_C_mul (P : F[X]) (S : F[X][Y]) (x y : F) :
    ((Y - C P) * S).evalEval x y = (y - P.eval x) * S.evalEval x y := by
  rw [evalEval_mul, evalEval_sub, evalEval_X, evalEval_C]

/-- **Large agreement gives simple roots.** Let `Q` be a Sudan interpolant of least `Y`-degree for
the dimension `d + 1`, with distinct points. If `P` has degree at most `d` and agrees with the
received word at more than `D` points, then `Q = (Y - P) * S` where `S(X, P(X))` is a nonzero
polynomial of degree at most `D - d`. -/
theorem exists_eq_mul_eval_ne_zero {α w : ι → F} {d D : ℕ} (hα : Function.Injective α)
    {Q : F[X][Y]} (hQ : IsInterpolant α w (d + 1) D Q)
    (hmin : ∀ Q', IsInterpolant α w (d + 1) D Q' → Q.natDegree ≤ Q'.natDegree) {P : F[X]}
    (hP : P.natDegree ≤ d) (hagree : D < #{i | P.eval (α i) = w i}) :
    ∃ S : F[X][Y], Q = (Y - C P) * S ∧ S.eval P ≠ 0 ∧ (S.eval P).natDegree ≤ D - d := by
  have hPdeg : P.degree < (d + 1 : ℕ) := by
    refine degree_le_natDegree.trans_lt ?_
    exact_mod_cast Nat.lt_succ_of_le hP
  obtain ⟨S, rfl⟩ := hQ.X_sub_C_dvd hα hPdeg hagree
  have hwd := add_mul_add_one_le_of_mul hP fun a b hab => by
    have := hQ.weightedDegree_le a b hab
    rwa [Nat.add_sub_cancel] at this
  have hS0 : S ≠ 0 := fun h => hQ.ne_zero (by rw [h, mul_zero])
  refine ⟨S, rfl, fun hSP => ?_, natDegree_eval_le_of_weighted hP fun a b hab => by
    have := hwd a b hab
    rw [mul_add, mul_one] at this
    omega⟩
  -- otherwise `S` is an interpolant of smaller `Y`-degree
  obtain ⟨S₂, rfl⟩ := dvd_iff_isRoot.2 hSP
  have hS : IsInterpolant α w (d + 1) D ((Y - C P) * S₂) := by
    refine ⟨hS0, fun a b hab => ?_, fun i => ?_⟩
    · have := hwd a b hab
      rw [Nat.add_sub_cancel]
      nlinarith
    · have h := hQ.evalEval_eq_zero i
      rw [evalEval_X_sub_C_mul, evalEval_X_sub_C_mul] at h
      rw [evalEval_X_sub_C_mul]
      by_cases hi : w i - P.eval (α i) = 0
      · rw [hi, zero_mul]
      · have h' := mul_eq_zero.1 h
        rcases h' with h' | h'
        · exact absurd h' hi
        · exact h'
  have hmon : (Y - C P).Monic := monic_X_sub_C P
  have := hmin _ hS
  rw [hmon.natDegree_mul' (by simpa using hS0), natDegree_X_sub_C] at this
  omega

end Cslib.Code.Sudan
