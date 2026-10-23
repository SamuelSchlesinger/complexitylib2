/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Code.ReedSolomon
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Sudan's list decoder for Reed–Solomon codes

Let `w : ι → F` be a received word and let `α` be distinct evaluation points. Sudan's algorithm
[Sudan1997], [GuruswamiRudraSudan2019] lists the polynomials `P` of degree less than `k` whose
values agree with `w` at more than `D` points, for a parameter `D`. It interpolates: it finds a
nonzero bivariate polynomial `Q(X, Y)` of `(1, k - 1)`-weighted degree at most `D`, that is with
`a + (k - 1) * b ≤ D` for each of its monomials `X ^ a * Y ^ b`, that vanishes at the `n` points
`(α i, w i)` (`Cslib.Code.Sudan.IsInterpolant`). Such a `Q` is a nonzero solution of `n` linear
equations in its coefficients, so it exists as soon as there are more than `n` monomials of
weighted degree at most `D` (`Cslib.Code.Sudan.exists_isInterpolant`); for `k ≥ 2` there are at
least `(D + 1) * (D + 2) / (2 * (k - 1))` of them
(`Cslib.Code.Sudan.add_one_mul_add_two_le_two_mul_mul_card_monomials`). If `P` has degree less
than `k`, then `Q(X, P(X))` has degree at most `D` and vanishes at every point where `P` agrees
with `w`; when there are more than `D` of them it is zero, so `Y - P(X)` divides `Q(X, Y)`
(`Cslib.Code.Sudan.IsInterpolant.X_sub_C_dvd`): `P` is a root of `Q` viewed as a polynomial in `Y`
over `F[X]`. The number of such roots is at most the `Y`-degree of `Q`, which is at most
`D / (k - 1)` for `k ≥ 2`.

The decoder `Cslib.Code.sudan` returns the roots `P` of an interpolant `Q` that have degree less
than `k` and agree with `w` at more than `D` points. With distinct points and more than `n`
monomials, its list consists of exactly those polynomials (`Cslib.Code.mem_sudan_iff`), and its
length `L` always satisfies `L * (k - 1) ≤ D` (`Cslib.Code.card_sudan_mul_le`). For `k ≥ 2` and
`2 * (k - 1) * n < (D + 1) * (D + 2)`, this list decodes the Reed–Solomon code of dimension `k`
from agreement `D + 1 ≈ √(2 * (k - 1) * n)` (`Cslib.Code.mem_sudan_iff_of_lt`), and at most
`D / (k - 1)` codewords have that agreement with any word
(`Cslib.Code.ncard_sep_reedSolomon_mul_le`). Unique decoding needs agreement `(n + k) / 2`, so this
goes beyond half the minimum distance when the rate `k / n` is small: asymptotically, below
`3 - 2 * √2 ≈ 0.17`.

This module proves the correctness of the decoder only: `Cslib.Code.sudan` chooses an interpolant
noncomputably and takes its roots, which in the literature are found by solving a linear system and
factoring bivariate polynomials in polynomial time; no running time is formalized.

## Main definitions

* `Cslib.Code.Sudan.monomials`: the monomials of bounded weighted degree.
* `Cslib.Code.Sudan.bivariateOf`: the bivariate polynomial with given coefficients on a set of
  monomials.
* `Cslib.Code.Sudan.IsInterpolant`: the bivariate interpolants of a received word.
* `Cslib.Code.sudan`: Sudan's list decoder.

## Main results

* `Cslib.Code.Sudan.exists_isInterpolant`: interpolants exist when there are more than `n`
  monomials.
* `Cslib.Code.Sudan.add_one_mul_add_two_le_two_mul_mul_card_monomials`: counting the monomials.
* `Cslib.Code.Sudan.IsInterpolant.eval_eq_zero`, `Cslib.Code.Sudan.IsInterpolant.X_sub_C_dvd`:
  root containment, the polynomials with large agreement are roots of every interpolant.
* `Cslib.Code.Sudan.IsInterpolant.natDegree_mul_sub_one_le`: the `Y`-degree of an interpolant.
* `Cslib.Code.mem_sudan_iff`, `Cslib.Code.mem_sudan_iff_of_lt`: the decoder lists exactly the
  polynomials with large agreement.
* `Cslib.Code.card_sudan_mul_le`: the decoder lists at most `D / (k - 1)` polynomials.
* `Cslib.Code.exists_mem_sudan_of_mem_reedSolomon`: list decoding of Reed–Solomon codes.
* `Cslib.Code.ncard_sep_reedSolomon_mul_le`: few Reed–Solomon codewords have large agreement with
  a word.

## References

* [M. Sudan, *Decoding of Reed Solomon codes beyond the error-correction bound*][Sudan1997]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*]
  [GuruswamiRudraSudan2019]
-/

@[expose] public section

namespace Cslib.Code

open Finset Polynomial
open scoped Polynomial.Bivariate

variable {F ι : Type*} [Field F]

namespace Sudan

/-- The exponents `(a, b)` with `a, b ≤ D` of the monomials `X ^ a * Y ^ b` of `(1, w)`-weighted
degree `a + w * b` at most `D`. For `w ≥ 1` the bound `b ≤ D` holds for all of them. -/
def monomials (w D : ℕ) : Finset (ℕ × ℕ) :=
  {ab ∈ range (D + 1) ×ˢ range (D + 1) | ab.1 + w * ab.2 ≤ D}

theorem mem_monomials {w D : ℕ} {ab : ℕ × ℕ} :
    ab ∈ monomials w D ↔ ab.1 ≤ D ∧ ab.2 ≤ D ∧ ab.1 + w * ab.2 ≤ D := by
  simp only [monomials, mem_filter, mem_product, mem_range, Nat.lt_succ_iff, and_assoc]

/-- `∑ j < n, 2 * (j + 1) = n * (n + 1)`. -/
private theorem sum_range_two_mul_add_one (n : ℕ) :
    ∑ j ∈ range n, 2 * (j + 1) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    ring

/-- **Counting monomials.** For `w ≥ 1` there are at least `(D + 1) * (D + 2) / (2 * w)` monomials
of `(1, w)`-weighted degree at most `D`: for each `j ≤ D` there are `j / w + 1 ≥ (j + 1) / w` of
weighted degree exactly `j`. -/
theorem add_one_mul_add_two_le_two_mul_mul_card_monomials {w : ℕ} (hw : 1 ≤ w) (D : ℕ) :
    (D + 1) * (D + 2) ≤ 2 * w * #(monomials w D) := by
  -- the monomials of weighted degree `j`
  let fiber : ℕ → Finset (ℕ × ℕ) := fun j => {ab ∈ monomials w D | ab.1 + w * ab.2 = j}
  have hcard : #(monomials w D) = ∑ j ∈ range (D + 1), #(fiber j) :=
    card_eq_sum_card_fiberwise fun ab hab =>
      mem_range.2 (Nat.lt_succ_of_le (mem_monomials.1 hab).2.2)
  have hfiber (j : ℕ) (hj : j ∈ range (D + 1)) : j / w + 1 ≤ #(fiber j) := by
    have hjD := Nat.lt_succ_iff.1 (mem_range.1 hj)
    calc j / w + 1 = #((range (j / w + 1)).image fun b => (j - w * b, b)) := by
          rw [card_image_of_injective _ fun b b' h => (Prod.ext_iff.1 h).2, card_range]
      _ ≤ #(fiber j) := by
          refine card_le_card fun ab hab => ?_
          obtain ⟨b, hb, rfl⟩ := mem_image.1 hab
          have hb : w * b ≤ j :=
            (Nat.mul_le_mul_left w (Nat.lt_succ_iff.1 (mem_range.1 hb))).trans (Nat.mul_div_le j w)
          have hbj : b ≤ j := (Nat.le_mul_of_pos_left b hw).trans hb
          refine mem_filter.2 ⟨mem_monomials.2 ⟨?_, ?_, ?_⟩, ?_⟩ <;> dsimp only <;> omega
  calc (D + 1) * (D + 2) = ∑ j ∈ range (D + 1), 2 * (j + 1) := (sum_range_two_mul_add_one _).symm
    _ ≤ ∑ j ∈ range (D + 1), 2 * w * #(fiber j) := by
        refine sum_le_sum fun j hj => ?_
        rw [mul_assoc]
        exact Nat.mul_le_mul_left 2 ((Nat.lt_mul_div_succ j hw).trans_le
          (Nat.mul_le_mul_left w (hfiber j hj)))
    _ = 2 * w * #(monomials w D) := by rw [← mul_sum, hcard]

/-- `Q` is a *Sudan interpolant* for the received word `w` with evaluation points `α`, dimension
`k` and weighted degree `D`: a nonzero bivariate polynomial of `(1, k - 1)`-weighted degree at most
`D` that vanishes at the points `(α i, w i)`. -/
structure IsInterpolant (α w : ι → F) (k D : ℕ) (Q : F[X][Y]) : Prop where
  /-- The interpolant is nonzero. -/
  ne_zero : Q ≠ 0
  /-- Every monomial `X ^ a * Y ^ b` of `Q` has `(1, k - 1)`-weighted degree `a + (k - 1) * b` at
  most `D`. -/
  weightedDegree_le : ∀ a b, (Q.coeff b).coeff a ≠ 0 → a + (k - 1) * b ≤ D
  /-- The interpolant vanishes at the points `(α i, w i)`. -/
  evalEval_eq_zero : ∀ i, Q.evalEval (α i) (w i) = 0

/-- The bivariate polynomial with coefficient `c m` at `X ^ m.1 * Y ^ m.2` for `m ∈ M`. -/
noncomputable def bivariateOf (M : Finset (ℕ × ℕ)) (c : ℕ × ℕ → F) : F[X][Y] :=
  ∑ m ∈ M, monomial m.2 (monomial m.1 (c m))

/-- The coefficient of `X ^ a * Y ^ b` in `bivariateOf M c` is `c (a, b)` when `(a, b) ∈ M`, and
zero otherwise. -/
@[simp]
theorem coeff_coeff_bivariateOf (M : Finset (ℕ × ℕ)) (c : ℕ × ℕ → F) (a b : ℕ) :
    ((bivariateOf M c).coeff b).coeff a = if (a, b) ∈ M then c (a, b) else 0 := by
  classical
  simp only [bivariateOf, finsetSum_coeff]
  rw [Finset.sum_congr rfl fun m _ => (?_ :
    ((monomial m.2 (monomial m.1 (c m))).coeff b).coeff a = if (a, b) = m then c m else 0)]
  · exact Finset.sum_ite_eq M (a, b) c
  · obtain ⟨a', b'⟩ := m
    simp only [coeff_monomial, Prod.mk.injEq]
    by_cases hb : b' = b
    · subst hb
      by_cases ha : a' = a
      · subst ha
        simp
      · simp [coeff_monomial, ha, Ne.symm ha]
    · simp [hb, Ne.symm hb]

/-- The value of `bivariateOf M c` at `(x, y)` is `∑ m ∈ M, c m * x ^ m.1 * y ^ m.2`. -/
theorem evalEval_bivariateOf (M : Finset (ℕ × ℕ)) (c : ℕ × ℕ → F) (x y : F) :
    (bivariateOf M c).evalEval x y = ∑ m ∈ M, c m * x ^ m.1 * y ^ m.2 := by
  simp only [bivariateOf, evalEval_finsetSum]
  refine sum_congr rfl fun m _ => ?_
  simp [evalEval, eval_monomial, mul_assoc]

variable {α w : ι → F} {k D : ℕ} {Q : F[X][Y]}

/-- Evaluating `Q(X, P(X))` at `x` evaluates `Q` at `(x, P(x))`. -/
theorem _root_.Polynomial.eval_eval_eq_evalEval {R : Type*} [CommSemiring R] (Q : R[X][Y])
    (P : R[X]) (x : R) : (Q.eval P).eval x = Q.evalEval x (P.eval x) := by
  rw [← map_evalRingHom_eval, eval_map]
  exact (hom_eval₂ Q (RingHom.id _) (evalRingHom x) P).trans (by rw [RingHom.comp_id]; rfl)

/-- Substituting `Y = P(X)`, with `P` of degree at most `d`, into a bivariate polynomial whose
monomials have `(1, d)`-weighted degree at most `E` gives a polynomial of degree at most `E`. -/
theorem natDegree_eval_le_of_weighted {d E : ℕ} {S : F[X][Y]} {P : F[X]} (hP : P.natDegree ≤ d)
    (hS : ∀ a b, (S.coeff b).coeff a ≠ 0 → a + d * b ≤ E) : (S.eval P).natDegree ≤ E := by
  rw [eval_eq_sum_range]
  refine natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
  rcases eq_or_ne (S.coeff b) 0 with h0 | h0
  · simp [h0]
  have := hS _ b (leadingCoeff_ne_zero.2 h0)
  calc (S.coeff b * P ^ b).natDegree ≤ (S.coeff b).natDegree + b * P.natDegree :=
        natDegree_mul_le.trans (Nat.add_le_add_left natDegree_pow_le _)
    _ ≤ (S.coeff b).natDegree + d * b := by
        rw [mul_comm d]
        exact Nat.add_le_add_left (Nat.mul_le_mul_left b hP) _
    _ ≤ E := this

/-- The `Y`-degree of a Sudan interpolant: `deg_Y Q * (k - 1) ≤ D`. -/
theorem IsInterpolant.natDegree_mul_sub_one_le (hQ : IsInterpolant α w k D Q) :
    Q.natDegree * (k - 1) ≤ D := by
  have hlead : Q.coeff Q.natDegree ≠ 0 := leadingCoeff_ne_zero.2 hQ.ne_zero
  have := hQ.weightedDegree_le _ _ (leadingCoeff_ne_zero.2 hlead)
  rw [mul_comm]
  omega

/-- If `P` has degree less than `k`, then `Q(X, P(X))` has degree at most `D`. -/
private theorem IsInterpolant.natDegree_eval_le (hQ : IsInterpolant α w k D Q) {P : F[X]}
    (hP : P.degree < k) : (Q.eval P).natDegree ≤ D := by
  refine natDegree_eval_le_of_weighted (d := k - 1) ?_ hQ.weightedDegree_le
  rcases eq_or_ne P 0 with rfl | hP0
  · simp
  · have := (natDegree_lt_iff_degree_lt hP0).2 hP
    omega

variable [Fintype ι]

/-- **Interpolation.** If there are more than `n` monomials of `(1, k - 1)`-weighted degree at most
`D`, every received word has a Sudan interpolant: the `n` conditions `Q (α i, w i) = 0` are linear
in the coefficients of `Q`. -/
theorem exists_isInterpolant (α w : ι → F)
    (hn : Fintype.card ι < #(monomials (k - 1) D)) : ∃ Q, IsInterpolant α w k D Q := by
  classical
  let M := monomials (k - 1) D
  let A : Matrix ι M F := Matrix.of fun i m => α i ^ m.1.1 * w i ^ m.1.2
  have hker : LinearMap.ker A.mulVecLin ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by
      rwa [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
        Fintype.card_coe])
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hker
  obtain ⟨m, hm⟩ := Function.ne_iff.1 hc0
  let c' : ℕ × ℕ → F := fun m' => if h : m' ∈ M then c ⟨m', h⟩ else 0
  refine ⟨bivariateOf M c', fun h => hm ?_, fun a b hab => ?_, fun i => ?_⟩
  · have := coeff_coeff_bivariateOf M c' m.1.1 m.1.2
    rw [h] at this
    simpa [c', m.2] using this.symm
  · rw [coeff_coeff_bivariateOf] at hab
    split_ifs at hab with h
    · exact (mem_monomials.1 h).2.2
    · exact absurd rfl hab
  · rw [evalEval_bivariateOf, ← sum_attach]
    have := congrFun (LinearMap.mem_ker.1 hc) i
    simpa [A, c', Matrix.mulVec, dotProduct, mul_comm, mul_left_comm, mul_assoc] using this

variable [DecidableEq F]

/-- **Root containment.** With distinct points, if `P` has degree less than `k` and agrees with the
received word at more than `D` points, then `Q(X, P(X)) = 0` for every Sudan interpolant `Q`. -/
theorem IsInterpolant.eval_eq_zero (hα : Function.Injective α) (hQ : IsInterpolant α w k D Q)
    {P : F[X]} (hP : P.degree < k) (hagree : D < #{i | P.eval (α i) = w i}) : Q.eval P = 0 := by
  let agree : Finset ι := {i | P.eval (α i) = w i}
  refine eq_zero_of_degree_lt_of_eval_finset_eq_zero (agree.image α) ?_ fun x hx => ?_
  · rw [card_image_of_injective _ hα]
    exact (degree_le_natDegree.trans (Nat.cast_le.2 (hQ.natDegree_eval_le hP))).trans_lt
      (by exact_mod_cast hagree)
  · obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
    rw [eval_eval_eq_evalEval, (mem_filter.1 hi).2, hQ.evalEval_eq_zero]

/-- **Root containment.** With distinct points, if `P` has degree less than `k` and agrees with the
received word at more than `D` points, then `Y - P(X)` divides every Sudan interpolant
`Q(X, Y)`. -/
theorem IsInterpolant.X_sub_C_dvd (hα : Function.Injective α) (hQ : IsInterpolant α w k D Q)
    {P : F[X]} (hP : P.degree < k) (hagree : D < #{i | P.eval (α i) = w i}) : Y - C P ∣ Q :=
  dvd_iff_isRoot.2 (hQ.eval_eq_zero hα hP hagree)

/-- With distinct points, a polynomial of degree less than `k` that agrees with the received word
at more than `D` points is a root of every Sudan interpolant, as a polynomial in `Y`. -/
theorem IsInterpolant.mem_roots (hα : Function.Injective α) (hQ : IsInterpolant α w k D Q)
    {P : F[X]} (hP : P.degree < k) (hagree : D < #{i | P.eval (α i) = w i}) : P ∈ Q.roots :=
  (Polynomial.mem_roots hQ.ne_zero).2 (hQ.eval_eq_zero hα hP hagree)

end Sudan

variable [Fintype ι] [DecidableEq F]

open Sudan Classical in
/-- *Sudan's list decoder* for dimension `k` and weighted degree `D` with evaluation points `α`: the
roots `P` of a Sudan interpolant `Q` for the received word `w`, as a polynomial in `Y`, that have
degree less than `k` and agree with `w` at more than `D` points; the empty list when there is no
interpolant. The interpolant is chosen noncomputably; this definition makes no claim about how it
or its roots are found. -/
noncomputable def sudan (α w : ι → F) (k D : ℕ) : Finset F[X] :=
  if h : ∃ Q, IsInterpolant α w k D Q then
    {P ∈ h.choose.roots.toFinset | P.degree < k ∧ D < #{i | P.eval (α i) = w i}}
  else ∅

variable {α w : ι → F} {k D : ℕ} {P : F[X]}

/-- Every polynomial listed by Sudan's decoder has degree less than `k` and agrees with the
received word at more than `D` points. -/
theorem degree_lt_and_lt_card_of_mem_sudan (h : P ∈ sudan α w k D) :
    P.degree < k ∧ D < #{i | P.eval (α i) = w i} := by
  classical
  unfold sudan at h
  split_ifs at h with hQ
  · exact (mem_filter.1 h).2
  · exact absurd h (notMem_empty P)

/-- **The size of the list.** Sudan's decoder lists `L` polynomials with `L * (k - 1) ≤ D`: at most
`D / (k - 1)` of them for `k ≥ 2`. -/
theorem card_sudan_mul_le : #(sudan α w k D) * (k - 1) ≤ D := by
  classical
  unfold sudan
  split_ifs with hQ
  · refine (Nat.mul_le_mul_right _ ?_).trans hQ.choose_spec.natDegree_mul_sub_one_le
    exact (card_filter_le _ _).trans (Multiset.toFinset_card_le _ |>.trans (card_roots' _))
  · simp

/-- **Sudan's list decoder lists the polynomials with large agreement.** With distinct points, if
there are more than `n` monomials of `(1, k - 1)`-weighted degree at most `D`, Sudan's decoder lists
exactly the polynomials of degree less than `k` that agree with the received word at more than `D`
points. -/
theorem mem_sudan_iff (hα : Function.Injective α)
    (hn : Fintype.card ι < #(Sudan.monomials (k - 1) D)) :
    P ∈ sudan α w k D ↔ P.degree < k ∧ D < #{i | P.eval (α i) = w i} := by
  classical
  refine ⟨degree_lt_and_lt_card_of_mem_sudan, fun hP => ?_⟩
  have hQ := Sudan.exists_isInterpolant α w hn
  unfold sudan
  rw [dite_eq_left hQ]
  exact mem_filter.2 ⟨Multiset.mem_toFinset.2 (hQ.choose_spec.mem_roots hα hP.1 hP.2), hP⟩

/-- **Sudan's list decoding of Reed–Solomon codes** [Sudan1997]. With distinct points, `k ≥ 2` and
`2 * (k - 1) * n < (D + 1) * (D + 2)`, Sudan's decoder lists exactly the polynomials of degree less
than `k` that agree with the received word at more than `D` points; by `card_sudan_mul_le` there are
at most `D / (k - 1)` of them. -/
theorem mem_sudan_iff_of_lt (hα : Function.Injective α) (hk : 2 ≤ k)
    (hn : 2 * (k - 1) * Fintype.card ι < (D + 1) * (D + 2)) :
    P ∈ sudan α w k D ↔ P.degree < k ∧ D < #{i | P.eval (α i) = w i} := by
  refine mem_sudan_iff hα ?_
  have := Sudan.add_one_mul_add_two_le_two_mul_mul_card_monomials (w := k - 1) (by omega) D
  exact Nat.lt_of_mul_lt_mul_left (hn.trans_le this)

/-- **List decoding of Reed–Solomon codes.** With distinct points, `k ≥ 2` and
`2 * (k - 1) * n < (D + 1) * (D + 2)`, every codeword of the Reed–Solomon code of dimension `k`
that agrees with the received word at more than `D` points is the list of values of a polynomial
listed by Sudan's decoder. -/
theorem exists_mem_sudan_of_mem_reedSolomon (hα : Function.Injective α) (hk : 2 ≤ k)
    (hn : 2 * (k - 1) * Fintype.card ι < (D + 1) * (D + 2)) {c : ι → F}
    (hc : c ∈ reedSolomon α k) (hagree : D < #{i | c i = w i}) :
    ∃ P ∈ sudan α w k D, (fun i => P.eval (α i)) = c := by
  obtain ⟨P, hP, rfl⟩ := mem_reedSolomon.1 hc
  exact ⟨P, (mem_sudan_iff_of_lt hα hk hn).2 ⟨hP, hagree⟩, rfl⟩

/-- **List size for Reed–Solomon codes.** With distinct points, `k ≥ 2` and
`2 * (k - 1) * n < (D + 1) * (D + 2)`, the number `L` of codewords of the Reed–Solomon code of
dimension `k` that agree with a word at more than `D` points satisfies `L * (k - 1) ≤ D`. -/
theorem ncard_sep_reedSolomon_mul_le (hα : Function.Injective α) (hk : 2 ≤ k)
    (hn : 2 * (k - 1) * Fintype.card ι < (D + 1) * (D + 2)) (w : ι → F) :
    {c ∈ (reedSolomon α k : Set (ι → F)) | D < #{i | c i = w i}}.ncard * (k - 1) ≤ D := by
  refine (Nat.mul_le_mul_right _ ?_).trans (card_sudan_mul_le (α := α) (w := w))
  calc {c ∈ (reedSolomon α k : Set (ι → F)) | D < #{i | c i = w i}}.ncard
      ≤ ((fun P : F[X] => fun i => P.eval (α i)) '' (sudan α w k D : Set F[X])).ncard := by
        refine Set.ncard_le_ncard (fun c hc => ?_) ((sudan α w k D).finite_toSet.image _)
        obtain ⟨P, hP, rfl⟩ := exists_mem_sudan_of_mem_reedSolomon hα hk hn hc.1 hc.2
        exact ⟨P, hP, rfl⟩
    _ ≤ (sudan α w k D : Set F[X]).ncard := Set.ncard_image_le (sudan α w k D).finite_toSet
    _ = #(sudan α w k D) := Set.ncard_coe_finset _

end Cslib.Code
