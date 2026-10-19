/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Code.ReedSolomon
public import Mathlib.Algebra.Polynomial.Div
import Complexity.Foundations.Data.Hamming
import Mathlib.LinearAlgebra.Lagrange

/-!
# The Berlekamp–Welch decoder

Let `w : ι → F` be a received word that differs from the values `i ↦ p (α i)` of a polynomial `p`
of degree less than `k` at no more than `e` of the distinct points `α i`. The Berlekamp–Welch
decoder [WelchBerlekamp1986], [GuruswamiRudraSudan2019] looks for a monic
*error locator* `E` of degree `e` and a polynomial `Q` of degree less than `e + k` with
`Q (α i) = w i * E (α i)` at every point: the *key equations*
(`Cslib.Code.BerlekampWelch.IsSolution`). They have a solution, with `E` vanishing at the errors
and `Q = p * E` (`Cslib.Code.BerlekampWelch.exists_isSolution`). Conversely, if `2 e + k ≤ n`,
then for every solution `Q - p * E` has degree less than `e + k` and vanishes at the at least
`n - e ≥ e + k` points without errors, so `Q = p * E` and `p` is the quotient `Q /ₘ E`
(`Cslib.Code.BerlekampWelch.IsSolution.divByMonic_eq`). The decoder `Cslib.Code.berlekampWelch`
therefore recovers `p` from any solution (`Cslib.Code.berlekampWelch_eq_some`): Reed–Solomon codes
of dimension `k` are uniquely decoded up to `(n - k) / 2` errors, half their minimum distance
`n - k + 1`.

The key equations are a system of `n` linear equations in the `2 e + k` unknown coefficients of
`E` and `Q`, which Gaussian elimination solves in polynomial time. This module proves the
correctness of the decoder only: `Cslib.Code.berlekampWelch` chooses a solution noncomputably,
and no claim about running time is made.

## Main definitions

* `Cslib.Code.BerlekampWelch.IsSolution`: solutions of the key equations.
* `Cslib.Code.berlekampWelch`: the Berlekamp–Welch decoder.

## Main results

* `Cslib.Code.BerlekampWelch.exists_isSolution`: the key equations have a solution.
* `Cslib.Code.BerlekampWelch.IsSolution.eq_mul`,
  `Cslib.Code.BerlekampWelch.IsSolution.divByMonic_eq`: every solution yields the polynomial.
* `Cslib.Code.berlekampWelch_eq_some`: the decoder corrects up to `e` errors when
  `2 e + k ≤ n`.
* `Cslib.Code.berlekampWelch_eq_some_of_mem_reedSolomon`: unique decoding of Reed–Solomon codes.

## References

* [L. R. Welch, E. R. Berlekamp, *Error correction for algebraic block codes*][WelchBerlekamp1986]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*]
  [GuruswamiRudraSudan2019]
-/

@[expose] public section

namespace Cslib.Code

open Finset Polynomial

variable {F ι : Type*} [Field F]

namespace BerlekampWelch

/-- `(E, Q)` solves the *Berlekamp–Welch key equations* for the received word `w` with evaluation
points `α`, `e` errors and dimension `k`: the error locator `E` is monic of degree `e`, `Q` has
degree less than `e + k`, and `Q (α i) = w i * E (α i)` at every point. -/
structure IsSolution (α w : ι → F) (e k : ℕ) (E Q : F[X]) : Prop where
  monic : E.Monic
  natDegree_eq : E.natDegree = e
  degree_lt : Q.degree < (e + k : ℕ)
  eval_eq : ∀ i, Q.eval (α i) = w i * E.eval (α i)

variable {α w : ι → F} {e k : ℕ} {p : F[X]}

/-- The product of a polynomial of degree less than `k` with a polynomial of degree `e` has degree
less than `e + k`. -/
private theorem degree_mul_lt {E : F[X]} (hp : p.degree < k) (hE : E.natDegree = e) :
    (p * E).degree < (e + k : ℕ) := by
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [zero_mul, degree_zero]
    exact WithBot.bot_lt_coe _
  rcases eq_or_ne E 0 with rfl | hE0
  · rw [mul_zero, degree_zero]
    exact WithBot.bot_lt_coe _
  have := (natDegree_lt_iff_degree_lt hp0).2 hp
  rw [degree_mul, degree_eq_natDegree hp0, degree_eq_natDegree hE0, hE, ← Nat.cast_add,
    Nat.cast_lt]
  omega

variable [Fintype ι] [DecidableEq F]

/-- If the received word `w` is within distance `e` of the values of a polynomial `p` of degree
less than `k`, the key equations have a solution: `E` is the product of `X - α i` over the
points `i` where `w` is wrong, times a power of `X` that brings its degree to `e`, and
`Q = p * E`. -/
theorem exists_isSolution (hp : p.degree < k) (he : hammingDist (fun i => p.eval (α i)) w ≤ e) :
    ∃ E Q, IsSolution α w e k E Q := by
  classical
  let errors : Finset ι := {i | p.eval (α i) ≠ w i}
  have herrors : #errors ≤ e := he
  have hmonic : (Lagrange.nodal errors α * X ^ (e - #errors)).Monic :=
    Lagrange.nodal_monic.mul (monic_X_pow _)
  have hdeg : (Lagrange.nodal errors α * X ^ (e - #errors)).natDegree = e := by
    rw [Lagrange.nodal_monic.natDegree_mul (monic_X_pow _), Lagrange.natDegree_nodal,
      natDegree_X_pow]
    omega
  refine ⟨_, _, ⟨hmonic, hdeg, degree_mul_lt hp hdeg, fun i => ?_⟩⟩
  rw [eval_mul]
  by_cases hi : i ∈ errors
  · rw [eval_mul, Lagrange.eval_nodal_at_node hi, zero_mul, mul_zero, mul_zero]
  · rw [show p.eval (α i) = w i by simpa [errors] using hi]

/-- **Correctness of the key equations.** With distinct points, if `2 e + k ≤ n` and the received
word `w` is within distance `e` of the values of a polynomial `p` of degree less than `k`, every
solution `(E, Q)` of the key equations has `Q = p * E`. -/
theorem IsSolution.eq_mul (hα : Function.Injective α) (hn : 2 * e + k ≤ Fintype.card ι)
    (hp : p.degree < k) (he : hammingDist (fun i => p.eval (α i)) w ≤ e) {E Q : F[X]}
    (h : IsSolution α w e k E Q) : Q = p * E := by
  classical
  -- `Q - p * E` vanishes at the points without errors, of which there are at least `e + k`
  let correct : Finset ι := {i | p.eval (α i) = w i}
  have hcorrect : #correct + hammingDist (fun i => p.eval (α i)) w = Fintype.card ι :=
    card_filter_eq_add_hammingDist _ _
  refine sub_eq_zero.1 (eq_zero_of_degree_lt_of_eval_finset_eq_zero (correct.image α) ?_ ?_)
  · rw [card_image_of_injective _ hα]
    calc (Q - p * E).degree ≤ max Q.degree (p * E).degree := degree_sub_le _ _
      _ < (e + k : ℕ) := max_lt h.degree_lt (degree_mul_lt hp h.natDegree_eq)
      _ ≤ #correct := by exact_mod_cast (by omega)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
    rw [eval_sub, eval_mul, h.eval_eq i, (mem_filter.1 hi).2, sub_self]

/-- With distinct points, if `2 e + k ≤ n` and the received word is within distance `e` of the
values of a polynomial `p` of degree less than `k`, every solution `(E, Q)` of the key equations
gives `p = Q /ₘ E`. -/
theorem IsSolution.divByMonic_eq (hα : Function.Injective α) (hn : 2 * e + k ≤ Fintype.card ι)
    (hp : p.degree < k) (he : hammingDist (fun i => p.eval (α i)) w ≤ e) {E Q : F[X]}
    (h : IsSolution α w e k E Q) : Q /ₘ E = p := by
  rw [h.eq_mul hα hn hp he, mul_comm, mul_divByMonic_cancel_left p h.monic]

end BerlekampWelch

open BerlekampWelch Classical in
/-- The *Berlekamp–Welch decoder* for `e` errors and dimension `k` with evaluation points `α`: the
quotient `Q /ₘ E` for a solution `(E, Q)` of the key equations for the received word `w`, or
`none` when they have no solution. The solution is chosen noncomputably; this definition makes no
claim about how it is found. -/
noncomputable def berlekampWelch (α : ι → F) (e k : ℕ) (w : ι → F) : Option F[X] :=
  if h : ∃ EQ : F[X] × F[X], IsSolution α w e k EQ.1 EQ.2 then
    some (h.choose.2 /ₘ h.choose.1)
  else none

variable [Fintype ι] [DecidableEq F] {α w : ι → F} {e k : ℕ}

open BerlekampWelch in
/-- **The Berlekamp–Welch decoder corrects `e` errors** when `2 e + k ≤ n`: with distinct points,
if the received word `w` is within distance `e` of the values of a polynomial `p` of degree less
than `k`, the decoder returns `p`. -/
theorem berlekampWelch_eq_some (hα : Function.Injective α) (hn : 2 * e + k ≤ Fintype.card ι)
    {p : F[X]} (hp : p.degree < k) (he : hammingDist (fun i => p.eval (α i)) w ≤ e) :
    berlekampWelch α e k w = some p := by
  obtain ⟨E, Q, hEQ⟩ := exists_isSolution hp he
  have h : ∃ EQ : F[X] × F[X], IsSolution α w e k EQ.1 EQ.2 := ⟨(E, Q), hEQ⟩
  rw [berlekampWelch, dite_eq_left h]
  exact congrArg some (h.choose_spec.divByMonic_eq hα hn hp he)

/-- **Unique decoding of Reed–Solomon codes.** With distinct points, if `2 e + k ≤ n` and the
received word `w` is within distance `e` of a codeword `c` of the Reed–Solomon code of dimension
`k`, the Berlekamp–Welch decoder returns a polynomial of degree less than `k` whose values are
`c`. -/
theorem berlekampWelch_eq_some_of_mem_reedSolomon (hα : Function.Injective α)
    (hn : 2 * e + k ≤ Fintype.card ι) {c : ι → F} (hc : c ∈ reedSolomon α k)
    (he : hammingDist c w ≤ e) :
    ∃ p : F[X], p.degree < k ∧ (fun i => p.eval (α i)) = c ∧ berlekampWelch α e k w = some p := by
  obtain ⟨p, hp, rfl⟩ := mem_reedSolomon.1 hc
  exact ⟨p, hp, rfl, berlekampWelch_eq_some hα hn hp he⟩

end Cslib.Code
