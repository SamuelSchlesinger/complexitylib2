/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/{,Order/}BigOperators/Expect.lean`)

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Data.Finset.Density
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Uniform averages of indicators and second moments

Over a finite type, the uniform average of the indicator of a predicate is the density of the set
where it holds (`Fintype.expect_boole`), the counterpart for `𝔼` of `Finset.sum_boole`: the
probability of an event under the uniform distribution is the expectation of its indicator. With
it, **Markov's inequality** bounds the density of the set where a nonnegative function is large
by its average (`Fintype.mul_dens_filter_le_expect`), and the **second moment method** bounds the
density of the set where a function does not vanish from below by the square of its average over
the average of its square (`Fintype.sq_expect_le_dens_mul_expect_sq`).

The square of an average is at most the average of the squares (`Finset.sq_expect_le_expect_sq`),
the form for `𝔼` of `sum_div_card_sq_le_sum_sq_div_card`; both inequalities of second moments are
cases of the Cauchy–Schwarz inequality `Finset.expect_mul_sq_le_sq_mul_sq`.

## Main results

* `Finset.sq_expect_le_expect_sq`: the square of an average is at most the average of the squares.
* `Fintype.expect_prod_type`: the average over a product is the iterated average.
* `Fintype.expect_boole`: the average of an indicator is a density.
* `Fintype.mul_dens_filter_le_expect`: Markov's inequality for a uniform average.
* `Fintype.sq_expect_le_dens_mul_expect_sq`: the second moment method for a uniform average.
-/

@[expose] public section

open scoped BigOperators

namespace Finset

variable {ι R : Type*} [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]
  [Module ℚ≥0 R] [PosSMulMono ℚ≥0 R]

/-- The square of an average is at most the average of the squares. -/
theorem sq_expect_le_expect_sq (s : Finset ι) (f : ι → R) :
    (𝔼 i ∈ s, f i) ^ 2 ≤ 𝔼 i ∈ s, f i ^ 2 := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · simpa [hs] using expect_mul_sq_le_sq_mul_sq s f fun _ ↦ 1

end Finset

namespace Fintype

open Finset

variable {ι 𝕜 : Type*} [Fintype ι]

/-- The uniform average over a product is the iterated average. -/
theorem expect_prod_type {α β M : Type*} [Fintype α] [Fintype β] [AddCommMonoid M] [Module ℚ≥0 M]
    (f : α × β → M) : 𝔼 x, f x = 𝔼 a, 𝔼 b, f (a, b) := by
  rw [← univ_product_univ, expect_product]

/-- The uniform average of the indicator of `p` is the density of the set where `p` holds. -/
theorem expect_boole [Semifield 𝕜] [CharZero 𝕜] (p : ι → Prop) [DecidablePred p] :
    𝔼 i, (if p i then 1 else 0 : 𝕜) = (dens {i | p i} : 𝕜) := by
  rw [Fintype.expect_eq_sum_div_card, sum_boole, nnratCast_dens]

/-- **Markov's inequality** for a uniform average: a nonnegative function is at least `a` on a set
of density at most its average divided by `a`. -/
theorem mul_dens_filter_le_expect [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {f : ι → 𝕜} (hf : ∀ i, 0 ≤ f i) (a : 𝕜) :
    a * (dens {i | a ≤ f i} : 𝕜) ≤ 𝔼 i, f i := by
  rw [← expect_boole, mul_expect]
  refine expect_le_expect fun i _ => ?_
  split_ifs with hi
  · rwa [mul_one]
  · rw [mul_zero]
    exact hf i

/-- **The second moment method** for a uniform average: the square of the average of `f` is at
most the density of the set where `f` does not vanish times the average of `f ^ 2`. So `f` does not
vanish on a set of density at least `(𝔼 f) ^ 2 / 𝔼 f ^ 2`. -/
theorem sq_expect_le_dens_mul_expect_sq [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (f : ι → 𝕜) : (𝔼 i, f i) ^ 2 ≤ (dens {i | f i ≠ 0} : 𝕜) * 𝔼 i, f i ^ 2 := by
  have h := expect_mul_sq_le_sq_mul_sq univ (fun i ↦ if f i ≠ 0 then (1 : 𝕜) else 0) f
  have h₁ : 𝔼 i, (if f i ≠ 0 then (1 : 𝕜) else 0) * f i = 𝔼 i, f i :=
    expect_congr rfl fun i _ ↦ by split_ifs with hi <;> simp_all
  have h₂ : 𝔼 i, (if f i ≠ 0 then (1 : 𝕜) else 0) ^ 2 = 𝔼 i, if f i ≠ 0 then 1 else 0 :=
    expect_congr rfl fun i _ ↦ by split_ifs <;> norm_num
  rwa [h₁, h₂, expect_boole] at h

end Fintype
