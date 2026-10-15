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
public import Mathlib.Data.Finset.Density
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Uniform averages of indicators

Over a finite type, the uniform average of the indicator of a predicate is the density of the set
where it holds (`Fintype.expect_boole`), the counterpart for `𝔼` of `Finset.sum_boole`: the
probability of an event under the uniform distribution is the expectation of its indicator. With
it, **Markov's inequality** bounds the density of the set where a nonnegative function is large
by its average (`Fintype.mul_dens_filter_le_expect`).

## Main results

* `Fintype.expect_boole`: the average of an indicator is a density.
* `Fintype.mul_dens_filter_le_expect`: Markov's inequality for a uniform average.
-/

@[expose] public section

namespace Fintype

open Finset
open scoped BigOperators

variable {ι 𝕜 : Type*} [Fintype ι]

/-- The uniform average of the indicator of `p` is the density of the set where `p` holds. -/
theorem expect_boole [Semifield 𝕜] [CharZero 𝕜] (p : ι → Prop) [DecidablePred p] :
    𝔼 i, (if p i then 1 else 0 : 𝕜) = (dens {i | p i} : 𝕜) := by
  rw [Fintype.expect_eq_sum_div_card, sum_boole, nnratCast_dens]

/-- **Markov's inequality** for a uniform average: a nonnegative function is at least `a` on a set
of density at most its average divided by `a`. -/
theorem mul_dens_filter_le_expect [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {f : ι → 𝕜} (hf : ∀ i, 0 ≤ f i) (a : 𝕜) :
    a * (dens {i | a ≤ f i} : 𝕜) ≤ 𝔼 i, f i := by
  rw [← expect_boole, mul_expect]
  refine expect_le_expect fun i _ => ?_
  split_ifs with hi
  · rwa [mul_one]
  · rw [mul_zero]
    exact hf i

end Fintype
