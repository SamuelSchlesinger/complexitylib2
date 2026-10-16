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
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Fintype.Powerset
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
cases of the Cauchy–Schwarz inequality `Finset.expect_mul_sq_le_sq_mul_sq`, which also gives its
form with square roots (`Real.expect_mul_le_sqrt_mul_sqrt`, the form for `𝔼` of
`Real.sum_mul_le_sqrt_mul_sqrt`) and the triangle inequality for `√(𝔼 f²)`
(`Fintype.expect_add_sq_le`).

The uniform average over a product is the iterated average (`Fintype.expect_prod_type`), so a
function of some of the coordinates has the same average on the product
(`Fintype.expect_comp_fst`, `Fintype.expect_comp_snd`), and the uniform average on a finite group
is translation invariant (`Fintype.expect_add_left`).

## Main results

* `Finset.sq_expect_le_expect_sq`: the square of an average is at most the average of the squares.
* `Finset.prod_filter_mem_eq_prod_filter_notMem`: the sets containing an element are the sets
  avoiding it, with the element inserted.
* `Real.expect_mul_le_sqrt_mul_sqrt`: the Cauchy–Schwarz inequality for averages.
* `Fintype.expect_prod_type`: the average over a product is the iterated average.
* `Fintype.expect_comp_fst`, `Fintype.expect_comp_snd`, `Fintype.expect_comp_fst_snd_fst`: a
  function of some of the coordinates has the same average on the product.
* `Fintype.expect_add_left`: the uniform average on a finite group is translation invariant.
* `Fintype.expect_boole`: the average of an indicator is a density.
* `Fintype.mul_dens_filter_le_expect`: Markov's inequality for a uniform average.
* `Fintype.sq_expect_le_dens_mul_expect_sq`: the second moment method for a uniform average.
* `Fintype.expect_add_sq_le`: the triangle inequality for `√(𝔼 f²)`, squared.
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

/-- The sets containing `i` are the sets avoiding `i`, with `i` inserted. -/
@[to_additive /-- The sets containing `i` are the sets avoiding `i`, with `i` inserted. -/]
theorem prod_filter_mem_eq_prod_filter_notMem {M : Type*} [CommMonoid M] [Fintype ι]
    [DecidableEq ι] (i : ι) (g : Finset ι → M) :
    ∏ S with i ∈ S, g S = ∏ T with i ∉ T, g (insert i T) :=
  prod_nbij' (·.erase i) (insert i) (fun _ _ => by simp) (fun _ _ => by simp)
    (fun _ hS => insert_erase (mem_filter.1 hS).2) (fun _ hT => erase_insert (mem_filter.1 hT).2)
    fun _ hS => by rw [insert_erase (mem_filter.1 hS).2]

end Finset

namespace Real

open Finset

/-- **The Cauchy–Schwarz inequality** for averages, with square roots. -/
theorem expect_mul_le_sqrt_mul_sqrt {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    𝔼 i ∈ s, f i * g i ≤ √(𝔼 i ∈ s, f i ^ 2) * √(𝔼 i ∈ s, g i ^ 2) := by
  rw [← Real.sqrt_mul (expect_nonneg fun i _ ↦ sq_nonneg (f i))]
  exact Real.le_sqrt_of_sq_le (expect_mul_sq_le_sq_mul_sq _ _ _)

end Real

namespace Fintype

open Finset

variable {ι 𝕜 : Type*} [Fintype ι]

section Module

variable {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M] [Module ℚ≥0 M]

/-- The uniform average over a product is the iterated average. -/
theorem expect_prod_type (f : α × β → M) : 𝔼 x, f x = 𝔼 a, 𝔼 b, f (a, b) := by
  rw [← univ_product_univ, expect_product]

/-- A function of the first coordinate has the same average on the product. -/
theorem expect_comp_fst [Nonempty β] (f : α → M) : 𝔼 p : α × β, f p.1 = 𝔼 a, f a := by
  simp only [expect_prod_type, Fintype.expect_const]

/-- A function of the second coordinate has the same average on the product. -/
theorem expect_comp_snd [Nonempty α] (f : β → M) : 𝔼 p : α × β, f p.2 = 𝔼 b, f b := by
  simp only [expect_prod_type, Fintype.expect_const]

/-- A function of the first two coordinates has the same average on the product of three. -/
theorem expect_comp_fst_snd_fst [Nonempty γ] (f : α × β → M) :
    𝔼 p : α × β × γ, f (p.1, p.2.1) = 𝔼 q, f q := by
  rw [expect_prod_type, expect_prod_type f]
  exact expect_congr rfl fun a _ ↦ expect_comp_fst fun b ↦ f (a, b)

/-- **Translation invariance**: adding a fixed element permutes a finite additive group, so the
uniform average is unchanged. -/
theorem expect_add_left {G : Type*} [AddGroup G] [Fintype G] (f : G → M) (x : G) :
    𝔼 y, f (x + y) = 𝔼 y, f y :=
  Fintype.expect_equiv (Equiv.addLeft x) _ _ fun _ ↦ rfl

end Module

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
theorem sq_expect_le_dens_mul_expect_sq [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [ExistsAddOfLE 𝕜] (f : ι → 𝕜) :
    (𝔼 i, f i) ^ 2 ≤ (dens {i | f i ≠ 0} : 𝕜) * 𝔼 i, f i ^ 2 := by
  have h := expect_mul_sq_le_sq_mul_sq univ (fun i ↦ if f i ≠ 0 then (1 : 𝕜) else 0) f
  have h₁ : 𝔼 i, (if f i ≠ 0 then (1 : 𝕜) else 0) * f i = 𝔼 i, f i :=
    expect_congr rfl fun i _ ↦ by split_ifs <;> simp_all
  have h₂ : 𝔼 i, (if f i ≠ 0 then (1 : 𝕜) else 0) ^ 2 = 𝔼 i, if f i ≠ 0 then 1 else 0 :=
    expect_congr rfl fun i _ ↦ by split_ifs <;> norm_num
  rwa [h₁, h₂, expect_boole] at h

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- A read that is correct with probability at least `1 - δ` whatever the first argument is wrong
with probability at most `δ` on average. -/
theorem expect_expect_one_sub_le {β : Type*} [Nonempty ι] [Fintype β] [Nonempty β]
    {c : ι → β → 𝕜} {δ : 𝕜} (h : ∀ i, 1 - δ ≤ 𝔼 j, c i j) : 𝔼 i, 𝔼 j, (1 - c i j) ≤ δ :=
  expect_le univ_nonempty fun i _ => by
    rw [expect_sub_distrib, Fintype.expect_const]
    linarith [h i]

/-- **The triangle inequality for `√(𝔼 f²)`**, squared: if `𝔼 X² ≤ α² A` and `𝔼 Y² ≤ β² A`, then
`𝔼 (a X + b Y)² ≤ (a α + b β)² A` for `a, b ≥ 0`. -/
theorem expect_add_sq_le {X Y : ι → 𝕜} {a b α β A : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hA : 0 ≤ A) (hX : 𝔼 i, X i ^ 2 ≤ α ^ 2 * A) (hY : 𝔼 i, Y i ^ 2 ≤ β ^ 2 * A) :
    𝔼 i, (a * X i + b * Y i) ^ 2 ≤ (a * α + b * β) ^ 2 * A := by
  have hXY : 𝔼 i, X i * Y i ≤ α * β * A := by
    refine (le_abs_self _).trans (abs_le_of_sq_le_sq ?_ (by positivity))
    calc (𝔼 i, X i * Y i) ^ 2 ≤ (𝔼 i, X i ^ 2) * 𝔼 i, Y i ^ 2 := expect_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ (α ^ 2 * A) * (β ^ 2 * A) :=
        mul_le_mul hX hY (expect_nonneg fun _ _ ↦ sq_nonneg _) (by positivity)
      _ = (α * β * A) ^ 2 := by ring
  calc 𝔼 i, (a * X i + b * Y i) ^ 2
      = a ^ 2 * 𝔼 i, X i ^ 2 + 2 * a * b * 𝔼 i, X i * Y i + b ^ 2 * 𝔼 i, Y i ^ 2 := by
        simp only [mul_expect, ← expect_add_distrib]
        exact expect_congr rfl fun i _ ↦ by ring
    _ ≤ a ^ 2 * (α ^ 2 * A) + 2 * a * b * (α * β * A) + b ^ 2 * (β ^ 2 * A) := by gcongr
    _ = (a * α + b * β) ^ 2 * A := by ring

end LinearOrderedField

end Fintype
