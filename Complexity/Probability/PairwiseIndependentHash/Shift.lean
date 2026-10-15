/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.PairwiseIndependentHash
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Tactic.Abel

/-!
# The shift criterion for pairwise independence

Let `g k : X → Y` be functions into a finite additive group `Y`, indexed by keys `k` drawn
uniformly from a finite type `κ`. Masking them with an independent uniformly random offset
`v : Y` gives the family `h (k, v) x = g k x + v`, whose values are uniformly distributed
whatever `g` is. This file shows when this family is pairwise independent: strongly universal in
the terms of [Katz and Lindell, Definition 4.19][KatzLindell2020], after the strongly
universal₂ classes of Wegman and Carter [WegmanCarter1981].

* It suffices that the difference `g k x₁ - g k x₂` at two distinct points be uniformly
  distributed (`Cslib.Probability.isPairwiseIndependentHash_add_of_dens_filter_sub_eq`), that
  is, that `g` be `1 / |Y|`-difference universal [Katz and Lindell, Definition 4.23]
  [KatzLindell2020] (for `ε = 1 / |Y|` the bound of that definition forces equality): given the
  first value, the offset is determined, and the difference fixes the second.
* **The shift criterion**: the difference is uniformly distributed as soon as each of its
  translates is realized by a permutation of the keys
  (`Cslib.Probability.isPairwiseIndependentHash_add_of_shift`), since a permutation preserves
  the uniform distribution of the key (`Cslib.Probability.dens_filter_eq_of_shift`).
* When `g` depends additively on its key, translating the key by `k₀` shifts the difference by
  its value at `k₀`, so it suffices that the difference take every value
  (`Cslib.Probability.isPairwiseIndependentHash_add_of_surjective`).

The last criterion applies to the affine maps `x ↦ A x + b` over a finite field
(`Cslib.Probability.affineHash`), which include the families of [Katz and Lindell, Theorem 4.22
and Exercises 4.24 and 4.25][KatzLindell2020]: for `x₁ ≠ x₂`, the matrices `A` reach every
vector `A (x₁ - x₂)`. It also applies to their restriction to Toeplitz matrices
(`Cslib.Probability.toeplitzHash`, [Katz and Lindell, Exercise 4.26][KatzLindell2020]).

## Main results

* `Cslib.Probability.card_mul_card_filter_eq_of_shift`,
  `Cslib.Probability.dens_filter_eq_of_shift`: a function into a finite group whose translates
  are all realized by permutations has fibers of equal size.
* `Cslib.Probability.isPairwiseIndependentHash_add_of_dens_filter_sub_eq`: masking a family
  whose differences are uniformly distributed gives a pairwise independent family.
* `Cslib.Probability.isPairwiseIndependentHash_add_of_shift`: the shift criterion.
* `Cslib.Probability.isPairwiseIndependentHash_add_of_surjective`: the criterion for families
  that depend additively on their key.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, Section 4.6][KatzLindell2020]
* [M. N. Wegman, J. L. Carter, *New hash functions and their use in authentication and set
  equality*][WegmanCarter1981]
-/

@[expose] public section

namespace Cslib.Probability

open Finset

section Fiber

variable {ι G : Type*} [Fintype ι] [AddGroup G] [Fintype G] [DecidableEq G]

/-- If every translate `f + c` of a function `f : ι → G` into a finite group is `f ∘ e` for a
permutation `e` of `ι`, then all fibers of `f` have the same size `|ι| / |G|`. -/
theorem card_mul_card_filter_eq_of_shift {f : ι → G}
    (hf : ∀ c : G, ∃ e : Equiv.Perm ι, ∀ i, f (e i) = f i + c) (y : G) :
    Fintype.card G * #{i | f i = y} = Fintype.card ι := by
  have hfib (z : G) : #{i | f i = z} = #{i | f i = y} := by
    obtain ⟨e, he⟩ := hf (-z + y)
    refine card_equiv e fun i => ?_
    simp only [mem_filter, mem_univ, true_and]
    rw [he, ← add_assoc, add_eq_right, add_neg_eq_zero]
  have hsum := card_eq_sum_card_fiberwise (f := f) (s := univ) (t := univ) fun _ _ => mem_univ _
  rw [card_univ] at hsum
  rw [hsum]
  simp only [hfib, sum_const, card_univ, smul_eq_mul]

/-- **Uniformity from shifts**: if every translate `f + c` of a function `f : ι → G` into a
finite group is `f ∘ e` for a permutation `e` of `ι`, then `f` is uniformly distributed: for a
uniformly random `i`, `f i` takes each value with probability `1 / |G|`. -/
theorem dens_filter_eq_of_shift [Nonempty ι] {f : ι → G}
    (hf : ∀ c : G, ∃ e : Equiv.Perm ι, ∀ i, f (e i) = f i + c) (y : G) :
    dens {i | f i = y} = (Fintype.card G : ℚ≥0)⁻¹ := by
  have h := card_mul_card_filter_eq_of_shift hf y
  have hpos : #{i | f i = y} ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at h
    exact Fintype.card_ne_zero h.symm
  rw [dens_eq_card_div_card, ← h, Nat.cast_mul, div_mul_cancel_right₀ (Nat.cast_ne_zero.2 hpos)]

end Fiber

variable {κ X Y : Type*} [Fintype κ] [AddCommGroup Y] [Fintype Y] [DecidableEq Y]

/-- **Masking a difference-universal family**: let `g k : X → Y` be functions into a finite
additive group, indexed by keys `k : κ`, whose difference `g k x₁ - g k x₂` at any two distinct
points is uniformly distributed over a uniformly random key: `g` is `1 / |Y|`-difference
universal [Katz and Lindell, Definition 4.23][KatzLindell2020], where the bound `1 / |Y|` on the
probability of each difference forces equality. Then the family `h (k, v) x = g k x + v`, masked
by an independent uniformly random offset `v : Y`, is pairwise independent. -/
theorem isPairwiseIndependentHash_add_of_dens_filter_sub_eq [Nonempty κ] (g : κ → X → Y)
    (hg : ∀ ⦃x₁ x₂⦄, x₁ ≠ x₂ → ∀ c : Y,
      dens {k | g k x₁ - g k x₂ = c} = (Fintype.card Y : ℚ≥0)⁻¹) :
    IsPairwiseIndependentHash fun (p : κ × Y) x => g p.1 x + p.2 where
  dens_filter_apply_eq x y := by
    refine dens_filter_eq_of_shift
      (fun c => ⟨(Equiv.refl κ).prodCongr (Equiv.addRight c), fun p => ?_⟩) y
    exact (add_assoc _ _ _).symm
  dens_filter_apply_eq_and_apply_eq {x₁ x₂} hx y₁ y₂ := by
    have hcard : #{p : κ × Y | g p.1 x₁ + p.2 = y₁ ∧ g p.1 x₂ + p.2 = y₂} =
        #{k | g k x₁ - g k x₂ = y₁ - y₂} := by
      refine card_nbij' Prod.fst (fun k => (k, y₁ - g k x₁)) ?_ ?_ ?_ ?_
      · rintro ⟨k, v⟩ hkv
        simp only [mem_coe, mem_filter, mem_univ, true_and] at hkv ⊢
        rw [← hkv.1, ← hkv.2]
        abel
      · intro k hk
        simp only [mem_coe, mem_filter, mem_univ, true_and] at hk ⊢
        refine ⟨add_sub_cancel _ _, ?_⟩
        calc g k x₂ + (y₁ - g k x₁) = y₁ - (g k x₁ - g k x₂) := by abel
          _ = y₂ := by rw [hk, sub_sub_cancel]
      · rintro ⟨k, v⟩ hkv
        simp only [mem_coe, mem_filter, mem_univ, true_and] at hkv
        refine Prod.ext rfl ?_
        change y₁ - g k x₁ = v
        rw [← hkv.1, add_sub_cancel_left]
      · exact fun _ _ => rfl
    rw [dens_eq_card_div_card, hcard, Fintype.card_prod, Nat.cast_mul, div_mul_eq_div_div,
      ← dens_eq_card_div_card, hg hx, sq, mul_inv, div_eq_mul_inv]

/-- **The shift criterion**: let `g k : X → Y` be functions into a finite additive group,
indexed by keys `k` from a nonempty finite type `κ`. Suppose that, for any two distinct points
`x₁ ≠ x₂` and any `c : Y`, some permutation `e` of the keys shifts the difference
`g k x₁ - g k x₂` by `c`. Then the family `h (k, v) x = g k x + v`, masked by an independent
uniformly random offset `v : Y`, is pairwise independent. -/
theorem isPairwiseIndependentHash_add_of_shift [Nonempty κ] (g : κ → X → Y)
    (hg : ∀ ⦃x₁ x₂⦄, x₁ ≠ x₂ → ∀ c : Y, ∃ e : Equiv.Perm κ, ∀ k,
      g (e k) x₁ - g (e k) x₂ = g k x₁ - g k x₂ + c) :
    IsPairwiseIndependentHash fun (p : κ × Y) x => g p.1 x + p.2 :=
  isPairwiseIndependentHash_add_of_dens_filter_sub_eq g fun _ _ hx =>
    dens_filter_eq_of_shift (hg hx)

/-- **The shift criterion for additive keys**: let the keys `κ` form a finite additive group and
let the functions `g k : X → Y` depend additively on `k`. If the difference `g k x₁ - g k x₂`
at any two distinct points takes every value in `Y`, then the family `h (k, v) x = g k x + v`,
masked by an independent uniformly random offset `v : Y`, is pairwise independent. -/
theorem isPairwiseIndependentHash_add_of_surjective [AddGroup κ] (g : κ →+ X → Y)
    (hg : ∀ ⦃x₁ x₂⦄, x₁ ≠ x₂ → Function.Surjective fun k => g k x₁ - g k x₂) :
    IsPairwiseIndependentHash fun (p : κ × Y) x => g p.1 x + p.2 :=
  isPairwiseIndependentHash_add_of_shift g fun _ _ hx c => by
    obtain ⟨k₀, rfl⟩ := hg hx c
    refine ⟨Equiv.addRight k₀, fun k => ?_⟩
    simp only [Equiv.coe_addRight, map_add, Pi.add_apply]
    abel

end Cslib.Probability
