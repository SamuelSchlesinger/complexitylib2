/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.BitString.LinearHash
public import Complexity.Probability.PairwiseIndependentHash
import Complexity.Probability.PairwiseIndependentHash.Shift

/-!
# Affine hashing of bit strings

The affine maps `x ↦ A x + b` of bit strings, with a Boolean matrix `A` given by its rows and an
offset `b` (`Cslib.BitString.LinearHash.affineHash`), form a pairwise independent hash family
(`Cslib.BitString.LinearHash.isPairwiseIndependentHash_affineHash`): masking the two-universal
linear family `Cslib.BitString.LinearHash.hash` with a uniformly random offset satisfies the shift
criterion `Cslib.Probability.isPairwiseIndependentHash_add_of_surjective`. This is the family of
the set lower bound protocol of Goldwasser and Sipser [GoldwasserSipser1986]
[Arora and Barak, Section 8.2][AroraBarak09].

In counts, for a pairwise independent family into `Y` and a set `S`, a target is missed by at most
a quarter of the seeds when `#S ≥ 4 |Y|`, and hit by at most a quarter of them when
`4 #S ≤ |Y|` (`Cslib.Probability.IsPairwiseIndependentHash.four_mul_card_filter_notMem_image_le`,
`Cslib.Probability.IsPairwiseIndependentHash.four_mul_card_filter_mem_image_le`). Relabelling the
seeds by an equivalence keeps a family pairwise independent
(`Cslib.Probability.IsPairwiseIndependentHash.comp_equiv`), so the seeds can be read from a flat
bit string.

## Main definitions

* `Cslib.BitString.LinearHash.affineHash`: the affine map `x ↦ A x + b` of bit strings.

## Main results

* `Cslib.Probability.IsPairwiseIndependentHash.comp_equiv`: relabelling seeds.
* `Cslib.Probability.IsPairwiseIndependentHash.four_mul_card_filter_notMem_image_le`,
  `Cslib.Probability.IsPairwiseIndependentHash.four_mul_card_filter_mem_image_le`: the two
  quarter bounds of the set lower bound protocol.
* `Cslib.BitString.LinearHash.isPairwiseIndependentHash_affineHash`: affine hashing of bit strings
  is pairwise independent.

## References

* [S. Goldwasser, M. Sipser, *Private coins versus public coins in interactive proof
  systems*][GoldwasserSipser1986]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Probability

open Finset

variable {ι ι' X Y : Type*} [Fintype ι] [Fintype Y] [DecidableEq Y] {h : ι → X → Y}

namespace IsPairwiseIndependentHash

/-- Relabelling the seeds by an equivalence does not change densities. -/
private theorem dens_filter_comp_equiv [Fintype ι'] (e : ι' ≃ ι) (P : ι → Prop)
    [DecidablePred P] : dens {i' | P (e i')} = dens {i | P i} := by
  rw [dens_eq_card_div_card, dens_eq_card_div_card, Fintype.card_congr e]
  congr 2
  exact card_equiv e fun i' => by simp

/-- **Relabelling seeds**: precomposing the seeds of a pairwise independent family with an
equivalence keeps it pairwise independent. -/
theorem comp_equiv [Fintype ι'] (hh : IsPairwiseIndependentHash h) (e : ι' ≃ ι) :
    IsPairwiseIndependentHash fun i => h (e i) where
  dens_filter_apply_eq x y := by
    rw [dens_filter_comp_equiv e fun i => h i x = y]
    exact hh.dens_filter_apply_eq x y
  dens_filter_apply_eq_and_apply_eq hx y₁ y₂ := by
    rw [dens_filter_comp_equiv e fun i => h i _ = y₁ ∧ h i _ = y₂]
    exact hh.dens_filter_apply_eq_and_apply_eq hx y₁ y₂

/-- **Large sets are hit**: if `#S ≥ 4 |Y|`, at most a quarter of the seeds miss a target. -/
theorem four_mul_card_filter_notMem_image_le (hh : IsPairwiseIndependentHash h) {S : Finset X}
    (hS : 4 * Fintype.card Y ≤ #S) (y : Y) :
    4 * #{i | y ∉ S.image (h i)} ≤ Fintype.card ι := by
  have hY : 0 < Fintype.card Y := Fintype.card_pos_iff.2 ⟨y⟩
  have hne : S.Nonempty := card_pos.1 (by omega)
  have hι : 0 < Fintype.card ι := by
    obtain ⟨x, -⟩ := hne
    have := hh.nonempty x y
    exact Fintype.card_pos
  have hd := hh.dens_filter_notMem_image_le hne y
  rw [dens_eq_card_div_card, div_le_div_iff₀ (by exact_mod_cast hι)
    (by exact_mod_cast hne.card_pos)] at hd
  have hd' : #{i | y ∉ S.image (h i)} * #S ≤ Fintype.card Y * Fintype.card ι := by
    exact_mod_cast hd
  nlinarith

/-- **Small sets are missed**: if `4 #S ≤ |Y|`, at most a quarter of the seeds hit a target. -/
theorem four_mul_card_filter_mem_image_le (hh : IsPairwiseIndependentHash h) {S : Finset X}
    (hS : 4 * #S ≤ Fintype.card Y) (y : Y) :
    4 * #{i | y ∈ S.image (h i)} ≤ Fintype.card ι := by
  have hY : 0 < Fintype.card Y := Fintype.card_pos_iff.2 ⟨y⟩
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hι : 0 < Fintype.card ι := by
    obtain ⟨x, -⟩ := hne
    have := hh.nonempty x y
    exact Fintype.card_pos
  have hd := hh.dens_filter_mem_image_le S y
  rw [dens_eq_card_div_card, div_le_div_iff₀ (by exact_mod_cast hι) (by exact_mod_cast hY)] at hd
  have hd' : #{i | y ∈ S.image (h i)} * Fintype.card Y ≤ #S * Fintype.card ι := by
    exact_mod_cast hd
  nlinarith

end IsPairwiseIndependentHash

end Cslib.Probability

namespace Cslib.BitString.LinearHash

open Cslib.Probability

/-- The affine map `x ↦ A x + b` of bit strings, with seed the rows of the matrix `A` and the
offset `b`. -/
def affineHash {n m : ℕ} (seed : (Fin m → BitString n) × BitString m) (x : BitString n) :
    BitString m :=
  hash seed.1 x + seed.2

/-- **Affine hashing of bit strings is pairwise independent**: for distinct inputs, the difference
of the linear hashes is the linear hash of a nonzero difference, which takes every value. -/
theorem isPairwiseIndependentHash_affineHash (n m : ℕ) :
    IsPairwiseIndependentHash (affineHash (n := n) (m := m)) := by
  let g : (Fin m → BitString n) →+ (BitString n → BitString m) :=
    { toFun := hash
      map_zero' := by
        funext x i
        simp [hash]
      map_add' := by
        intro A B
        funext x i
        simp [hash, add_dotProduct] }
  refine isPairwiseIndependentHash_add_of_surjective g fun x₁ x₂ hx c => ?_
  obtain ⟨j, hj⟩ : ∃ j, (x₁ - x₂) j = true := by
    by_contra! h
    exact hx (sub_eq_zero.1 (funext fun j => by simpa [Bool.zero_eq_false] using h j))
  refine ⟨fun i => Pi.single j (c i), funext fun i => ?_⟩
  change (Pi.single j (c i) : BitString n) ⬝ᵥ x₁ - (Pi.single j (c i) : BitString n) ⬝ᵥ x₂ = c i
  rw [← dotProduct_sub, single_dotProduct, hj, Bool.mul_eq_and, Bool.and_true]

end Cslib.BitString.LinearHash
