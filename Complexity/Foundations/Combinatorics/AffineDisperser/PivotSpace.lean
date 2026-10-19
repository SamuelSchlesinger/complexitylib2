/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib

/-!
# Pivot spaces of a subspace of a product

For a subspace `V` of `Fin r → M`, the `i`-th *pivot space* consists of the `i`-th coordinates of
the vectors of `V` that vanish in all coordinates below `i`. This is the block-echelon form of `V`
used by Bourgain for affine extractors [Bourgain2007] and by Ben-Sasson and Kopparty
[BenSassonKopparty2012, Lemma 7.1]: choosing for each pivot vector a lift in `V` that vanishes
below its block presents `V` in block-triangular form, and the dimensions of the pivot spaces add
up to the dimension of `V`.

## Main definitions

* `Cslib.AffineDisperser.pivotSpace`: the `i`-th pivot space of a subspace of `Fin r → M`.

## Main results

* `Cslib.AffineDisperser.mem_pivotSpace`: pivot vectors lift to vectors of `V` vanishing below
  their block.
* `Cslib.AffineDisperser.sum_finrank_pivotSpace`: the dimensions of the pivot spaces add up to
  the dimension of `V`.

## References

* [J. Bourgain, *On the construction of affine extractors*][Bourgain2007]
* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
-/

@[expose] public section

namespace Cslib.AffineDisperser

open Module

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {r : ℕ}

/-- The `i`-th *pivot space* of `V ≤ Fin r → M`: the `i`-th coordinates of the vectors of `V`
that vanish in every coordinate below `i`. -/
def pivotSpace (V : Submodule K (Fin r → M)) (i : Fin r) : Submodule K M :=
  (V ⊓ ⨅ j : Fin r, ⨅ (_ : j < i), LinearMap.ker (LinearMap.proj j)).map (LinearMap.proj i)

theorem mem_pivotSpace {V : Submodule K (Fin r → M)} {i : Fin r} {y : M} :
    y ∈ pivotSpace V i ↔ ∃ v ∈ V, (∀ j < i, v j = 0) ∧ v i = y := by
  sorry

/-- The dimensions of the pivot spaces of `V` add up to the dimension of `V`. -/
theorem sum_finrank_pivotSpace [FiniteDimensional K M] (V : Submodule K (Fin r → M)) :
    ∑ i, finrank K (pivotSpace V i) = finrank K V := by
  sorry

end Cslib.AffineDisperser
