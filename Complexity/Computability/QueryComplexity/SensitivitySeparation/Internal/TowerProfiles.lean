/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.SensitivitySeparation.Internal.Tower
public import Complexity.Computability.QueryComplexity.SensitivitySeparation.Internal.RecursiveChildren
import Mathlib.Tactic

/-!
# Superquadratic sensitivity separation: tower profiles

Fixes the initial number `D` of predicate indices and records, for each level `n` of the tower
(which has `D - n` indices left), the side and joint sensitivity profiles on each output side.
Specializing the four recursive recurrences to a regular tournament with a good labeling yields the
level-to-level recurrences of these profiles. The number of distinct lifted blocks at each level is
also computed.

## Main definitions

* `towerSide`: side sensitivity of the tower family at level `n`.
* `towerJoint`: joint sensitivity of the tower family at level `n`.

## Main results

* `tower_four_recurrences`: the four linear recurrences relating the profiles at levels `n + 1` and
  `n`.
* `towerBlocks_family_card`: at level `n` there are `k ^ n * Fintype.card K` distinct lifted blocks.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/TowerProfiles.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

/-- Maximum sensitivity on a given output side at a recursive tower level. -/
def towerSide {k r : ℕ} {I : Type} [Fintype I] (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (D n : ℕ) (b : Bool) : ℕ :=
  sideSensitivity (towerFamily T label base n (D - n)) b

/-- Maximum joint sensitivity on a given output side at a recursive tower level. -/
def towerJoint {k r : ℕ} {I : Type} [Fintype I] (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (D n : ℕ) (b : Bool) : ℕ :=
  jointSensitivity (towerFamily T label base n (D - n)) b

/-- At level `0`, the side profile is the side sensitivity of `base D`. -/
@[simp] theorem towerSide_zero {k r : ℕ} {I : Type} [Fintype I] (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (D : ℕ) (b : Bool) : towerSide T label base D 0 b = sideSensitivity (base D) b := by
  rfl

/-- At level `0`, the joint profile is the joint sensitivity of `base D`. -/
@[simp] theorem towerJoint_zero {k r : ℕ} {I : Type} [Fintype I] (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (D : ℕ) (b : Bool) : towerJoint T label base D 0 b = jointSensitivity (base D) b := by
  rfl

/-- For a regular tournament on `2 * M ^ 2 + 1` vertices with a good labeling, `0 < r`, `n < D` and
a nested base family `base D`, writing `s b`, `j b` for `towerSide`, `towerJoint` at level `n` and
`s' b`, `j' b` for the same profiles at level `n + 1`, we have
`s' true ≤ M ^ 2 * s false + r * s true`, `j' true ≤ M ^ 2 * j false + r * s true`,
`s' false ≤ 16 * s false + s true + 3 * j true` and `j' false ≤ 16 * s false + 3 * j true`. -/
theorem tower_four_recurrences {M r : ℕ} {I : Type} [Fintype I]
    (T : RegularTournament M) (A : GoodLabeling T.toTournament r)
    (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (D n : ℕ) (hn : n < D) (hr : 0 < r) (hbase : NestedFamily (base D)) :
    (towerSide T.toTournament A.label base D (n + 1) true ≤
      M ^ 2 * towerSide T.toTournament A.label base D n false +
      r * towerSide T.toTournament A.label base D n true) ∧
    (towerJoint T.toTournament A.label base D (n + 1) true ≤
      M ^ 2 * towerJoint T.toTournament A.label base D n false +
      r * towerSide T.toTournament A.label base D n true) ∧
    (towerSide T.toTournament A.label base D (n + 1) false ≤
      16 * towerSide T.toTournament A.label base D n false +
      towerSide T.toTournament A.label base D n true +
      3 * towerJoint T.toTournament A.label base D n true) ∧
    (towerJoint T.toTournament A.label base D (n + 1) false ≤
      16 * towerSide T.toTournament A.label base D n false +
      3 * towerJoint T.toTournament A.label base D n true) := by
  have he : (D - (n + 1) + 1) + n = D := by omega
  have hf : NestedFamily (towerFamily T.toTournament A.label base n (D - (n + 1) + 1)) := by
    apply towerFamily_nested
    rwa [he]
  have H := recursive_four_recurrences T A
    (towerFamily T.toTournament A.label base n (D - (n + 1) + 1)) hf hr
  dsimp only at H
  change (sideSensitivity
    (towerFamily T.toTournament A.label base (n + 1) (D - (n + 1))) true ≤ _) ∧
    (jointSensitivity (towerFamily T.toTournament A.label base (n + 1) (D - (n + 1))) true ≤ _) ∧
    (sideSensitivity (towerFamily T.toTournament A.label base (n + 1) (D - (n + 1))) false ≤ _) ∧
    (jointSensitivity (towerFamily T.toTournament A.label base (n + 1) (D - (n + 1))) false ≤ _)
      at H
  have hcount : D - (n + 1) + 1 = D - n := by omega
  rw [hcount] at H
  exact H

open scoped Classical in
/-- If `0 < r` and the base blocks are nonempty and pairwise disjoint, then the lifted blocks at
level `n` form exactly `k ^ n * Fintype.card K` distinct sets. -/
theorem towerBlocks_family_card {k r : ℕ} {I K : Type} [Fintype K]
    (blocks : K → Finset I) (hr : 0 < r) (hne : ∀ b, (blocks b).Nonempty)
    (hd : Pairwise fun a b => Disjoint (blocks a) (blocks b)) (n : ℕ) :
    (Finset.univ.image (towerBlocks (k := k) (r := r) blocks n)).card = k ^ n * Fintype.card K := by
  have hinj : Function.Injective (towerBlocks (k := k) (r := r) blocks n) := by
    intro a b hab
    by_contra hneab
    obtain ⟨i, hi⟩ := towerBlocks_nonempty blocks hr hne n a
    exact Finset.disjoint_left.mp (towerBlocks_pairwise blocks hd n hneab) hi
      (by simpa [← hab] using hi)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, tower_block_index_card]

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
