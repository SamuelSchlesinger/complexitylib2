/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.SensitivitySeparation.Internal.Defs
public import Complexity.Foundations.Data.BitString.Flip
public import Cslib.Computability.QueryComplexity.Measures

/-!
# Superquadratic sensitivity separation: agreement with the CSLib measures

The separation construction works with its own flips and measures over an arbitrary finite
coordinate type (`Internal.flip`, `Internal.sensitivity`, `Internal.blockSensitivity`), since it
composes functions on product coordinate types. On the coordinates `Fin n` these agree with
CSLib's `BitString.flipBlock`, `BitString.sensitivity` and `QueryComplexity.blockSensitivity`.
Internal block families must consist of nonempty blocks, but this is no restriction: flipping
the empty block never changes the value of a function.

## Main results

* `Internal.flip_eq_flipOn`: the internal flip is `BitString.flipOn`.
* `Internal.sensitivity_eq_bitString_sensitivity`: the internal sensitivity is
  `BitString.sensitivity`.
* `Internal.blockSensitivityAt_eq_queryComplexity_blockSensitivityAt`,
  `Internal.blockSensitivity_eq_queryComplexity_blockSensitivity`: the internal block sensitivity is
  `QueryComplexity.blockSensitivity`, pointwise and globally.

## References

* [N. Nisan, *CREW PRAMs and decision trees*][Nisan1991]
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation.Internal

open Finset

variable {n : ℕ}

/-- The internal flip is `BitString.flipOn`, for any decidable equality on the coordinates. -/
theorem flip_eq_flipOn {I : Type} [DecidableEq I] (x : I → Bool) (B : Finset I) :
    flip x B = BitString.flipOn B x := by
  unfold flip
  congr
  exact Subsingleton.elim _ _

/-- On `Fin n`, the internal flip is CSLib's `BitString.flipBlock`. -/
theorem flip_eq_flipBlock (x : BitString n) (B : Finset (Fin n)) :
    flip x B = BitString.flipBlock B x :=
  flip_eq_flipOn x B

/-- On `Fin n`, the internal pointwise sensitivity is `BitString.sensitivityAt`. -/
theorem sensitivityAt_eq_bitString_sensitivityAt (f : BooleanFunction n) (x : BitString n) :
    sensitivityAt f x = BitString.sensitivityAt f x := by
  unfold sensitivityAt BitString.sensitivityAt BitString.sensitiveCoords
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, BitString.IsSensitiveCoord, flip_eq_flipBlock,
    BitString.flipBlock_singleton]

/-- On `Fin n`, the internal sensitivity is `BitString.sensitivity`. -/
theorem sensitivity_eq_bitString_sensitivity (f : BooleanFunction n) :
    sensitivity f = BitString.sensitivity f := by
  refine le_antisymm (Finset.sup_le fun x _ => ?_) (Finset.sup_le fun x _ => ?_)
  · exact (sensitivityAt_eq_bitString_sensitivityAt f x).trans_le
      (BitString.sensitivityAt_le_sensitivity f x)
  · exact (sensitivityAt_eq_bitString_sensitivityAt f x).symm.trans_le (Finset.le_sup (by simp))

/-- On `Fin n`, the internal pointwise block sensitivity is
`QueryComplexity.blockSensitivityAt`. -/
theorem blockSensitivityAt_eq_queryComplexity_blockSensitivityAt (f : BooleanFunction n)
    (x : BitString n) :
    blockSensitivityAt f x = QueryComplexity.blockSensitivityAt f x := by
  classical
  refine le_antisymm (Finset.sup_le fun F _ => ?_) (Finset.sup_le fun F hF => ?_)
  · split_ifs with h
    · refine card_le_blockSensitivityAt ⟨fun B hB => ?_, fun A hA B hB hAB => h.1 A hA B hB hAB⟩
      rw [IsSensitiveBlock, ← flip_eq_flipBlock]
      exact (h.2 B hB).2
    · exact Nat.zero_le _
  · obtain ⟨hsens, hdisj⟩ := mem_sensitiveFamilies.mp hF
    have h : (∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B) ∧
        ∀ B ∈ F, B.Nonempty ∧ f (flip x B) ≠ f x := by
      refine ⟨fun A hA B hB hAB => hdisj hA hB hAB, fun B hB => ⟨?_, ?_⟩⟩
      · rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        exact hsens _ hB (by rw [BitString.flipBlock_empty])
      · rw [flip_eq_flipBlock]
        exact hsens B hB
    exact Finset.le_sup_of_le (mem_univ F) (le_of_eq (ite_eq_left h).symm)

/-- On `Fin n`, the internal block sensitivity is `QueryComplexity.blockSensitivity`. -/
theorem blockSensitivity_eq_queryComplexity_blockSensitivity (f : BooleanFunction n) :
    blockSensitivity f = QueryComplexity.blockSensitivity f := by
  refine le_antisymm (Finset.sup_le fun x _ => ?_) (Finset.sup_le fun x _ => ?_)
  · exact (blockSensitivityAt_eq_queryComplexity_blockSensitivityAt f x).trans_le
      (blockSensitivityAt_le_blockSensitivity f x)
  · exact (blockSensitivityAt_eq_queryComplexity_blockSensitivityAt f x).symm.trans_le
      (Finset.le_sup (by simp))

end Cslib.QueryComplexity.SensitivitySeparation.Internal
