/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Hadamard
public import Complexity.Foundations.Data.Code.Basic

/-!
# The minimum distance of the Hadamard code

The encodings of distinct messages of `n` bits under the Hadamard code
`Cslib.BitString.hadamardCode` differ on exactly half of the `2 ^ n` inputs
(`Cslib.BitString.two_mul_hammingDist_hadamardCode`), so for `n ≥ 1` the Hadamard code has
minimum distance `2 ^ (n - 1)` (`Cslib.BitString.minDist_range_hadamardCode`)
[Arora and Barak, Chapter 19][AroraBarak09].

## Main results

* `Cslib.BitString.minDist_range_hadamardCode`: the minimum distance of the Hadamard code.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 19
-/

@[expose] public section

namespace Cslib.BitString

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The distance of the Hadamard code.** For messages of `n ≥ 1` bits, the Hadamard code has
minimum distance `2 ^ (n - 1)`: half of its length `2 ^ n`. -/
theorem minDist_range_hadamardCode [Nonempty ι] :
    Code.minDist (Set.range (hadamardCode (ι := ι))) = (2 ^ (Fintype.card ι - 1) : ℕ) := by
  have hdist {x y : ι → Bool} (h : x ≠ y) :
      hammingDist (hadamardCode x) (hadamardCode y) = 2 ^ (Fintype.card ι - 1) := by
    have := two_mul_hammingDist_hadamardCode h
    rw [← Nat.sub_add_cancel (Fintype.card_pos (α := ι)), pow_succ, mul_comm _ 2] at this
    exact Nat.eq_of_mul_eq_mul_left two_pos this
  have hne : (fun _ => false : ι → Bool) ≠ fun _ => true := fun h =>
    Bool.false_ne_true (congrFun h (Classical.arbitrary ι))
  refine le_antisymm ?_ (Code.le_minDist_iff.2 ?_)
  · rw [← hdist hne]
    exact Code.minDist_le_hammingDist ⟨_, rfl⟩ ⟨_, rfl⟩
      fun h => hne (hadamardCode_injective h)
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    rw [hdist fun h => hxy (congrArg hadamardCode h)]

end Cslib.BitString
