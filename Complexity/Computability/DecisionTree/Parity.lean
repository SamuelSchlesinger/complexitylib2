/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.PartialAssignment
public import Complexity.Foundations.Data.BitString.Parity
public import Complexity.Computability.DecisionTree.Sensitivity

/-!
# Decision trees for parity

Flipping any bit flips the parity, so parity is sensitive to every bit at every input
(`sensitivityAt_parity`). Its sensitivity, block sensitivity, certificate complexity and decision
tree complexity therefore all equal the number of bits [Jukna, Chapter 14][Jukna2012].

## Main results

* `Cslib.DecisionTree.complexity_parity`: the decision tree complexity of the parity of `n` bits
  is `n`.
* `Cslib.BitString.sensitivity_parity`, `Cslib.QueryComplexity.blockSensitivity_parity`,
  `Cslib.QueryComplexity.certificateComplexity_parity`: so are its sensitivity, block sensitivity
  and certificate complexity.
* `Cslib.DecisionTree.card_free_le_complexity_parity_fill`: restricted parity still needs to query
  every free bit.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib

open Finset BitString QueryComplexity

variable {n : ℕ}

namespace BitString

/-- Parity is sensitive to every bit at every input. -/
theorem sensitivityAt_parity (x : BitString n) : sensitivityAt (parity n) x = n := by
  have : (univ.filter fun i => parity n (Function.update x i !x i) ≠ parity n x) = univ := by
    refine eq_univ_of_forall fun i => mem_filter.2 ⟨mem_univ i, ?_⟩
    rw [parity, parityOn_update_not (mem_univ i)]
    cases parityOn univ x <;> decide
  change #(univ.filter fun i => parity n (Function.update x i !x i) ≠ parity n x) = n
  rw [this, card_univ, Fintype.card_fin]

/-- The sensitivity of parity is its number of coordinates. -/
theorem sensitivity_parity : sensitivity (parity n) = n :=
  le_antisymm (sensitivity_le_card _) ((sensitivityAt_parity (fun _ => false)).symm.trans_le
    (sensitivityAt_le_sensitivity _ _))

end BitString

namespace QueryComplexity

/-- The block sensitivity of parity is its number of coordinates. -/
theorem blockSensitivity_parity : blockSensitivity (parity n) = n :=
  le_antisymm (blockSensitivity_le_card _)
    (sensitivity_parity.symm.trans_le (sensitivity_le_blockSensitivity _))

/-- The certificate complexity of parity is its number of coordinates. -/
theorem certificateComplexity_parity : certificateComplexity (parity n) = n :=
  le_antisymm (certificateComplexity_le_card _)
    (blockSensitivity_parity.symm.trans_le (blockSensitivity_le_certificateComplexity _))

end QueryComplexity

namespace DecisionTree

/-- Every decision tree for the parity of `n` bits queries all of them in the worst case. -/
theorem complexity_parity : complexity (parity n) = n :=
  complexity_eq_card_of_sensitivityAt_eq_card (sensitivityAt_parity (fun _ => false))

/-- **Restricted parity** is the parity of the free bits, up to a constant, so every decision tree
for it queries all free bits in the worst case. -/
theorem card_free_le_complexity_parity_fill (ρ : PartialAssignment (Fin n)) :
    #ρ.free ≤ complexity fun x => parity n (ρ.fill x) := by
  refine card_le_complexity_of_forall_update_ne (x := fun _ => false) fun i hi => ?_
  have hρ := PartialAssignment.mem_free.1 hi
  set y := ρ.fill fun _ => false
  have hfill : ρ.fill (Function.update (fun _ => false) i !false) = Function.update y i !y i := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [y, PartialAssignment.fill, hρ]
    · simp [y, PartialAssignment.fill, hj]
  simp only [hfill]
  rw [parity, parityOn_update_not (mem_univ i)]
  cases parityOn univ y <;> decide

end DecisionTree

end Cslib
