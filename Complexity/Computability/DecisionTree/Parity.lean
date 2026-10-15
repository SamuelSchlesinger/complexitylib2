/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Restriction
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
* `Cslib.DecisionTree.sensitivity_parity`, `Cslib.DecisionTree.blockSensitivity_parity`,
  `Cslib.DecisionTree.certificateComplexity_parity`: so are its sensitivity, block sensitivity and
  certificate complexity.
* `Cslib.DecisionTree.card_free_le_complexity_parity_fill`: restricted parity still needs to query
  every free bit.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.DecisionTree

open Finset BitString

variable {n : ℕ}

/-- Parity is sensitive to every bit at every input. -/
theorem sensitivityAt_parity (x : BitString n) : sensitivityAt (parity n) x = n := by
  have : (univ.filter fun i => parity n (Function.update x i !x i) ≠ parity n x) = univ := by
    refine eq_univ_of_forall fun i => mem_filter.2 ⟨mem_univ i, ?_⟩
    rw [parity, parityOn_update_not (mem_univ i)]
    cases parityOn univ x <;> decide
  rw [sensitivityAt, this, card_univ, Fintype.card_fin]

/-- Every decision tree for the parity of `n` bits queries all of them in the worst case. -/
theorem complexity_parity : complexity (parity n) = n := by
  have h := complexity_eq_card_of_sensitivityAt_eq_card (f := parity n) (x := fun _ => false)
    (by rw [sensitivityAt_parity, Fintype.card_fin])
  rwa [Fintype.card_fin] at h

/-- **Restricted parity** is the parity of the free bits, up to a constant, so every decision tree
for it queries all free bits in the worst case. -/
theorem card_free_le_complexity_parity_fill (ρ : Cslib.Circuits.Boolean.Restriction n) :
    #ρ.free ≤ complexity fun x => parity n (ρ.fill x) := by
  refine le_trans ?_ (sensitivityAt_le_complexity _ fun _ => false)
  refine card_le_card fun i hi => mem_filter.2 ⟨mem_univ i, ?_⟩
  have hρ := Cslib.Circuits.Boolean.Restriction.mem_free.1 hi
  set y := ρ.fill fun _ => false
  have hfill : ρ.fill (Function.update (fun _ => false) i !false) = Function.update y i !y i := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [y, Cslib.Circuits.Boolean.Restriction.fill, hρ]
    · simp [y, Cslib.Circuits.Boolean.Restriction.fill, hj]
  simp only [hfill]
  rw [parity, parityOn_update_not (mem_univ i)]
  cases parityOn univ y <;> decide

private theorem chain_parity :
    n ≤ sensitivity (parity n) ∧ certificateComplexity (parity n) ≤ n :=
  ⟨(sensitivityAt_parity (fun _ => false)).symm.trans_le
      (le_sup (f := sensitivityAt (parity n)) (mem_univ _)),
    (certificateComplexity_le_complexity _).trans complexity_parity.le⟩

theorem sensitivity_parity : sensitivity (parity n) = n :=
  le_antisymm ((sensitivity_le_blockSensitivity _).trans
    ((blockSensitivity_le_certificateComplexity _).trans chain_parity.2)) chain_parity.1

theorem blockSensitivity_parity : blockSensitivity (parity n) = n :=
  le_antisymm ((blockSensitivity_le_certificateComplexity _).trans chain_parity.2)
    (chain_parity.1.trans (sensitivity_le_blockSensitivity _))

theorem certificateComplexity_parity : certificateComplexity (parity n) = n :=
  le_antisymm chain_parity.2 (chain_parity.1.trans ((sensitivity_le_blockSensitivity _).trans
    (blockSensitivity_le_certificateComplexity _)))

end Cslib.DecisionTree
