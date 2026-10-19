/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.Functions
public import Complexity.Computability.Communication.Operations

/-!
# Intersection and inclusion

Disjointness of `n`-bit strings, read as subsets of the `n` positions, needs `n + 1` bits
(`ecomplexity_disjointness`). Since negating the output does not change the communication
complexity, so does *intersection*, deciding whether the two sets meet
(`ecomplexityFun_not_disjointness`). *Inclusion* `x ≤ y` (pointwise, so that the set of positions
where `x` is `true` lies in that of `y`) also needs `n + 1` bits
(`ecomplexityFun_decide_le`): in any partial order the diagonal pairs `(x, x)` form a fooling set
for `≤` with value `true`, by antisymmetry (`isFoolingSet_le`)
[Kushilevitz and Nisan, Chapter 1][KushilevitzNisan1997].

## Main results

* `Cslib.Communication.isFoolingSet_le`: the diagonal is a fooling set for a partial order.
* `Cslib.Communication.ecomplexityFun_not_disjointness`: intersection of `n` bits needs `n + 1`
  bits.
* `Cslib.Communication.ecomplexityFun_decide_le`: inclusion of `n` bits needs `n + 1` bits.

## References

* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Communication

open Finset

variable {X : Type*} {n : ℕ}

/-- In a partial order, the diagonal pairs form a fooling set for `≤` with value `true`. -/
theorem isFoolingSet_le [PartialOrder X] [DecidableLE X] [DecidableEq X] (s : Finset X) :
    IsFoolingSet (fun x y => decide (x ≤ y)) true (s.image fun x => (x, x)) := by
  simp only [IsFoolingSet, mem_image]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    simp
  · rintro _ ⟨x, -, rfl⟩ _ ⟨x', -, rfl⟩ h h'
    simp only [decide_eq_true_eq] at h h'
    rw [le_antisymm h h']

/-- **Intersection of `n` bits needs `n + 1` bits**, for `0 < n`: deciding whether two subsets of
`n` positions meet costs as much as disjointness. -/
theorem ecomplexityFun_not_disjointness (hn : 0 < n) :
    Protocol.ecomplexityFun (fun x y : BitString n => !disjointness x y) = n + 1 := by
  rw [Protocol.ecomplexityFun_not]
  exact ecomplexity_disjointness hn

/-- **Inclusion of `n` bits needs `n + 1` bits**, for `0 < n`: deciding whether `x ≤ y`
pointwise, that is, whether the set of positions where `x` is `true` lies in that of `y`. -/
theorem ecomplexityFun_decide_le (hn : 0 < n) :
    Protocol.ecomplexityFun (fun x y : BitString n => decide (x ≤ y)) = n + 1 := by
  refine le_antisymm (Protocol.ecomplexityFun_le_succ _)
    ((isFoolingSet_le univ).succ_le_ecomplexity ⟨fun _ => true, fun _ => false, ?_⟩ ?_)
  · intro h
    have h' : true ≤ false := of_decide_eq_true h ⟨0, hn⟩
    exact absurd h' (by decide)
  · rw [card_image_of_injective _ fun x y h => congrArg Prod.fst h, card_univ, BitString.card]

end Cslib.Communication
