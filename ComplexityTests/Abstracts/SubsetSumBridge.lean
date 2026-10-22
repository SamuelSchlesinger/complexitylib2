/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Problems.SubsetSum

/-!
# Bridge for the Subset Sum formal abstract

Connects the sublist-based `SubsetSum` definition in `SubsetSumAbstract.lean` to
`Cslib.Complexity.SubsetSum_npComplete`.
-/

namespace ComplexityTests.Abstracts.SubsetSumBridge

open Turing.MultiTapeTM Cslib.Complexity

theorem subsetSum_eq :
    {x : List ℕ × ℕ | ∃ s : List ℕ, s.Sublist x.1 ∧ s.sum = x.2} =
      Cslib.Complexity.SubsetSum := by
  ext x
  exact Cslib.Complexity.mem_SubsetSum_iff_sublist.symm

theorem subsetSum_npComplete :
    Cslib.Complexity.NPComplete (encPair (encList encNat) encNat)
      {x : List ℕ × ℕ | ∃ s : List ℕ, s.Sublist x.1 ∧ s.sum = x.2} := by
  rw [subsetSum_eq]
  exact Cslib.Complexity.SubsetSum_npComplete

end ComplexityTests.Abstracts.SubsetSumBridge
