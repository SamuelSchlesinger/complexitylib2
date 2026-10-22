/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import ComplexityTests.Abstracts.Check
import ComplexityTests.Abstracts.SubsetSumBridge

/-! # A formal abstract of Subset Sum NP-completeness

This file defines the binary Subset Sum decision problem on finite lists of
natural numbers and proves that it is NP-complete under polynomial-time
many-one reductions.

This abstract demonstrates the `allowing [...]` mode of `#check_abstract`:
the complexity class `Cslib.Complexity.NPComplete` and the standard framed
encodings (`encPair`, `encList`, `encNat`) are imported from `Complexitylib`'s
core model modules, while `#check_abstract` verifies that the problem definition
itself (`SubsetSum`) is completely self-contained and does not reference
`Complexity.Computability.Complexity.Problems.SubsetSum`.
-/

namespace ComplexityTests.Abstracts.SubsetSumAbstract

/-- An instance `(numbers, target) : List ℕ × ℕ` belongs to `SubsetSum` if some
subsequence (`List.Sublist`) of `numbers` sums to `target`. Using lists rather
than sets allows repeated numbers in the input; each occurrence may be chosen at
most once. -/
def SubsetSum : Set (List ℕ × ℕ) :=
  {x | ∃ s : List ℕ, s.Sublist x.1 ∧ s.sum = x.2}

/-- **Theorem (Karp):** Subset Sum is NP-complete under polynomial-time many-one
reductions when the input list and target sum are encoded in binary. -/
theorem subsetSum_npComplete :
    Cslib.Complexity.NPComplete
      (Turing.MultiTapeTM.encPair
        (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encNat)
        Turing.MultiTapeTM.encNat)
      SubsetSum :=
  SubsetSumBridge.subsetSum_npComplete

#check_abstract ComplexityTests.Abstracts.SubsetSumAbstract allowing [
  Complexity.Computability.Complexity.Reduction,
  Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair,
  Complexity.Computability.Machines.Turing.MultiTape.Encodings.List,
  Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
]

end ComplexityTests.Abstracts.SubsetSumAbstract
