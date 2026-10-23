/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.BitString.List.Operations

/-! # Clients of the padded-row API

Short words retain false padding, suffixes cannot change existing rows, and zero-width rows
remain empty. The old public crypto name still has its original statement.
-/

namespace ComplexityTests.BitStringRows

open Cslib

-- The indexing rule needs no lower bound on the input length.
example (word : List Bool) (row : ℕ) :
    (BitString.listRow 3 row word).getD 2 false = word.getD (row * 3 + 2) false :=
  BitString.getD_listRow (by decide)

example : (BitString.listRow 3 0 [true]).getD 2 false = false := by
  rw [BitString.getD_listRow (by decide)]
  rfl

example : (BitString.listRow 2 3 [true]).getD 1 false = false := by
  rw [BitString.getD_listRow (by decide)]
  rfl

example (suffix : List Bool) :
    BitString.listRow 2 1 ([[true, false], [false, true]].flatten ++ suffix) = [false, true] :=
  BitString.listRow_flatMap_append (width := 2) id [[true, false], [false, true]]
    (by simp) suffix 1 (by decide)

-- Even a nonempty suffix does not become part of a zero-width row.
example (suffix : List Bool) : BitString.listRow 0 1 ([[], []].flatten ++ suffix) = [] :=
  BitString.listRow_flatMap_append (width := 0) id [[], []] (by simp) suffix 1 (by decide)

example (word : List Bool) : BitString.listRow 0 0 word = [] := by
  rw [BitString.listRow_zero]
  rfl

end ComplexityTests.BitStringRows
