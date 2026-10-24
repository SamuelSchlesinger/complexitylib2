/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Foundations.Data.Matrix.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Polynomial-time access to binary matrix words

Rows and columns are supplied at runtime in unary. Entries are decoded from arbitrary raw words,
padding missing bits with `false`. The result uses binary natural encoding, so no conversion to a
unary value is required.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.matrixBinaryEntry`: uniform entry access with
  computed dimensions, indices and input word.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Read a fixed-width matrix entry from an arbitrary computed word. Dimensions and indices
are efficient unary values; the entry is returned in binary. -/
@[fun_prop]
theorem matrixBinaryEntry {α : Type} {input : α ↪ List Bool}
    {cols width row col : α → ℕ} {word : α → List Bool}
    (hcols : ComputableInPolyTime cols input encUnary)
    (hwidth : ComputableInPolyTime width input encUnary)
    (hword : ComputableInPolyTime word input encBits)
    (hrow : ComputableInPolyTime row input encUnary)
    (hcol : ComputableInPolyTime col input encUnary) :
    ComputableInPolyTime
      (fun a => Cslib.Matrix.binaryEntry (cols a) (width a) (word a) (row a) (col a))
      input encNat := by
  apply ComputableInPolyTime.of_tidy
  exact ComputableTidilyInPolyTime.bitsToNat.comp
    (ComputableTidilyInPolyTime.bitsRowWithInput hwidth.tidy
      (ComputableTidilyInPolyTime.unary_add.comp
        ((ComputableTidilyInPolyTime.unary_mul.comp
          (hrow.tidy.prod hcols.tidy)).prod hcol.tidy)) hword.tidy)

end Turing.MultiTapeTM.ComputableInPolyTime
