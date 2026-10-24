/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Matrix.Binary

/-! A plain client of the topic-local matrix rule, without importing the calculus aggregate. -/

open Turing.MultiTapeTM

example {α : Type} {input : α ↪ List Bool} {cols width row col : α → ℕ}
    {word : α → List Bool} (hcols : ComputableInPolyTime cols input encUnary)
    (hwidth : ComputableInPolyTime width input encUnary)
    (hword : ComputableInPolyTime word input encBits)
    (hrow : ComputableInPolyTime row input encUnary)
    (hcol : ComputableInPolyTime col input encUnary) :
    ComputableInPolyTime
      (fun a => Cslib.Matrix.binaryEntry (cols a) (width a) (word a) (row a) (col a))
      input encNat := by fun_prop

run_meta do
  if (← Lean.getEnv).contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.matrixBinaryEntry then
    throwError "the superseded matrix construction export remains"

-- All dimensions and coordinates vary with the runtime input; entries stay binary encoded.
example : ComputableInPolyTime
    (fun p : ℕ × List Bool => Cslib.Matrix.binaryEntry p.1 p.1 p.2 p.1 p.1)
    (encPair encUnary encBits) encNat := by fun_prop

example : Cslib.Matrix.binaryEntry 2 0 [true, true] 9 9 = 0 := by decide
example : Cslib.Matrix.binaryEntry 2 3 [] 4 1 = 0 := by decide
example : Cslib.Matrix.binaryEntry 2 3 [true] 0 0 = 1 := by decide
example : Cslib.Matrix.binaryEntry 2 2 [false, true, true, false] 0 1 = 1 := by decide

-- Zero columns means zero row stride for this total accessor, not an invented emptiness guard.
example : Cslib.Matrix.binaryEntry 0 3 [true, true, true] 7 0 = 7 := by decide
