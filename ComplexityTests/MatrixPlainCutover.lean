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
