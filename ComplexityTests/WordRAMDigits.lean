/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.Multiword.Transfer
import Complexity.Computability.WordRAM.Multiword.Bitwise
import Complexity.Computability.WordRAM.Multiword.Shift

/-! Shared digit clients work without importing the full multiplication development. -/

namespace WordRAMDigitsTests

open Cslib.WordRAM Cslib.WordRAM.Multiword

open Lean Elab Command in
run_cmd do
  if (← getEnv).header.moduleNames.contains
      `Complexity.Computability.WordRAM.Multiword.Mul then
    throwError "digit operations must not import full multiplication"

-- The representation applies to arbitrary register counts, including zero and one.
example (x : Data 0) : value 2 x [] = 0 := rfl
example (x : Data 0) : Bounded 2 x [] := by simp [Bounded]
example (x : Data 1) : value 10 x [0, 0] = x.regs 0 + 10 * x.regs 0 := rfl

example (x : Data 5) :
    Exec 2 Workspace.setup x (Workspace.setupResult 2 x) 6 :=
  Workspace.exec_setup (by decide) x

example (x : Data 5) : (Workspace.setupResult 2 x).regs 4 = x.regs 4 :=
  Workspace.setup_digit 2 x (by dsimp [Workspace.IsDigit]; omega)

-- A minimal client can assemble digits without any multiplication theorem.
example (as : List (Fin 5)) (d : Fin 5) :
    (Transfer.assemble as d).size = 2 * as.length + 8 :=
  Transfer.size_assemble as d

end WordRAMDigitsTests
