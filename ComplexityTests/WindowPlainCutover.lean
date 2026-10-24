/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Window

/-! Ordinary automation for growing signed windows and total clamped input-head motion. -/

open Turing.MultiTapeTM

example : ComputableInPolyTime Turing.windowList encUnary (encList encInt) := by fun_prop

-- The actual negative-position serialization client retains its binary numbering.
example : ComputableInPolyTime
    (fun n => (Turing.windowList n).map Equiv.intEquivNat) encUnary (encList encNat) :=
  (ComputableInPolyTime.map
    (ComputableInPolyTime.unary_to_binary.comp ComputableInPolyTime.int_equivNat)).comp
    Turing.computableInPolyTime_windowList

example (direction : SignType) : ComputableInPolyTime
    (fun p : ℕ × ℕ => Turing.moveInputPosNat p.1 p.2 direction)
    (encPair encUnary encUnary) encUnary := by fun_prop

example : Turing.windowList 0 = [0] := by decide
example : Turing.windowList 2 = [-2, -1, 0, 1, 2] := by decide
example (n : ℕ) : (Turing.windowList n).length = 2 * n + 1 := by
  simp only [Turing.windowList, List.length_map, List.length_range]

example : Turing.moveInputPosNat 0 0 .neg = 0 := by decide
example : Turing.moveInputPosNat 0 0 .pos = 1 := by decide
example : Turing.moveInputPosNat 0 99 .zero = 1 := by decide
example : Turing.moveInputPosNat 2 99 .neg = 3 := by decide

run_meta do
  for name in [`Turing.computableTidilyInPolyTime_windowList,
      `Turing.MultiTapeTM.ComputableTidilyInPolyTime.moveInputPosNat] do
    if (← Lean.getEnv).contains name then
      throwError "retired window rule remains: {name}"
