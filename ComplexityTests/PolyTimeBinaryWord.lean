/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Tactic.PolyTime

/-! Ordinary providers preserve unary division defaults and captured padded-row inputs. -/

open Turing.MultiTapeTM

example : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 / p.2)
    (encPair encUnary encUnary) encUnary := by fun_prop

example : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 % p.2)
    (encPair encUnary encUnary) encUnary := by fun_prop

example (n : ℕ) : n / 0 = 0 ∧ n % 0 = n := by simp

example : ComputableInPolyTime (fun word : List Bool => word) (encList encBool) encBits := by
  fun_prop

example {α : Type} {input : α ↪ List Bool} {width row : α → ℕ} {word : α → List Bool}
    (hwidth : ComputableInPolyTime width input encUnary)
    (hrow : ComputableInPolyTime row input encUnary)
    (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime (fun a => Cslib.BitString.listRow (width a) (row a) (word a))
      input encBits := by
  fail_if_success (clear hword; fun_prop)
  fun_prop

example : Cslib.BitString.listRow 0 7 [true] = [] := by decide
example : Cslib.BitString.listRow 3 0 [true] = [true, false, false] := by decide
