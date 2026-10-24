/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeUnaryPrimitives

/-! Unary certificates and their zero, one, and unbounded runtime-parameter boundaries. -/
open Turing.MultiTapeTM
example : ComputableInDegree (· + 1) encUnary encUnary 1 1 := .unary_succ
example : ComputableInDegree (· - 1) encUnary encUnary 1 1 := .unary_pred
example : encUnary (0 + 1) = [true] := rfl
example : encUnary (0 - 1) = [] := rfl
example : encUnary (1 - 1) = [] := rfl
example : encUnary (1 + 1) = [true, true] := rfl
example (n : ℕ) : (encUnary (n + 1)).length = n + 1 := by simp
example (n : ℕ) : (encUnary (n - 1)).length = n - 1 := by simp
