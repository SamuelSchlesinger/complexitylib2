/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-! # Plain unary enumeration and captured universal scans -/

open Turing.MultiTapeTM

example {α : Type} {input : α ↪ List Bool} {count : α → ℕ}
    (hcount : ComputableInPolyTime count input encUnary) :
    ComputableInPolyTime (fun a => List.range (count a)) input (encList encUnary) := by
  exact ComputableInPolyTime.range.comp hcount

example {α β : Type} {input : α ↪ List Bool} {element : β ↪ List Bool}
    {list : α → List β} {test : α → β → Bool}
    (hlist : ComputableInPolyTime list input (encList element))
    (htest : ComputableInPolyTime (fun p : α × β => test p.1 p.2)
      (encPair input element) encBool) :
    ComputableInPolyTime (fun a => (list a).all (test a)) input encBool := by
  exact ComputableInPolyTime.allWithInput hlist htest

example (test : ℕ → ℕ → Bool)
    (htest : ComputableInPolyTime (fun p : ℕ × ℕ => test p.1 p.2)
      (encPair encUnary encUnary) encBool) :
    ComputableInPolyTime (fun n => (List.range n).all (test n)) encUnary encBool := by
  exact ComputableInPolyTime.allWithInput ComputableInPolyTime.range htest

example (_count : List Bool → ℕ) : True := by
  fail_if_success
    have : ComputableInPolyTime (fun word => List.range (_count word))
        encBits (encList encUnary) := by fun_prop
  trivial

example (_test : ℕ → ℕ → Bool) : True := by
  fail_if_success
    have : ComputableInPolyTime (fun n => (List.range n).all (_test n))
        encUnary encBool := by fun_prop
  trivial

example : (List.range 0).all (fun _ => false) = true := by decide
