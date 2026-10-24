/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-! Projection clients using the standalone plain API, without the larger calculus imports. -/

open Turing.MultiTapeTM

universe u v

example {α : Type v} {β γ : Type u} {input : α ↪ List Bool} {left : β ↪ List Bool}
    {right : γ ↪ List Bool} {f : α → β × γ}
    (hf : ComputableInPolyTime f input (encPair left right)) :
    ComputableInPolyTime (fun a => (f a).1) input left := by fun_prop

-- The existing canonical theorem and its named implicit arguments remain directly available.
example {α : Type v} {β γ : Type u} {input : α ↪ List Bool} {left : β ↪ List Bool}
    {right : γ ↪ List Bool} {f : α → β × γ}
    (hf : ComputableInPolyTime f input (encPair left right)) :
    ComputableInPolyTime (fun a => (f a).1) input left :=
  ComputableInPolyTime.fst' (enc₁ := left) (enc₂ := right) hf

example {α β : Type u} (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInPolyTime (Prod.fst : α × β → α) (encPair left right) left := by fun_prop
