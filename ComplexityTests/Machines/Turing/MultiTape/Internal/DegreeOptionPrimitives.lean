/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives

/-! Option construction and fixed defaults, with arbitrary encodings and growing runtime words. -/
open Turing.MultiTapeTM

example {α : Type*} (a : α ↪ List Bool) (o : Option α ↪ List Bool) [OptionEncoding a o] :
    ComputableInDegree some a o 1 1 := .optionSome

example {α : Type*} (a : α ↪ List Bool) (o : Option α ↪ List Bool) [OptionEncoding a o]
    (d : α) : ComputableInDegree (fun x => x.getD d) o a 1 1 := .getD d

example : ComputableInDegree some (Function.Embedding.refl (List Bool))
    (encOption (Function.Embedding.refl _)) 1 1 := .optionSome

example (d : List Bool) : ComputableInDegree (fun x => x.getD d)
    (encOption (Function.Embedding.refl _)) (Function.Embedding.refl _) 1 1 := .getD d

example (n : ℕ) : (encOption (Function.Embedding.refl _) (some (List.replicate n true))).length
    = n + 1 := by simp

example {α : Type*} (a : α ↪ List Bool) :
    ComputableInDegree (fun _ : Option α => none) (encOption a) (encOption a) 1 0 := .const none
