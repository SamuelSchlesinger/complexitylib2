/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeClosure
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Primitives

/-! Independent-degree append controls, including degree zero on runtime-varying inputs. -/
open Turing.MultiTapeTM

example {α β γ δ : Type*} {a : α ↪ List Bool} {b : β ↪ List Bool}
    {c : γ ↪ List Bool} {d : δ ↪ List Bool} {f : α → β} {g : α → γ} {h : α → δ}
    {d₁ e₁ d₂ e₂ : ℕ} (hf : ComputableInDegree f a b d₁ e₁)
    (hg : ComputableInDegree g a c d₂ e₂)
    (hh : ∀ x, d (h x) = b (f x) ++ c (g x)) :
    ComputableInDegree h a d (max d₁ d₂) (max e₁ e₂) :=
  hf.append hg hh

example {α : Type*} (a : α ↪ List Bool) {f g : α → List Bool}
    (hf : ComputableInDegree f a (Function.Embedding.refl _) 0 0)
    (hg : ComputableInDegree g a (Function.Embedding.refl _) 0 0) :
    ComputableInDegree (fun x => f x ++ g x) a (Function.Embedding.refl _) 0 0 := by
  exact hf.append hg (fun _ => rfl)

example {α : Type*} (a : α ↪ List Bool) {f _g : α → List Bool}
    (_hf : ComputableInDegree f a (Function.Embedding.refl _) 0 0) : True := by
  fail_if_success
    have : ComputableInDegree (fun x => f x ++ _g x) a
        (Function.Embedding.refl _) 0 0 := by
      exact _hf.append (by assumption) (fun _ => rfl)
  trivial
