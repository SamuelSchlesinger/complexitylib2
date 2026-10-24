/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Foldl
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree

/-! Shared raw constructors are available through ordinary imports and preserve degree zero. -/

open Turing.MultiTapeTM

universe u v

example {α : Type u} {β : Type v} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {d e : ℕ}
    (h : ComputableInDegree f encIn encOut d e) :
    ComputableTidilyInDegree f encIn encOut d e := Internal.normalizeDegree h

example {α : Type u} {β : Type v} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {d e : ℕ}
    (h : ComputableTidilyInDegree f encIn encOut d e) :
    ComputableInDegree f encIn encOut d e := Internal.forgetDegree h

example : ∃ c, ComputableTidilyInTimeAndSpace Prod.fst (encPair encBits encBool) encBits
    (fun p => c * ((encPair encBits encBool p).length + 1))
    (fun p => c * ((encPair encBits encBool p).length + 1)) :=
  Internal.normalizeLinear (PairEncoding.fst encBool)

-- A real constant machine on an infinite input type has both cost and output degree zero.
example : ComputableTidilyInDegree (fun _ : List Bool => false) encBits encBool 0 0 := by
  obtain ⟨c, h⟩ := computableInTimeAndSpace_of_const (encIn := encBits) (encOut := encBool) false
  have hzero : ComputableInDegree (fun _ : List Bool => false) encBits encBool 0 0 :=
    ⟨⟨_, _, ⟨c, fun _ => by simp⟩, ⟨0, fun _ => by simp⟩, h⟩, ⟨1, fun _ => by simp⟩⟩
  exact Internal.normalizeDegree hzero

example {α β γ : Type u} {encIn : α ↪ List Bool} {enc₁ : β ↪ List Bool}
    {enc₂ : γ ↪ List Bool} {enc : β × γ ↪ List Bool} [PairEncoding enc₁ enc₂ enc]
    {f : α → β} {g : α → γ} {t₁ s₁ t₂ s₂ : α → ℕ}
    (hf : ComputableTidilyInTimeAndSpace f encIn enc₁ t₁ s₁)
    (hg : ComputableTidilyInTimeAndSpace g encIn enc₂ t₂ s₂) :
    ∃ c, ComputableTidilyInTimeAndSpace (fun a => (f a, g a)) encIn enc
      (fun a => c * (t₁ a + t₂ a + 1))
      (fun a => c * (s₁ a + s₂ a + (enc (f a, g a)).length + 1)) :=
  ComputableTidilyInTimeAndSpace.pair hf hg

-- Ordinary imports expose one shared polynomial-space construction operation.
example {α : Type u} {β : Type v} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (h : ComputableInPolySpace f encIn encOut) :
    ∃ (t : α → ℕ) (s : ℕ → ℕ), Cslib.PolynomiallyBounded s ∧
      ComputableTidilyInTimeAndSpace f encIn encOut t (fun a => s (encIn a).length) ∧
      ∀ a, (encOut (f a)).length ≤ s (encIn a).length :=
  Internal.normalizePolySpace h
