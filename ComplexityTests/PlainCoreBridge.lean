/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

import all Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime

/-! A core proof using only private normalized witnesses and the existing bound algebra.
It does not import the legacy plain bridge or the aggregate calculus. The composition argument
retains the original polynomial-bound proof credit. -/

open Turing.MultiTapeTM

example {α β γ : Type*} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {f : β → γ} {g : α → β}
    (hf : ComputableInPolyTime f encB encC) (hg : ComputableInPolyTime g encA encB) :
    ComputableInPolyTime (f ∘ g) encA encC := by
  obtain ⟨t₁, s₁, ht₁, hs₁, h₁⟩ := Internal.normalizePolyTime hg
  obtain ⟨t₂, s₂, ht₂, hs₂, h₂⟩ := Internal.normalizePolyTime hf
  have hl : PolyBounded (fun a => (encA a).length) (fun a => (encB (g a)).length) :=
    (PolyBounded.of_polynomiallyBounded _ ht₁).mono h₁.length_le
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.comp_linear h₂ h₁
  have hm := (PolyBounded.const c).mul (hl.add (PolyBounded.const 1))
  have ht := ((PolyBounded.of_polynomiallyBounded _ ht₁).add
    ((PolyBounded.of_polynomiallyBounded _ ht₂).comp hl)).add hm
  have hs := ((PolyBounded.of_polynomiallyBounded _ hs₁).add
    ((PolyBounded.of_polynomiallyBounded _ hs₂).comp hl)).add hm
  obtain ⟨T, hT, ht⟩ := ht
  obtain ⟨S, hS, hs⟩ := hs
  exact Internal.forgetPolyTime hT hS (h.mono ht hs)

example {α β : Type*} {encA encA' : α ↪ List Bool} {encB encB' : β ↪ List Bool}
    (hA : EncodingEquiv encA encA') (hB : EncodingEquiv encB encB') {f : α → β}
    (hf : ComputableInPolyTime f encA encB) : ComputableInPolyTime f encA' encB' :=
  (EncodingEquiv.computableInPolyTime_iff hA hB).mp hf

example {α : Type*} {encA encB encC : α ↪ List Bool}
    (hAB : EncodingEquiv encA encB) (hBC : EncodingEquiv encB encC) :
    EncodingEquiv encA encC := hAB.trans hBC

example {α : Type*} (enc : α ↪ List Bool) : EncodingEquiv enc enc := .refl enc
