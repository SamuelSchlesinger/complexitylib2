/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime

/-! Ordinary plain composition and encoding-equivalence clients. -/

open Turing.MultiTapeTM

example {α β γ : Type*} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {f : β → γ} {g : α → β}
    (hf : ComputableInPolyTime f encB encC) (hg : ComputableInPolyTime g encA encB) :
    ComputableInPolyTime (f ∘ g) encA encC :=
  hf.comp hg

example {α β : Type*} {encA encA' : α ↪ List Bool} {encB encB' : β ↪ List Bool}
    (hA : EncodingEquiv encA encA') (hB : EncodingEquiv encB encB') {f : α → β}
    (hf : ComputableInPolyTime f encA encB) : ComputableInPolyTime f encA' encB' :=
  (EncodingEquiv.computableInPolyTime_iff hA hB).mp hf

example {α : Type*} {encA encB encC : α ↪ List Bool}
    (hAB : EncodingEquiv encA encB) (hBC : EncodingEquiv encB encC) :
    EncodingEquiv encA encC := hAB.trans hBC

example {α : Type*} (enc : α ↪ List Bool) : EncodingEquiv enc enc := .refl enc
