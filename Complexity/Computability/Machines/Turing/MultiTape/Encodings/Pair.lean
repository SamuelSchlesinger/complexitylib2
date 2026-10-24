/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Append
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Basic
import Mathlib.Tactic.Linarith

import all Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm

/-!
# The framed encoding of pairs

`encPair enc₁ enc₂` encodes a pair as its framed first component (`Turing.MultiTapeTM.frame`)
followed by its second component. It has the capabilities of `Turing.MultiTapeTM.PairEncoding`.

## Main definitions

* `Turing.MultiTapeTM.encFramed`: an encoding with every encoded value framed.
* `Turing.MultiTapeTM.encPair`: the framed encoding of pairs.
-/

namespace Turing.MultiTapeTM

universe u

variable {α β : Type u}

/-- `enc` with every encoded value framed. -/
@[expose] public def encFramed (enc : α ↪ List Bool) : α ↪ List Bool :=
  ⟨fun a => frame (enc a), fun _ _ h => enc.injective (frame_injective h)⟩

/-- Pairs encoded as the framed first component followed by the second component. -/
@[expose] public def encPair (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) :
    α × β ↪ List Bool :=
  ⟨fun p => frame (enc₁ p.1) ++ enc₂ p.2, fun _ _ h =>
    Prod.ext (enc₁.injective (frame_append_inj h).1) (enc₂.injective (frame_append_inj h).2)⟩

@[simp]
public lemma encFramed_apply (enc : α ↪ List Bool) (a : α) : encFramed enc a = frame (enc a) :=
  rfl

variable {enc₁ : α ↪ List Bool} {enc₂ : β ↪ List Bool}

@[simp]
public lemma encPair_apply (p : α × β) : encPair enc₁ enc₂ p = frame (enc₁ p.1) ++ enc₂ p.2 :=
  rfl

public lemma length_encPair (p : α × β) :
    (encPair enc₁ enc₂ p).length = 2 * (enc₁ p.1).length + 1 + (enc₂ p.2).length := by
  simp

public lemma length_le_encPair_left (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) (p : α × β) :
    (enc₁ p.1).length ≤ (encPair enc₁ enc₂ p).length := by
  rw [length_encPair]; omega

public lemma length_le_encPair_right (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) (p : α × β) :
    (enc₂ p.2).length ≤ (encPair enc₁ enc₂ p).length := by
  rw [length_encPair]; omega

public instance : PairEncoding enc₁ enc₂ (encPair enc₁ enc₂) where
  fst := (ComputableInLinearTimeAndSpace.of_unframe fun p => by simp)
  snd := (ComputableInLinearTimeAndSpace.of_dropFrame fun p => by simp)
  pair := fun {_ encIn f g t s} hf hg => by
    have hfO : ComputableInBigO f encIn enc₁ t s :=
      ⟨1, hf.mono (fun _ => by simp) (fun _ => by simp)⟩
    have hgO : ComputableInBigO g encIn enc₂ t s :=
      ⟨1, hg.mono (fun _ => by simp) (fun _ => by simp)⟩
    obtain ⟨cf, hf⟩ := Internal.normalizeBigO hfO
    obtain ⟨cg, hg⟩ := Internal.normalizeBigO hgO
    obtain ⟨c₀, hframe⟩ := Internal.normalizeLinear
      (ComputableInLinearTimeAndSpace.of_frame (f := id)
        (encIn := enc₁) (encOut := encFramed enc₁) fun _ => rfl)
    -- vendored: crei's `comp` is `comp_linear` here, as cslib #1111 restates `comp`
    obtain ⟨c₁, hf'⟩ := ComputableTidilyInTimeAndSpace.comp_linear hframe hf
    obtain ⟨k, h⟩ := hf'.append hg (encOut := encPair enc₁ enc₂) (g := fun x => (f x, g x))
      fun _ => rfl
    refine ⟨(2 + c₀ + c₁ + k) * (cf + cg + 1),
      h.computableInTimeAndSpace.mono (fun x => ?_) (fun x => ?_)⟩
    · have h₀ := Nat.mul_le_mul_left c₀ (hf.length_le x)
      have h₁ := Nat.mul_le_mul_left c₁ (hf.length_le x)
      ring_nf at h₀ h₁ ⊢
      omega
    · have h₀ := Nat.mul_le_mul_left c₀
        (length_le_encPair_left enc₁ enc₂ (f x, g x))
      have h₁ := Nat.mul_le_mul_left c₁
        (length_le_encPair_left enc₁ enc₂ (f x, g x))
      ring_nf at h₀ h₁ ⊢
      omega

end Turing.MultiTapeTM
