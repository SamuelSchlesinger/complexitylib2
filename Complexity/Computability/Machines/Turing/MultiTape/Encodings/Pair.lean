/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: subset of crei/tidy-universal `Encodings/Pair.lean`;
-- definitions only, delete when it lands

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Basic
public import Mathlib.Logic.Embedding.Basic

/-!
# The framed encoding of pairs

`encPair enc₁ enc₂` encodes a pair as its framed first component (`Turing.MultiTapeTM.frame`)
followed by its second component.

A verbatim subset of Christian Reitwiessner's `Encodings/Pair.lean` (branch
`crei/tidy-universal`), without the `PairEncoding` instance.

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

end Turing.MultiTapeTM
