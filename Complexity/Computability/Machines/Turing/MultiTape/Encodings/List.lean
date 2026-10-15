/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: subset of crei/tidy-universal `Encodings/List.lean`;
-- definitions only, delete when it lands

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Basic
public import Mathlib.Logic.Embedding.Basic

/-!
# Encodings of lists

`encList enc` encodes a list as the concatenation of its framed elements
(`Turing.MultiTapeTM.frame`), for any encoding `enc` of the elements. Lists of Booleans also have
the plain encoding `encBits`, the list itself.

A verbatim subset of Christian Reitwiessner's `Encodings/List.lean` (branch
`crei/tidy-universal`), without the `ListEncoding` instances.

## Main definitions

* `Turing.MultiTapeTM.encList`: the concatenation of the framed elements.
* `Turing.MultiTapeTM.encBits`: lists of Booleans encoded as themselves.
-/

namespace Turing.MultiTapeTM

universe u

variable {α : Type u}

/-- Lists encoded as the concatenation of their framed elements. -/
@[expose] public def encList (enc : α ↪ List Bool) : List α ↪ List Bool :=
  ⟨fun l => l.flatMap (frame ∘ enc), fun l l' h => by
    induction l generalizing l' with
    | nil => cases l' <;> simp_all
    | cons a l ih =>
      cases l' with
      | nil => simp at h
      | cons a' l' => rw [enc.injective (frame_append_inj h).1, ih _ (frame_append_inj h).2]⟩

variable {enc : α ↪ List Bool}

@[simp]
public lemma encList_nil : encList enc [] = [] := rfl

@[simp]
public lemma encList_cons (a : α) (l : List α) :
    encList enc (a :: l) = frame (enc a) ++ encList enc l := rfl

/-- Lists of Booleans encoded as themselves. -/
@[expose] public def encBits : List Bool ↪ List Bool := Function.Embedding.refl _

@[simp]
public lemma encBits_apply (l : List Bool) : encBits l = l := rfl

end Turing.MultiTapeTM
