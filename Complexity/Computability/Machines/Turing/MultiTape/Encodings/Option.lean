/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: subset of crei/tidy-universal `Encodings/Option.lean`;
-- definitions only, delete when it lands

public import Complexity.Init
public import Mathlib.Logic.Embedding.Basic

/-!
# The encoding of options

`encOption enc` encodes `none` as the empty word and `some a` as `true` followed by `enc a`.

A verbatim subset of Christian Reitwiessner's `Encodings/Option.lean` (branch
`crei/tidy-universal`), without the `OptionEncoding` instance.

## Main definitions

* `Turing.MultiTapeTM.encOption`: the encoding of options.
-/

namespace Turing.MultiTapeTM

universe u

variable {α : Type u}

/-- Options encoded with `none` as the empty word and `some a` as `true` followed by `enc a`. -/
@[expose] public def encOption (enc : α ↪ List Bool) : Option α ↪ List Bool :=
  ⟨fun o => o.elim [] (true :: enc ·), by rintro (_ | a) (_ | b) h <;> simp_all⟩

variable {enc : α ↪ List Bool}

@[simp]
public lemma encOption_none : encOption enc none = [] := rfl

@[simp]
public lemma encOption_some (a : α) : encOption enc (some a) = true :: enc a := rfl

end Turing.MultiTapeTM
