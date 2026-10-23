/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract regression tests)

import ComplexityAbstracts.CookLevinAbstract
import ComplexityAbstracts.SubsetSumAbstract
import ComplexityAbstracts.TQBFAbstract

/-! # Clients using the original named encoding arguments

An alias alone inherits its target's binder names. These clients ensure that extracting the
shared foundations preserves the old `encA` and `encB` named arguments as well as the types.
-/

namespace ComplexityTests.Abstracts.Compatibility

set_option linter.deprecated false

variable {α β : Type} (f : α → β) (encA : α ↪ List Bool) (encB : β ↪ List Bool)

example : CookLevinAbstract.encodePair (encA := encA) (encB := encB) =
    Encoding.encodePair encA encB := rfl

example : Function.Injective (Encoding.encodePair encA encB) :=
  CookLevinAbstract.encodePair_injective (encA := encA) (encB := encB)

example : CookLevinAbstract.encPair (encA := encA) (encB := encB) =
    Encoding.encPair encA encB := rfl

example : CookLevinAbstract.ComputableInPolyTime f (encA := encA) (encB := encB) ↔
    Computation.PolyTime f encA encB := Iff.rfl

example : SubsetSumAbstract.encodePair (encA := encA) (encB := encB) =
    Encoding.encodePair encA encB := rfl

example : Function.Injective (Encoding.encodePair encA encB) :=
  SubsetSumAbstract.encodePair_injective (encA := encA) (encB := encB)

example : SubsetSumAbstract.encPair (encA := encA) (encB := encB) =
    Encoding.encPair encA encB := rfl

example : SubsetSumAbstract.ComputableInPolyTime f (encA := encA) (encB := encB) ↔
    Computation.PolyTime f encA encB := Iff.rfl

example : TQBFAbstract.encodePair (encA := encA) (encB := encB) =
    Encoding.encodePair encA encB := rfl

example : TQBFAbstract.ComputableInPolyTime f (encA := encA) (encB := encB) ↔
    Computation.PolyTime f encA encB := Iff.rfl

end ComplexityTests.Abstracts.Compatibility
