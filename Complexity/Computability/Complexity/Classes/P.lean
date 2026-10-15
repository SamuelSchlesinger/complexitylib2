/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Encoding

/-!
# The class P

A decision problem is a set `A : Set α` of instances, together with an encoding
`enc : α ↪ List Bool` of instances as binary words, in the style of
`Turing.MultiTapeTM.DecidableInTimeAndSpace`. It is in `P` when a Boolean function deciding
membership is tidily computable in polynomial time (`Turing.MultiTapeTM.ComputableTidilyInPolyTime`)
with respect to `enc` and the encoding `Turing.MultiTapeTM.encBool` of answers
[Arora and Barak, Definition 1.13][AroraBarak09].

Polynomial time is taken in the tidy sense (the machine restores its work tapes and heads),
because that is the form in which polynomial-time computability is closed under composition.
That it agrees with the plain notion (`Turing.MultiTapeTM.ComputableInTimeAndSpace` with
polynomial bounds) is the tidy normal form theorem, which is part of the composition machinery
being developed upstream.

Mathlib's `Turing.TM2ComputableInPolyTime` is stated for Mathlib's two-stack machines; this file
uses cslib's multi-tape machines, which carry the time and space measures the rest of the
development is built on.

## Main definitions

* `Cslib.Complexity.P`: problems decidable in polynomial time.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type*}

/-- The problems decidable in polynomial time with respect to the encoding `enc`: `A ∈ P enc`
when a Boolean function deciding membership in `A` is computable in polynomial time. -/
def P (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f : α → Bool, ComputableTidilyInPolyTime f enc encBool ∧ ∀ a, a ∈ A ↔ f a = true}

theorem mem_P {enc : α ↪ List Bool} {A : Set α} :
    A ∈ P enc ↔
      ∃ f : α → Bool, ComputableTidilyInPolyTime f enc encBool ∧ ∀ a, a ∈ A ↔ f a = true :=
  Iff.rfl

end Cslib.Complexity
