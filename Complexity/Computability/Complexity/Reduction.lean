/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP

/-!
# Polynomial-time many-one reductions

`PolyTimeReducible encA encB A B`: a function computable in polynomial time with respect to the
encodings `encA` and `encB` maps instances of `A` to instances of `B`, preserving membership [Arora
and Barak, Definition 2.7][AroraBarak09]. `NPHard` and `NPComplete` are defined from it in the usual
way.

Hardness quantifies over problems whose instances live in `Type`, with every encoding of instances.
Instances of complexity-theoretic problems are finite objects encoded as words, so this loses
nothing: a problem in a higher universe is equivalent, through its encoding, to the problem of
recognising the encodings of its members.

Mathlib's `ManyOneReducible` (`Mathlib/Computability/Reduce.lean`) is the computable, not the
polynomial-time, reducibility, and is stated for `Primcodable` types; it is not reused here.

## Main definitions

* `Cslib.Complexity.PolyTimeReducible`.
* `Cslib.Complexity.NPHard`, `Cslib.Complexity.NPComplete`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β : Type*}

/-- `A` reduces to `B` in polynomial time: some `f`, computable in polynomial time with respect to
`encA` and `encB`, satisfies `a ∈ A ↔ f a ∈ B`. -/
def PolyTimeReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (A : Set α) (B : Set β) :
    Prop :=
  ∃ f : α → β, ComputableTidilyInPolyTime f encA encB ∧ ∀ a, a ∈ A ↔ f a ∈ B

/-- Every problem in `NP`, with any encoding of its instances, reduces to `B`. -/
def NPHard (encB : β ↪ List Bool) (B : Set β) : Prop :=
  ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α), A ∈ NP enc → PolyTimeReducible enc encB A B

/-- `B` is in `NP` and every problem in `NP` reduces to it. -/
def NPComplete {β : Type} (encB : β ↪ List Bool) (B : Set β) : Prop :=
  B ∈ NP encB ∧ NPHard encB B

end Cslib.Complexity
