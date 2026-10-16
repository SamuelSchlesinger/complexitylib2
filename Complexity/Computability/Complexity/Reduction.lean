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
* `Cslib.Complexity.coNPHard`, `Cslib.Complexity.coNPComplete`.

## Main results

* `Cslib.Complexity.PolyTimeReducible.compl`: a reduction between problems is one between their
  complements.
* `Cslib.Complexity.NPHard.compl`, `Cslib.Complexity.coNPHard.compl`,
  `Cslib.Complexity.NPComplete.compl`, `Cslib.Complexity.coNPComplete.compl`: complements exchange
  hardness and completeness for `NP` and `coNP`.

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

/-- Every problem in `coNP`, with any encoding of its instances, reduces to `B`. -/
def coNPHard (encB : β ↪ List Bool) (B : Set β) : Prop :=
  ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α), A ∈ coNP enc → PolyTimeReducible enc encB A B

/-- `B` is in `coNP` and every problem in `coNP` reduces to it. -/
def coNPComplete {β : Type} (encB : β ↪ List Bool) (B : Set β) : Prop :=
  B ∈ coNP encB ∧ coNPHard encB B

variable {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}

/-- A reduction from `A` to `B` is also a reduction from `Aᶜ` to `Bᶜ`. -/
theorem PolyTimeReducible.compl (h : PolyTimeReducible encA encB A B) :
    PolyTimeReducible encA encB Aᶜ Bᶜ :=
  let ⟨f, hf, hAB⟩ := h
  ⟨f, hf, fun a => not_congr (hAB a)⟩

/-- The complement of an `NP`-hard problem is `coNP`-hard. -/
theorem NPHard.compl (h : NPHard encB B) : coNPHard encB Bᶜ :=
  fun enc A hA => by simpa using (h enc Aᶜ hA).compl

/-- The complement of a `coNP`-hard problem is `NP`-hard. -/
theorem coNPHard.compl (h : coNPHard encB B) : NPHard encB Bᶜ :=
  fun enc A hA => by simpa using (h enc Aᶜ (by simpa [mem_coNP] using hA)).compl

/-- The complement of an `NP`-complete problem is `coNP`-complete. -/
theorem NPComplete.compl {β : Type} {encB : β ↪ List Bool} {B : Set β} (h : NPComplete encB B) :
    coNPComplete encB Bᶜ :=
  ⟨by simpa [mem_coNP] using h.1, NPHard.compl h.2⟩

/-- The complement of a `coNP`-complete problem is `NP`-complete. -/
theorem coNPComplete.compl {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (h : coNPComplete encB B) : NPComplete encB Bᶜ :=
  ⟨h.1, coNPHard.compl h.2⟩

end Cslib.Complexity
