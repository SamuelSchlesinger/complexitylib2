/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.Complexity.Classes.P

/-!
# Polynomial-time many-one reductions

`PolyTimeReducible encA encB A B`: a function computable in polynomial time with respect to the
encodings `encA` and `encB` maps instances of `A` to instances of `B`, preserving membership [Arora
and Barak, Definition 2.7][AroraBarak09].

A class of problems is given, as `NP` or `coNP`, by a set of problems for every type of instances
and every encoding of them. A problem `B` is hard for such a class `C` when every problem in `C`,
with any encoding of its instances, reduces to `B` (`PolyTimeHard C encB B`), and complete when it
also belongs to `C` (`PolyTimeComplete C encB B`). `NPHard`, `NPComplete`, `coNPHard` and
`coNPComplete` are the instances for `NP` and `coNP`. When the problems of a class `D` are the
complements of those of `C`, the complement of a `C`-complete problem is `D`-complete
(`PolyTimeComplete.compl`).

Hardness quantifies over problems whose instances live in `Type`, with every encoding of instances.
Instances of complexity-theoretic problems are finite objects encoded as words, so this loses
nothing: a problem in a higher universe is equivalent, through its encoding, to the problem of
recognising the encodings of its members.

Mathlib's `ManyOneReducible` (`Mathlib/Computability/Reduce.lean`) is the computable, not the
polynomial-time, reducibility, and is stated for `Primcodable` types; it is not reused here.

## Main definitions

* `Cslib.Complexity.PolyTimeReducible`.
* `Cslib.Complexity.PolyTimeHard`, `Cslib.Complexity.PolyTimeComplete`: hardness and completeness
  for a class.
* `Cslib.Complexity.NPHard`, `Cslib.Complexity.NPComplete`.
* `Cslib.Complexity.coNPHard`, `Cslib.Complexity.coNPComplete`.

## Main results

* `Cslib.Complexity.P_subset_NP`, `Cslib.Complexity.P_subset_coNP`: `P` is contained in `NP` and
  in `coNP`.
* `Cslib.Complexity.NPComplete.P_eq_NP_of_mem_P`, `Cslib.Complexity.NPComplete.mem_P_iff`: an
  `NP`-complete problem is in `P` exactly when `P = NP` for every encoding.
* `Cslib.Complexity.NPComplete.mem_P_iff_mem_P`: two `NP`-complete problems are both in `P` or
  both outside it.
* `Cslib.Complexity.PolyTimeReducible.refl`, `Cslib.Complexity.PolyTimeReducible.trans`:
  polynomial-time reducibility is a preorder.
* `Cslib.Complexity.PolyTimeReducible.mem_P`: `P` is closed under polynomial-time reductions.
* `Cslib.Complexity.PolyTimeHard.trans`, `Cslib.Complexity.NPHard.trans`,
  `Cslib.Complexity.coNPHard.trans`: hardness transfers along polynomial-time reductions.
* `Cslib.Complexity.PolyTimeReducible.compl`: a reduction between problems is one between their
  complements.
* `Cslib.Complexity.PolyTimeHard.compl`, `Cslib.Complexity.PolyTimeComplete.compl`: complements of
  hard and complete problems.
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

/-- `B` is hard for the class `C` under polynomial-time many-one reductions: every problem in `C`,
with any encoding of its instances, reduces to `B`. -/
def PolyTimeHard (C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)) (encB : β ↪ List Bool)
    (B : Set β) : Prop :=
  ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α), A ∈ C enc → PolyTimeReducible enc encB A B

/-- `B` is complete for the class `C` under polynomial-time many-one reductions: it is in `C` and
every problem in `C` reduces to it. -/
def PolyTimeComplete {β : Type} (C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α))
    (encB : β ↪ List Bool) (B : Set β) : Prop :=
  B ∈ C encB ∧ PolyTimeHard C encB B

/-- Every problem in `NP`, with any encoding of its instances, reduces to `B`. -/
abbrev NPHard (encB : β ↪ List Bool) (B : Set β) : Prop := PolyTimeHard @NP encB B

/-- `B` is in `NP` and every problem in `NP` reduces to it. -/
abbrev NPComplete {β : Type} (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeComplete @NP encB B

/-- Every problem in `coNP`, with any encoding of its instances, reduces to `B`. -/
abbrev coNPHard (encB : β ↪ List Bool) (B : Set β) : Prop := PolyTimeHard @coNP encB B

/-- `B` is in `coNP` and every problem in `coNP` reduces to it. -/
abbrev coNPComplete {β : Type} (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeComplete @coNP encB B

/-- Hardness for the class `NP` is `NPHard`. -/
theorem polyTimeHard_NP_iff {encB : β ↪ List Bool} {B : Set β} :
    PolyTimeHard @NP encB B ↔ NPHard encB B := Iff.rfl

/-- Completeness for the class `NP` is `NPComplete`. -/
theorem polyTimeComplete_NP_iff {β : Type} {encB : β ↪ List Bool} {B : Set β} :
    PolyTimeComplete @NP encB B ↔ NPComplete encB B := Iff.rfl

/-- Hardness for the class `coNP` is `coNPHard`. -/
theorem polyTimeHard_coNP_iff {encB : β ↪ List Bool} {B : Set β} :
    PolyTimeHard @coNP encB B ↔ coNPHard encB B := Iff.rfl

/-- Completeness for the class `coNP` is `coNPComplete`. -/
theorem polyTimeComplete_coNP_iff {β : Type} {encB : β ↪ List Bool} {B : Set β} :
    PolyTimeComplete @coNP encB B ↔ coNPComplete encB B := Iff.rfl

variable {γ : Type*} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {A : Set α} {B : Set β} {C : Set γ}

/-- Every problem reduces to itself in polynomial time by the identity function. -/
@[refl]
theorem PolyTimeReducible.refl (encA : α ↪ List Bool) (A : Set α) :
    PolyTimeReducible encA encA A A :=
  ⟨id, ComputableTidilyInPolyTime.id', fun _ => Iff.rfl⟩

/-- Polynomial-time many-one reductions compose. -/
@[trans]
theorem PolyTimeReducible.trans (hAB : PolyTimeReducible encA encB A B)
    (hBC : PolyTimeReducible encB encC B C) : PolyTimeReducible encA encC A C :=
  let ⟨f, hf, hAB⟩ := hAB
  let ⟨g, hg, hBC⟩ := hBC
  ⟨g ∘ f, hg.comp hf, fun a => (hAB a).trans (hBC (f a))⟩

/-- **`P` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_P (hAB : PolyTimeReducible encA encB A B) (hB : B ∈ P encB) :
    A ∈ P encA :=
  let ⟨f, hf, hAB⟩ := hAB
  let ⟨g, hg, hB⟩ := hB
  ⟨g ∘ f, hg.comp hf, fun a => (hAB a).trans (hB (f a))⟩

/-- A reduction from `A` to `B` is also a reduction from `Aᶜ` to `Bᶜ`. -/
theorem PolyTimeReducible.compl (h : PolyTimeReducible encA encB A B) :
    PolyTimeReducible encA encB Aᶜ Bᶜ :=
  let ⟨f, hf, hAB⟩ := h
  ⟨f, hf, fun a => not_congr (hAB a)⟩

section Hardness

variable {𝒞 𝒟 : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}

/-- Hardness transfers along a polynomial-time reduction. -/
theorem PolyTimeHard.trans (hB : PolyTimeHard 𝒞 encB B) (hBC : PolyTimeReducible encB encC B C) :
    PolyTimeHard 𝒞 encC C :=
  fun enc X hX => (hB enc X hX).trans hBC

/-- If the complement of every problem in `𝒟` is in `𝒞`, the complement of a `𝒞`-hard problem is
`𝒟`-hard. -/
theorem PolyTimeHard.compl (h𝒟𝒞 : ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α), A ∈ 𝒟 enc →
    Aᶜ ∈ 𝒞 enc) (hB : PolyTimeHard 𝒞 encB B) : PolyTimeHard 𝒟 encB Bᶜ :=
  fun enc X hX => by simpa using (hB enc Xᶜ (h𝒟𝒞 enc X hX)).compl

/-- If the problems in `𝒟` are exactly the complements of the problems in `𝒞`, the complement of
a `𝒞`-complete problem is `𝒟`-complete. -/
theorem PolyTimeComplete.compl {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (h𝒟𝒞 : ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α), A ∈ 𝒟 enc ↔ Aᶜ ∈ 𝒞 enc)
    (hB : PolyTimeComplete 𝒞 encB B) : PolyTimeComplete 𝒟 encB Bᶜ :=
  ⟨(h𝒟𝒞 encB Bᶜ).2 (by simpa using hB.1),
    PolyTimeHard.compl (fun enc A hA => (h𝒟𝒞 enc A).1 hA) hB.2⟩

end Hardness

/-- `NP`-hardness transfers along a polynomial-time reduction. -/
theorem NPHard.trans (hA : NPHard encA A) (hAB : PolyTimeReducible encA encB A B) :
    NPHard encB B :=
  PolyTimeHard.trans hA hAB

/-- `coNP`-hardness transfers along a polynomial-time reduction. -/
theorem coNPHard.trans (hA : coNPHard encA A) (hAB : PolyTimeReducible encA encB A B) :
    coNPHard encB B :=
  PolyTimeHard.trans hA hAB

/-- The complement of an `NP`-hard problem is `coNP`-hard. -/
theorem NPHard.compl (h : NPHard encB B) : coNPHard encB Bᶜ :=
  PolyTimeHard.compl (fun _ _ hA => hA) h

/-- The complement of a `coNP`-hard problem is `NP`-hard. -/
theorem coNPHard.compl (h : coNPHard encB B) : NPHard encB Bᶜ :=
  PolyTimeHard.compl (fun _ _ hA => by simpa [mem_coNP] using hA) h

/-- The complement of an `NP`-complete problem is `coNP`-complete. -/
theorem NPComplete.compl {β : Type} {encB : β ↪ List Bool} {B : Set β} (h : NPComplete encB B) :
    coNPComplete encB Bᶜ :=
  PolyTimeComplete.compl (fun _ _ => Iff.rfl) h

/-- The complement of a `coNP`-complete problem is `NP`-complete. -/
theorem coNPComplete.compl {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (h : coNPComplete encB B) : NPComplete encB Bᶜ :=
  PolyTimeComplete.compl (fun _ _ => by simp [mem_coNP]) h

/-! ### `P` and `NP`-complete problems -/

/-- **`P ⊆ NP`**: a decider is a verifier ignoring its certificate. -/
theorem P_subset_NP {α : Type} {enc : α ↪ List Bool} : P enc ⊆ NP enc :=
  fun _ ⟨f, hf, hA⟩ => ⟨0, fun x => f x.1, hf.comp (ComputableTidilyInPolyTime.fst enc encBits),
    fun a => (hA a).trans ⟨fun h => ⟨[], by simp, h⟩, fun ⟨_, _, h⟩ => h⟩⟩

/-- **`P ⊆ coNP`**: `P` is closed under complement. -/
theorem P_subset_coNP {α : Type} {enc : α ↪ List Bool} : P enc ⊆ coNP enc :=
  fun _ hA => P_subset_NP (compl_mem_P hA)

/-- **An `NP`-complete problem in `P` gives `P = NP`**, for every encoding of instances: every
problem in `NP` reduces to it, and `P` is closed under polynomial-time reductions. -/
theorem NPComplete.P_eq_NP_of_mem_P {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (hB : NPComplete encB B) (h : B ∈ P encB) {α : Type} (enc : α ↪ List Bool) :
    P enc = NP enc :=
  P_subset_NP.antisymm fun A hA => (hB.2 enc A hA).mem_P h

/-- **An `NP`-complete problem is in `P` exactly when `P = NP`**, for every encoding of
instances. -/
theorem NPComplete.mem_P_iff {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (hB : NPComplete encB B) : B ∈ P encB ↔ ∀ {α : Type} (enc : α ↪ List Bool), P enc = NP enc :=
  ⟨fun h _ enc => hB.P_eq_NP_of_mem_P h enc, fun h => h encB ▸ hB.1⟩

/-- Two `NP`-complete problems are both in `P` or both outside it. -/
theorem NPComplete.mem_P_iff_mem_P {β γ : Type} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {B : Set β} {C : Set γ} (hB : NPComplete encB B) (hC : NPComplete encC C) :
    B ∈ P encB ↔ C ∈ P encC :=
  hB.mem_P_iff.trans hC.mem_P_iff.symm

end Cslib.Complexity
