/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Embedding.Basic
import Mathlib.Order.BooleanAlgebra.Set

/-!
# Many-one reductions by a class of maps

Most reductions of complexity theory have one shape: a map `f` of an admissible kind sends the
instances of `A` to instances of `B`, preserving membership. Here the admissible maps are an
arbitrary predicate `Good` on functions, and `ManyOneReducibleBy Good A B` says that such a map
exists. Polynomial-time and logarithmic-space reductions of encoded problems, and first-order
reductions of ordered queries, are instances.

Reflexivity and transitivity are not assumed: they follow from closure of the admissible maps
under the identity and composition (`ManyOneReducibleBy.refl`, `ManyOneReducibleBy.trans`), which
holds for the machine-defined classes but has to be proved separately for others. A change of
representation transfers reductions when each admissible map is simulated, through partial
decodings, by an admissible map of representations (`ManyOneReducibleBy.lift`).

A class of problems is given, as elsewhere in the library, by a set of problems for every type of
instances and every encoding of them as bit strings. Since admissibility of a map generally
depends on the encodings, hardness is stated for a reducibility `R enc A B` indexed by the encoding
`enc` of the source instances, such as `ManyOneReducibleBy (Good enc) A B`: `B` is hard for a class
`𝒞` (`HardUnder R 𝒞 B`) when every problem `A` in `𝒞`, with any encoding `enc`, has `R enc A B`,
and complete (`CompleteUnder R 𝒞 encB B`) when it also belongs to `𝒞`. Polynomial-time and
logspace hardness and completeness are instances, whose unfoldings mention their own named
reducibilities.

Mathlib's `ManyOneReducible` (`Mathlib/Computability/Reduce.lean`) is the computable reducibility
on `Primcodable` types, the instance of this shape for computable maps; it is not reused here.

## Main definitions

* `Cslib.Complexity.ManyOneReducibleBy`: many-one reducibility by admissible maps.
* `Cslib.Complexity.HardUnder`, `Cslib.Complexity.CompleteUnder`: hardness and completeness for a
  class under a reducibility.

## Main results

* `Cslib.Complexity.ManyOneReducibleBy.refl`, `Cslib.Complexity.ManyOneReducibleBy.trans`:
  reflexivity and transitivity from identity and composition closure.
* `Cslib.Complexity.ManyOneReducibleBy.mono`: more admissible maps give more reductions.
* `Cslib.Complexity.ManyOneReducibleBy.compl`: reductions between complements.
* `Cslib.Complexity.ManyOneReducibleBy.lift`: transfer along partial decodings.
* `Cslib.Complexity.HardUnder.trans`: hardness transfers along reductions.
* `Cslib.Complexity.HardUnder.mono`, `Cslib.Complexity.CompleteUnder.mono`: a weaker reducibility
  preserves hardness and completeness.
* `Cslib.Complexity.HardUnder.compl`, `Cslib.Complexity.CompleteUnder.compl`: complements of hard
  and complete problems.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09],
  Definition 2.7.
-/

@[expose] public section

namespace Cslib.Complexity

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w}

/-- `A` many-one reduces to `B` by an admissible map: some `f` satisfying `Good` has
`a ∈ A ↔ f a ∈ B` for every `a`. -/
def ManyOneReducibleBy (Good : (α → β) → Prop) (A : Set α) (B : Set β) : Prop :=
  ∃ f : α → β, Good f ∧ ∀ a, a ∈ A ↔ f a ∈ B

variable {Good : (α → β) → Prop} {A : Set α} {B : Set β}

namespace ManyOneReducibleBy

/-- Every problem reduces to itself when the identity is admissible. -/
theorem refl {Good : (α → α) → Prop} (hid : Good id) (A : Set α) : ManyOneReducibleBy Good A A :=
  ⟨id, hid, fun _ => Iff.rfl⟩

/-- Reductions compose when composites of admissible maps are admissible. The three classes of
maps may differ, as they do when admissibility depends on encodings. -/
theorem trans {Good₁ : (α → β) → Prop} {Good₂ : (β → γ) → Prop} {Good₃ : (α → γ) → Prop}
    {C : Set γ} (hcomp : ∀ f g, Good₁ f → Good₂ g → Good₃ (g ∘ f))
    (hAB : ManyOneReducibleBy Good₁ A B) (hBC : ManyOneReducibleBy Good₂ B C) :
    ManyOneReducibleBy Good₃ A C :=
  let ⟨f, hf, hfAB⟩ := hAB
  let ⟨g, hg, hgBC⟩ := hBC
  ⟨g ∘ f, hcomp f g hf hg, fun a => (hfAB a).trans (hgBC (f a))⟩

/-- More admissible maps give more reductions. -/
theorem mono {Good' : (α → β) → Prop} (hle : ∀ f, Good f → Good' f)
    (h : ManyOneReducibleBy Good A B) : ManyOneReducibleBy Good' A B :=
  let ⟨f, hf, hAB⟩ := h
  ⟨f, hle f hf, hAB⟩

/-- A reduction from `A` to `B` is also a reduction from `Aᶜ` to `Bᶜ`. -/
theorem compl (h : ManyOneReducibleBy Good A B) : ManyOneReducibleBy Good Aᶜ Bᶜ :=
  let ⟨f, hf, hAB⟩ := h
  ⟨f, hf, fun a => not_congr (hAB a)⟩

/-- **Transfer along partial decodings.** Suppose representations `α'` and `β'` partially decode
to `α` and `β`, and every admissible map `f` is simulated by an admissible map `F` of
representations, in that `F` decodes to `f` on decodable inputs and to nothing elsewhere. Then a
reduction of `A` to `B` gives one of the representations of members of `A` to those of members of
`B`. -/
theorem lift {α' : Type w} {β' : Type x} {Good' : (α' → β') → Prop}
    (dec : α' → Option α) (dec' : β' → Option β)
    (hsim : ∀ f, Good f → ∃ F, Good' F ∧ ∀ y, dec' (F y) = (dec y).map f)
    (h : ManyOneReducibleBy Good A B) :
    ManyOneReducibleBy Good' {y | ∃ a ∈ A, dec y = some a} {z | ∃ b ∈ B, dec' z = some b} := by
  obtain ⟨f, hf, hAB⟩ := h
  obtain ⟨F, hF, hFf⟩ := hsim f hf
  refine ⟨F, hF, fun y => ?_⟩
  simp only [Set.mem_ofPred_eq, hFf]
  cases dec y with
  | none => simp
  | some a => simpa using hAB a

end ManyOneReducibleBy

/-! ### Hardness and completeness -/

section Hardness

variable {P : Type → Type u} {Q : Type v} {Q' : Type w}

/-- `B` is hard for the class `𝒞` under the reducibility `R`: every problem in `𝒞`, with any
encoding `enc` of its instances, reduces to `B`, in that `R enc A B`. -/
def HardUnder (R : ∀ {α : Type}, (α ↪ List Bool) → P α → Q → Prop)
    (𝒞 : ∀ {α : Type}, (α ↪ List Bool) → Set (P α)) (B : Q) : Prop :=
  ∀ {α : Type} (enc : α ↪ List Bool) (A : P α), A ∈ 𝒞 enc → R enc A B

/-- `B` is complete for the class `𝒞` under the reducibility `R`: it is in `𝒞`, with the encoding
`encB`, and is `𝒞`-hard under `R`. -/
def CompleteUnder {β : Type} (R : ∀ {α : Type}, (α ↪ List Bool) → P α → P β → Prop)
    (𝒞 : ∀ {α : Type}, (α ↪ List Bool) → Set (P α)) (encB : β ↪ List Bool) (B : P β) :
    Prop :=
  B ∈ 𝒞 encB ∧ HardUnder @R @𝒞 B

/-- A weaker reducibility preserves hardness. -/
theorem HardUnder.mono {R R' : ∀ {α : Type}, (α ↪ List Bool) → P α → Q → Prop}
    {𝒞 : ∀ {α : Type}, (α ↪ List Bool) → Set (P α)} {B : Q}
    (hR : ∀ {α : Type} (enc : α ↪ List Bool) (A : P α), R enc A B → R' enc A B)
    (hB : HardUnder @R @𝒞 B) : HardUnder @R' @𝒞 B :=
  fun enc A hA => hR enc A (hB enc A hA)

/-- **Hardness transfers along a reduction** `S B C` that composes with `R`-reductions to `B` into
`R'`-reductions to `C`. -/
theorem HardUnder.trans {R : ∀ {α : Type}, (α ↪ List Bool) → P α → Q → Prop}
    {R' : ∀ {α : Type}, (α ↪ List Bool) → P α → Q' → Prop}
    {𝒞 : ∀ {α : Type}, (α ↪ List Bool) → Set (P α)}
    {S : Q → Q' → Prop} {B : Q} {C : Q'}
    (hRS : ∀ {α : Type} (enc : α ↪ List Bool) (A : P α), R enc A B → S B C → R' enc A C)
    (hB : HardUnder @R @𝒞 B) (hBC : S B C) : HardUnder @R' @𝒞 C :=
  fun enc A hA => hRS enc A (hB enc A hA) hBC

/-- A weaker reducibility preserves completeness. -/
theorem CompleteUnder.mono {β : Type}
    {R R' : ∀ {α : Type}, (α ↪ List Bool) → P α → P β → Prop}
    {𝒞 : ∀ {α : Type}, (α ↪ List Bool) → Set (P α)} {encB : β ↪ List Bool}
    {B : P β} (hR : ∀ {α : Type} (enc : α ↪ List Bool) (A : P α), R enc A B → R' enc A B)
    (hB : CompleteUnder @R @𝒞 encB B) : CompleteUnder @R' @𝒞 encB B :=
  ⟨hB.1, HardUnder.mono hR hB.2⟩

variable {R : ∀ {α : Type}, (α ↪ List Bool) → Set α → Set β → Prop}
  {𝒞 𝒟 : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}

/-- If `R` relates complements and the complement of every problem in `𝒟` is in `𝒞`, the
complement of a `𝒞`-hard problem is `𝒟`-hard. -/
theorem HardUnder.compl (hR : ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α), R enc A B →
    R enc Aᶜ Bᶜ) (h𝒟𝒞 : ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α), A ∈ 𝒟 enc → Aᶜ ∈ 𝒞 enc)
    (hB : HardUnder @R @𝒞 B) : HardUnder @R @𝒟 Bᶜ :=
  fun enc A hA => compl_compl A ▸ hR enc Aᶜ (hB enc Aᶜ (h𝒟𝒞 enc A hA))

/-- If `R` relates complements and the problems in `𝒟` are exactly the complements of the
problems in `𝒞`, the complement of a `𝒞`-complete problem is `𝒟`-complete. -/
theorem CompleteUnder.compl {β : Type}
    {R : ∀ {α : Type}, (α ↪ List Bool) → Set α → Set β → Prop} {encB : β ↪ List Bool}
    {B : Set β} (hR : ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α), R enc A B → R enc Aᶜ Bᶜ)
    (h𝒟𝒞 : ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α), A ∈ 𝒟 enc ↔ Aᶜ ∈ 𝒞 enc)
    (hB : CompleteUnder @R @𝒞 encB B) : CompleteUnder @R @𝒟 encB Bᶜ :=
  ⟨(h𝒟𝒞 encB Bᶜ).2 ((compl_compl B).symm ▸ hB.1),
    HardUnder.compl hR (fun enc A hA => (h𝒟𝒞 enc A).1 hA) hB.2⟩

end Hardness

end Cslib.Complexity
