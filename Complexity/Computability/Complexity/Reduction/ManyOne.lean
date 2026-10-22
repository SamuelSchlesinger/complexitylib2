/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Option.Basic

/-!
# Many-one reductions by a class of maps

Most reductions of complexity theory have one shape: a map `f` of an admissible kind sends the
instances of `A` to instances of `B`, preserving membership. Here the admissible maps are an
arbitrary predicate `Good` on functions, so polynomial-time, logarithmic-space, computable and
first-order reductions are all instances. A `ManyOneReduction Good A B` is such a map as data, to
which constructions can attach further facts such as size bounds; `ManyOneReducibleBy Good A B`
says that one exists.

Reflexivity and transitivity are not assumed: they follow from closure of the admissible maps
under the identity and composition (`ManyOneReducibleBy.refl`, `ManyOneReducibleBy.trans`), which
holds for the machine-defined classes but has to be proved separately for others. A change of
representation transfers reductions when each admissible map is simulated, through partial
decodings, by an admissible map of representations (`ManyOneReducibleBy.lift`).

Mathlib's `ManyOneReducible` (`Mathlib/Computability/Reduce.lean`) is the computable reducibility
on `Primcodable` types, the instance of this shape for computable maps; it is not reused here.

## Main definitions

* `Cslib.Complexity.ManyOneReduction`: a many-one reduction by an admissible map, as data.
* `Cslib.Complexity.ManyOneReducibleBy`: many-one reducibility by admissible maps.

## Main results

* `Cslib.Complexity.ManyOneReducibleBy.refl`, `Cslib.Complexity.ManyOneReducibleBy.trans`:
  reflexivity and transitivity from identity and composition closure.
* `Cslib.Complexity.ManyOneReducibleBy.mono`: more admissible maps give more reductions.
* `Cslib.Complexity.ManyOneReducibleBy.compl`: reductions between complements.
* `Cslib.Complexity.ManyOneReducibleBy.lift`: transfer along partial decodings.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09],
  Definition 2.7.
-/

@[expose] public section

namespace Cslib.Complexity

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w}

/-- A many-one reduction of `A` to `B` by an admissible map: `toFun` satisfies `Good` and
`a ∈ A ↔ toFun a ∈ B` for every `a`. -/
structure ManyOneReduction (Good : (α → β) → Prop) (A : Set α) (B : Set β) where
  /-- The reduction map. -/
  toFun : α → β
  /-- The map is admissible. -/
  good : Good toFun
  /-- The map preserves membership in both directions. -/
  mem_iff : ∀ a, a ∈ A ↔ toFun a ∈ B

/-- `A` many-one reduces to `B` by an admissible map: some `f` satisfying `Good` has
`a ∈ A ↔ f a ∈ B` for every `a`. -/
def ManyOneReducibleBy (Good : (α → β) → Prop) (A : Set α) (B : Set β) : Prop :=
  ∃ f : α → β, Good f ∧ ∀ a, a ∈ A ↔ f a ∈ B

variable {Good : (α → β) → Prop} {A : Set α} {B : Set β}

/-- A reduction witnesses reducibility. -/
theorem ManyOneReduction.reducibleBy (r : ManyOneReduction Good A B) :
    ManyOneReducibleBy Good A B :=
  ⟨r.toFun, r.good, r.mem_iff⟩

/-- Reducibility is the existence of a reduction. -/
theorem manyOneReducibleBy_iff_nonempty :
    ManyOneReducibleBy Good A B ↔ Nonempty (ManyOneReduction Good A B) :=
  ⟨fun ⟨f, hf, h⟩ => ⟨⟨f, hf, h⟩⟩, fun ⟨r⟩ => r.reducibleBy⟩

/-- A reduction chosen from reducibility. -/
noncomputable def ManyOneReducibleBy.reduction (h : ManyOneReducibleBy Good A B) :
    ManyOneReduction Good A B :=
  (manyOneReducibleBy_iff_nonempty.mp h).some

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

end Cslib.Complexity
