/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Halting.Computable

/-!
# Mapping reductions

`MappingReducible encA encB A B`: a computable function (`Turing.MultiTapeTM.IsComputable`) with
respect to the encodings `encA` and `encB` maps the instances of `A` to instances of `B` and the
other instances to instances outside `B` [Sipser, Definition 5.20][Sipser2013]. Mapping
reducibility is a preorder, and decidability transfers backwards along reductions
(`Turing.MultiTapeTM.IsDecidable.of_mappingReducible`), so undecidability transfers forwards
(`Turing.MultiTapeTM.MappingReducible.not_isDecidable`).

A polynomial-time reduction (`Cslib.Complexity.PolyTimeReducible`) is a mapping reduction, its
function being computable (`Turing.MultiTapeTM.ComputableTidilyInPolyTime.isComputable`).
Mathlib's `ManyOneReducible` is the analogous notion for Mathlib's partial recursive functions on
`Primcodable` types; `Turing.MultiTapeTM.MappingReducible.manyOneReducible` in
`MultiTape.Halting.Partrec` connects the two notions.

## Main definitions

* `Turing.MultiTapeTM.MappingReducible`: mapping reducibility.

## Main results

* `Turing.MultiTapeTM.MappingReducible.refl`, `Turing.MultiTapeTM.MappingReducible.trans`: mapping
  reducibility is a preorder.
* `Turing.MultiTapeTM.MappingReducible.compl`: a reduction is one between the complements.
* `Turing.MultiTapeTM.IsDecidable.of_mappingReducible`,
  `Turing.MultiTapeTM.MappingReducible.not_isDecidable`: transfer of decidability and of
  undecidability.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β γ : Type*}

/-- `A` is mapping reducible to `B`: some function `f`, computable with respect to `encA` and
`encB`, satisfies `a ∈ A ↔ f a ∈ B`. -/
def MappingReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (A : Set α) (B : Set β) :
    Prop :=
  ∃ f : α → β, IsComputable f encA encB ∧ ∀ a, a ∈ A ↔ f a ∈ B

variable {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {A : Set α} {B : Set β} {C : Set γ}

/-- Every set reduces to itself by the identity. -/
@[refl]
theorem MappingReducible.refl (encA : α ↪ List Bool) (A : Set α) :
    MappingReducible encA encA A A :=
  ⟨id, isComputable_id encA, fun _ => Iff.rfl⟩

/-- **Mapping reductions compose.** -/
@[trans]
theorem MappingReducible.trans (hAB : MappingReducible encA encB A B)
    (hBC : MappingReducible encB encC B C) : MappingReducible encA encC A C :=
  let ⟨f, hf, hAB⟩ := hAB
  let ⟨g, hg, hBC⟩ := hBC
  ⟨g ∘ f, hg.comp hf, fun a => (hAB a).trans (hBC (f a))⟩

/-- A reduction from `A` to `B` is also a reduction from `Aᶜ` to `Bᶜ`. -/
theorem MappingReducible.compl (h : MappingReducible encA encB A B) :
    MappingReducible encA encB Aᶜ Bᶜ :=
  let ⟨f, hf, hAB⟩ := h
  ⟨f, hf, fun a => not_congr (hAB a)⟩

/-- **Decidability transfers backwards along mapping reductions.** -/
theorem IsDecidable.of_mappingReducible (hB : IsDecidable B encB)
    (h : MappingReducible encA encB A B) : IsDecidable A encA :=
  let ⟨f, hf, hAB⟩ := h
  let ⟨g, hg, hB⟩ := hB.exists_isComputable
  isDecidable_iff.mpr ⟨g ∘ f, hg.comp hf, fun a => (hAB a).trans (hB (f a))⟩

/-- **Undecidability transfers forwards along mapping reductions.** -/
theorem MappingReducible.not_isDecidable (h : MappingReducible encA encB A B)
    (hA : ¬IsDecidable A encA) : ¬IsDecidable B encB :=
  fun hB => hA (hB.of_mappingReducible h)

end Turing.MultiTapeTM
