/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Complexity.Classes.NP.Closure
import Complexity.Computability.Complexity.Classes.NP.Witness
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# The difference class DP

`DP` is the class of intersections of an NP language and a coNP language, equivalently differences
of two NP languages [Papadimitriou][Papadimitriou94]. The definition takes intersections of
languages; it does not require a language to belong to both `NP` and `coNP`. Completeness uses
polynomial-time many-one reductions and arbitrary
injective instance encodings.

## Main definitions

* `Cslib.Complexity.DP`, `Cslib.Complexity.DPHard`, `Cslib.Complexity.DPComplete`.

## Main results

* `Cslib.Complexity.mem_DP_iff_diff`: differences of NP languages.
* `Cslib.Complexity.inter_mem_DP`, `Cslib.Complexity.PolyTimeReducible.mem_DP`.
* `Cslib.Complexity.NPComplete.prod_coNPComplete`: the product of any NP-complete language and
  any coNP-complete language is DP-complete.

## References

* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β γ : Type} {enc : α ↪ List Bool} {A B : Set α}

/-- The class of languages expressible as the intersection of an NP and a coNP language. -/
def DP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ B ∈ NP enc, ∃ C ∈ coNP enc, A = B ∩ C}

/-- Every DP language, over any injective binary encoding, reduces to this language. -/
def DPHard (enc : α ↪ List Bool) (A : Set α) : Prop :=
  ∀ {β : Type} (encB : β ↪ List Bool) (B : Set β), B ∈ DP encB → PolyTimeReducible encB enc B A

/-- DP membership and hardness under polynomial-time many-one reductions. -/
def DPComplete (enc : α ↪ List Bool) (A : Set α) : Prop := A ∈ DP enc ∧ DPHard enc A

/-- DP is exactly the differences of two NP languages. -/
theorem mem_DP_iff_diff : A ∈ DP enc ↔ ∃ B ∈ NP enc, ∃ C ∈ NP enc, A = B \ C := by
  constructor
  · rintro ⟨B, hB, C, hC, rfl⟩
    exact ⟨B, hB, Cᶜ, hC, by simp⟩
  · rintro ⟨B, hB, C, hC, rfl⟩
    exact ⟨B, hB, Cᶜ, by simpa [mem_coNP] using hC, rfl⟩

/-- DP is closed under intersection. -/
theorem inter_mem_DP (hA : A ∈ DP enc) (hB : B ∈ DP enc) : A ∩ B ∈ DP enc := by
  obtain ⟨A₁, hA₁, A₂, hA₂, rfl⟩ := hA
  obtain ⟨B₁, hB₁, B₂, hB₂, rfl⟩ := hB
  exact ⟨A₁ ∩ B₁, inter_mem_NP hA₁ hB₁, A₂ ∩ B₂, inter_mem_coNP hA₂ hB₂, by
    ext a
    simp only [Set.mem_inter_iff]
    tauto⟩

/-- DP is closed under polynomial-time reductions. -/
theorem PolyTimeReducible.mem_DP {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ DP encB) : A ∈ DP enc := by
  obtain ⟨g, hg, hAB⟩ := h
  obtain ⟨B₁, h₁, B₂, h₂, rfl⟩ := hB
  exact ⟨g ⁻¹' B₁, PolyTimeReducible.mem_NP ⟨g, hg, fun _ => Iff.rfl⟩ h₁,
    g ⁻¹' B₂, PolyTimeReducible.mem_coNP ⟨g, hg, fun _ => Iff.rfl⟩ h₂,
    Set.ext hAB⟩

/-- An NP-complete problem paired with a coNP-complete problem is DP-complete. The two reductions
are computed independently and their outputs are paired. -/
theorem NPComplete.prod_coNPComplete {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} (hA : NPComplete encA A) (hB : coNPComplete encB B) :
    DPComplete (encPair encA encB) (A ×ˢ B) := by
  constructor
  · exact ⟨Prod.fst ⁻¹' A,
      PolyTimeReducible.mem_NP ⟨Prod.fst, .fst encA encB, fun _ => Iff.rfl⟩ hA.1,
      Prod.snd ⁻¹' B,
      PolyTimeReducible.mem_coNP ⟨Prod.snd, .snd encA encB, fun _ => Iff.rfl⟩ hB.1, rfl⟩
  · rintro γ encC C ⟨C₁, h₁, C₂, h₂, rfl⟩
    obtain ⟨f, hf, hCf⟩ := hA.2 encC C₁ h₁
    obtain ⟨g, hg, hCg⟩ := hB.2 encC C₂ h₂
    exact ⟨fun a => (f a, g a), hf.prod hg, fun a => by simp [hCf a, hCg a]⟩

end Cslib.Complexity
