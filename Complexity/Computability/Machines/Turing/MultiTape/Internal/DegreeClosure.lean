/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.NormalForm
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Append
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair

/-!
# Direct closure of independent degree bounds

These constructions combine machine witnesses, retaining independent resource and encoded-output
degrees, including degree zero. No higher tidy asymptotic calculus is used.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInDegree

variable {α β γ δ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool} {d₁ e₁ d₂ e₂ : ℕ}

/-- Concatenate encoded outputs without merging their independent cost and output degrees. -/
theorem append {enc₂ : δ ↪ List Bool} {f₁ : α → β} {f₂ : α → δ} {g : α → γ}
    (h₁ : ComputableInDegree f₁ encIn encMid d₁ e₁)
    (h₂ : ComputableInDegree f₂ encIn enc₂ d₂ e₂)
    (hg : ∀ x, encOut (g x) = encMid (f₁ x) ++ enc₂ (f₂ x)) :
    ComputableInDegree g encIn encOut (max d₁ d₂) (max e₁ e₂) := by
  obtain ⟨t₁, s₁, ht₁, hs₁, k₁, Q₁, _, tm₁, htm₁⟩ := Internal.NormalForm.degree h₁
  obtain ⟨t₂, s₂, ht₂, hs₂, k₂, Q₂, _, tm₂, htm₂⟩ := Internal.NormalForm.degree h₂
  refine ⟨⟨_, _, ht₁.add_max ht₂, (hs₁.add_max hs₂).add_const (2 * max k₁ k₂),
    _, _, inferInstance, appendTM tm₁ tm₂, fun a => ?_⟩,
    (h₁.2.add_max h₂.2).mono fun a => by simp [hg]⟩
  simpa only [hg a] using ((htm₁ a).append (htm₂ a)).computesInTimeAndSpace

universe u

/-- Generic pairing retains the resource degree as its encoded-output bound. -/
theorem pair {α β₁ β₂ : Type u} {encIn : α ↪ List Bool}
    {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {enc : β₁ × β₂ ↪ List Bool} [hP : PairEncoding enc₁ enc₂ enc] {f : α → β₁} {g : α → β₂}
    (hf : ComputableInDegree f encIn enc₁ d₁ e₁)
    (hg : ComputableInDegree g encIn enc₂ d₂ e₂) :
    ComputableInDegree (fun x => (f x, g x)) encIn enc (max d₁ d₂) (max d₁ d₂) := by
  obtain ⟨t₁, s₁, ht₁, hs₁, k₁, Q₁, _, tm₁, h₁⟩ := Internal.NormalForm.degree hf
  obtain ⟨t₂, s₂, ht₂, hs₂, k₂, Q₂, _, tm₂, h₂⟩ := Internal.NormalForm.degree hg
  obtain ⟨c, k, Q, hfin, tm, h⟩ := hP.pair
    (t := fun a => t₁ a + t₂ a) (s := fun a => s₁ a + s₂ a)
    ⟨k₁, Q₁, inferInstance, tm₁, fun a =>
      (h₁ a).mono (Nat.le_add_right _ _) (Nat.le_add_right _ _)⟩
    ⟨k₂, Q₂, inferInstance, tm₂, fun a =>
      (h₂ a).mono (Nat.le_add_left _ _) (Nat.le_add_left _ _)⟩
  have ht := ((ht₁.add_max ht₂).add_const 1).smul c
  have hs := ((((hs₁.add_max hs₂).add ht).add_const 1).smul c)
  refine ⟨⟨_, _, ht, hs, k, Q, hfin, tm, fun a => ?_⟩,
    ht.mono fun a => (h a).length_output_le⟩
  refine ((h a).mono le_rfl ?_).computesInTimeAndSpace
  apply Nat.mul_le_mul_left
  have hl : (enc (f a, g a)).length ≤ c * (t₁ a + t₂ a + 1) :=
    (h a).length_output_le
  omega

/-- Framed pairing retains the independent encoded-output degrees. -/
theorem prod {α β₁ β₂ : Type u} {encIn : α ↪ List Bool}
    {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {f : α → β₁} {g : α → β₂} (hf : ComputableInDegree f encIn enc₁ d₁ e₁)
    (hg : ComputableInDegree g encIn enc₂ d₂ e₂) :
    ComputableInDegree (fun x => (f x, g x)) encIn (encPair enc₁ enc₂) (max d₁ d₂)
      (max e₁ e₂) :=
  ⟨(hf.pair hg).1, (((hf.2.smul 2).add_const 1).add_max hg.2).mono fun x => by simp⟩

end Turing.MultiTapeTM.ComputableInDegree
