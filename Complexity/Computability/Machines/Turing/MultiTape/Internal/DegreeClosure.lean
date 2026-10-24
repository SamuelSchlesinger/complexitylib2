/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.NormalForm
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Append

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

end Turing.MultiTapeTM.ComputableInDegree
