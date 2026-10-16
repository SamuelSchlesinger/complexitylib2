/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Mathlib.Basic.Finite.Sum
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Basic

/-!
# Concatenating the outputs of tidy computations

A tidy machine leaves its tapes as it found them, so a second tidy machine can run after it on the
same input. `appendTM tm₁ tm₂` runs `tm₁` and then `tm₂`; the outputs concatenate.

## Main definitions

* `Turing.MultiTapeTM.appendTM`: the machine that runs two machines one after the other.

## Main results

* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.append`: the outputs of two tidy computations
  on the same input concatenate.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.append`: a function whose encoded value is the
  concatenation of the encoded values of two tidily computable functions is tidily computable.
-/

namespace Turing.MultiTapeTM

variable {k₁ k₂ : ℕ} {Symbol S₁ S₂ : Type*}

/-- Run `tm₁` and then `tm₂`, both with their work tapes padded to `max k₁ k₂`. -/
public noncomputable def appendTM (tm₁ : MultiTapeTM k₁ Symbol S₁)
    (tm₂ : MultiTapeTM k₂ Symbol S₂) : MultiTapeTM (max k₁ k₂) Symbol (S₁ ⊕ S₂) :=
  (tm₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).seq
    (tm₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂)))

/-- If `tm₁` computes `y₁` from `x` tidily and `tm₂` computes `y₂` from `x` tidily, then
`appendTM tm₁ tm₂` computes `y₁ ++ y₂` from `x` tidily. -/
public theorem ComputesTidilyInTimeAndSpace.append {tm₁ : MultiTapeTM k₁ Symbol S₁}
    {tm₂ : MultiTapeTM k₂ Symbol S₂} {x y₁ y₂ : List Symbol} {t₁ s₁ t₂ s₂ : ℕ}
    (h₁ : tm₁.ComputesTidilyInTimeAndSpace x y₁ t₁ s₁)
    (h₂ : tm₂.ComputesTidilyInTimeAndSpace x y₂ t₂ s₂) :
    (appendTM tm₁ tm₂).ComputesTidilyInTimeAndSpace x (y₁ ++ y₂) (t₁ + t₂)
      (s₁ + s₂ + 2 * max k₁ k₂) :=
  (transformsTapes_seq (h₁.extendTapes _) (h₂.extendTapes _)
    fun _ _ _ _ hP hQ => ⟨hP.1, hQ.1⟩).imp (fun _ _ h => h)
    (by rintro _ _ _ _ _ ⟨_, _, _, ⟨-, rfl⟩, ⟨hws, rfl⟩, rfl⟩; exact ⟨hws, rfl⟩) le_rfl
    (by omega)

/-- If `f₁` and `f₂` are tidily computable and the encoded value of `g` is the concatenation of
their encoded values, then `g` is tidily computable within the sum of their bounds, plus a constant
for the space. -/
public theorem ComputableTidilyInTimeAndSpace.append {γ α₁ α₂ β : Type*} {encIn : γ ↪ List Bool}
    {enc₁ : α₁ ↪ List Bool} {enc₂ : α₂ ↪ List Bool} {encOut : β ↪ List Bool} {f₁ : γ → α₁}
    {f₂ : γ → α₂} {g : γ → β} {t₁ s₁ t₂ s₂ : γ → ℕ}
    (h₁ : ComputableTidilyInTimeAndSpace f₁ encIn enc₁ t₁ s₁)
    (h₂ : ComputableTidilyInTimeAndSpace f₂ encIn enc₂ t₂ s₂)
    (hg : ∀ x, encOut (g x) = enc₁ (f₁ x) ++ enc₂ (f₂ x)) :
    ∃ k, ComputableTidilyInTimeAndSpace g encIn encOut (fun x => t₁ x + t₂ x)
      (fun x => s₁ x + s₂ x + k) := by
  obtain ⟨k₁, S₁, _, tm₁, htm₁⟩ := h₁
  obtain ⟨k₂, S₂, _, tm₂, htm₂⟩ := h₂
  exact ⟨2 * max k₁ k₂, _, _, inferInstance, appendTM tm₁ tm₂,
    fun x => hg x ▸ (htm₁ x).append (htm₂ x)⟩

end Turing.MultiTapeTM
