/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Parameterized

/-!
# Plain fixed-parameter tractability rules

These ordinary declarations preserve the encodings, captured parameters and quantitative premises
of the construction certificates used in their proofs. Public clients use the plain statements.

The existing construction exports and registrations are retired during the coordinated #456
client migration; this source package does not add an internal-layer exemption.
-/

public section

open _root_.Turing.MultiTapeTM

open Cslib.Complexity

namespace Cslib.Complexity.ComputableInFPTTime

/-- **Composition in fpt time**, along a function that bounds the parameter. -/
theorem comp
    {α β γ : Type}
    {encA : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool}
    {κA : α → ℕ}
    {κB : β → ℕ}
    {f : α → β}
    {g : β → γ}
    (hg : ComputableInFPTTime g encB encC κB)
    (hf : ComputableInFPTTime f encA encB κA)
    {h : ℕ → ℕ}
    (hκ : ∀ (a : α), κB (f a) ≤ h (κA a)) :
    ComputableInFPTTime (g ∘ f) encA encC κA := by
  simp only [computableInFPTTime_iff_computableTidilyInFPTTime] at *
  exact @ComputableTidilyInFPTTime.comp α β γ encA encB encC κA κB f g hg hf h hκ

/-- **Case distinction in fpt time.** -/
theorem ite
    {α β : Type}
    {encA : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {κ : α → ℕ}
    {p : α → Bool}
    {f g : α → β}
    (hp : ComputableInFPTTime p encA encBool κ)
    (hf : ComputableInFPTTime f encA encB κ)
    (hg : ComputableInFPTTime g encA encB κ) :
    ComputableInFPTTime
      (fun (a : α) => if p a = Bool.true then f a else g a) encA encB κ := by
  simp only [computableInFPTTime_iff_computableTidilyInFPTTime] at *
  exact @ComputableTidilyInFPTTime.ite α β encA encB κ p f g hp hf hg

end Cslib.Complexity.ComputableInFPTTime

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- A function computable in polynomial time is computable in fpt time, for every parameter. -/
theorem computableInFPTTime
    {α β : Type}
    {encA : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {f : α → β}
    (hf : ComputableInPolyTime f encA encB)
    (κ : α → ℕ) :
    ComputableInFPTTime f encA encB κ := by
  simp only [
    computableInPolyTime_iff_computableTidilyInPolyTime,
    computableInFPTTime_iff_computableTidilyInFPTTime] at *
  exact @ComputableTidilyInPolyTime.computableTidilyInFPTTime α β encA encB f hf κ

end Turing.MultiTapeTM.ComputableInPolyTime
