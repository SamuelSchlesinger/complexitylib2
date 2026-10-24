/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (spike for #862, not for merge)

public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Comp
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm

/-!
# Plain bounds of given degrees without a tidy calculus (spike)

The composition of `Turing.MultiTapeTM.ComputableInDegree`, proved directly from plain hypotheses,
with the degrees of the tidy rule `ComputableTidilyInDegree.comp`: time and workspace of degree
`max d₁ (e₁ d₂)` and output of degree `e₁ e₂`. The tidy normal form keeps degrees: time
`2 t + 3 s + O(1)` and space `O(s + 1)` have the degree `d` of `t` and `s`.

The tidy degree calculus is the backbone of the tidy polynomial-time library (lists, options,
integers and natural numbers are certified through it), so a plain degree calculus with direct
rules is what the polynomial-time library would be rebuilt on.

## Main results

* `Turing.MultiTapeTM.PlainDirect.ComputableInDegree.comp`: composition.
-/

@[expose] public section

namespace Turing.MultiTapeTM.PlainDirect.ComputableInDegree

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- A plain certificate of degree `d` gives a tidy machine within time and space of degree `d`. -/
private theorem exists_computesTidily {f : α → β} {d e : ℕ}
    (h : ComputableInDegree f encIn encMid d e) :
    ∃ t s : α → ℕ, DegreeBounded (fun a => (encIn a).length) t d ∧
      DegreeBounded (fun a => (encIn a).length) s d ∧
      ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
        ∀ a, tm.ComputesTidilyInTimeAndSpace (encIn a) (encMid (f a)) (t a) (s a) := by
  obtain ⟨⟨t, s, ht, hs, k, State, hfin, tm, htm⟩, -⟩ := h
  exact ⟨fun a => 2 * t a + 3 * s a + 2 * k + 4,
    fun a => 2 * s a + 2 * k * (3 * s a + 2 * k + 3),
    (((ht.smul 2).add (hs.smul 3)).add_const _).add_const _,
    (hs.smul 2).add (((hs.smul 3).add_const _).add_const _ |>.smul _),
    k + k, _, inferInstance, tidy false true tm,
    fun a => (htm a).computesTidily_tidy Bool.false_ne_true⟩

/-- **Composition**, through the machine-level composition of tidy machines. The intermediate word
is no longer than the time of the inner machine. -/
theorem comp {f : β → γ} {g : α → β} {d₁ e₁ d₂ e₂ : ℕ}
    (hf : ComputableInDegree f encMid encOut d₂ e₂)
    (hg : ComputableInDegree g encIn encMid d₁ e₁) :
    ComputableInDegree (fun a => f (g a)) encIn encOut (max d₁ (e₁ * d₂)) (e₁ * e₂) := by
  have hl₁ := hg.2
  have hl₂ := hf.2
  obtain ⟨t₁, s₁, ht₁, hs₁, k₁, Q₁, _, tm₁, h₁⟩ := exists_computesTidily hg
  obtain ⟨t₂, s₂, ht₂, hs₂, k₂, Q₂, _, tm₂, h₂⟩ := exists_computesTidily hf
  have hm : DegreeBounded (fun a => (encIn a).length) (fun a => (encMid (g a)).length) d₁ :=
    ht₁.mono fun a => (h₁ a).length_output_le
  have hd₁ : d₁ ≤ max d₁ (e₁ * d₂) := le_max_left _ _
  exact ⟨⟨_, _, ((ht₁.add_max (ht₂.comp hl₁)).add ((hm.smul 4).mono_deg hd₁)).add_const 9,
    ((hs₁.add_max (hs₂.comp hl₁)).add ((hm.smul 5).mono_deg hd₁)).add_const _,
    _, _, inferInstance, tm₂.comp tm₁ true,
    fun a => ((h₁ a).comp (h₂ (g a)) true).computesInTimeAndSpace⟩, hl₂.comp hl₁⟩

end Turing.MultiTapeTM.PlainDirect.ComputableInDegree
