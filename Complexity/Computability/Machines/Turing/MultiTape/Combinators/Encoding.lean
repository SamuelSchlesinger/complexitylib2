/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Append
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Ite
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
import all Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Linear time and space, and encodings of pairs, options and lists

Tidy computability (`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace`) is relative to encodings of
values as words. Tidy computability in linear time and space is closed under composition, case
distinctions, concatenation of encoded values and pairing, and contains constant functions and the
functions computed by finite-state transducers.

This file also states, as classes indexed by the encodings, what is required of encodings of
pairs, options and lists: their basic operations are plainly computable in linear time and space,
and pairing, which builds a value from a common input, preserves independent time and work-space
bounds up to a constant, with explicit space for the encoded pair. Theorems take
these classes as instance arguments, so they hold for every encoding with the required
capabilities.

## Main definitions

* `Turing.MultiTapeTM.encBool`: the encoding `b ↦ [b]` of `Bool`. Case distinctions
  (`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.ite`) accept any encoding of `Bool`, so the
  choice matters only up to a constant.
* `Turing.MultiTapeTM.ComputableTidilyInLinearTimeAndSpace`: tidy computability in linear time and
  space, up to a constant.
* `Turing.MultiTapeTM.PairEncoding enc₁ enc₂ enc`: `enc` encodes pairs compatibly with `enc₁` and
  `enc₂`.
* `Turing.MultiTapeTM.OptionEncoding enc₁ enc`: `enc` encodes options compatibly with `enc₁`, with
  `none` encoded by the empty word.
* `Turing.MultiTapeTM.ListEncoding enc₁ enc`: `enc` encodes lists compatibly with `enc₁`.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.of_enc_eq`: reuse identical encoded outputs
  with the same machine and exact time and space bounds.

* `Turing.MultiTapeTM.ComputableTidilyInLinearTimeAndSpace.comp`, `.ite`, `.append`, `.pair`:
  closure properties of linear time and space.
* `Turing.MultiTapeTM.ComputableTidilyInLinearTimeAndSpace.const`: constant functions.
* `Turing.MultiTapeTM.Transducer.computableTidilyInLinearTimeAndSpace`: functions computed by
  finite-state transducers.
* `Turing.MultiTapeTM.PairEncoding.pair_mono`: pairing functions computable within different
  bounds.
-/

namespace Turing.MultiTapeTM

universe u

/-- The encoding `b ↦ [b]` of `Bool`. -/
@[expose] public def encBool : Bool ↪ List Bool :=
  ⟨fun b => [b], fun _ _ h => List.head_eq_of_cons_eq h⟩

@[simp]
public lemma encBool_apply (b : Bool) : encBool b = [b] := rfl

/-- `f` is tidily computable within a constant factor of the length of the encoded input plus one,
in time and in space. -/
@[expose] public def ComputableTidilyInLinearTimeAndSpace {α β : Type*} (f : α → β)
    (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) : Prop :=
  ∃ c, ComputableTidilyInTimeAndSpace f encIn encOut (fun a => c * ((encIn a).length + 1))
    (fun a => c * ((encIn a).length + 1))

-- upstream: candidate
-- vendored: local output-word transport rule; not part of the copied revision.
/-- Reuse the same machine when the new function emits the same encoded output word.
The time and space bounds are unchanged; no encoding conversion is performed. -/
public theorem ComputableTidilyInTimeAndSpace.of_enc_eq
    {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
    {encOut : γ ↪ List Bool} {f : α → β} {g : α → γ} {t s : α → ℕ}
    (hf : ComputableTidilyInTimeAndSpace f encIn encMid t s)
    (h : ∀ a, encOut (g a) = encMid (f a)) :
    ComputableTidilyInTimeAndSpace g encIn encOut t s :=
  let ⟨k, State, hfinite, tm, htm⟩ := hf
  ⟨k, State, hfinite, tm, fun a => h a ▸ htm a⟩

-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

/-! ### Closure properties of linear time and space -/

namespace ComputableTidilyInLinearTimeAndSpace

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- Compositions of functions tidily computable in linear time and space. -/
public theorem comp {f : β → γ} {g : α → β}
    (hf : ComputableTidilyInLinearTimeAndSpace f encMid encOut)
    (hg : ComputableTidilyInLinearTimeAndSpace g encIn encMid) :
    ComputableTidilyInLinearTimeAndSpace (f ∘ g) encIn encOut := by
  obtain ⟨c₁, h₁⟩ := hg
  obtain ⟨c₂, h₂⟩ := hf
  -- vendored: crei's `comp` is `comp_linear` here, as cslib #1111 restates `comp`
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.comp_linear h₂ h₁
  refine ⟨c₁ + (c₂ + c) * (c₁ + 1), h.mono (fun a => ?_) (fun a => ?_)⟩ <;>
  nlinarith [h₁.length_le a]

/-- A function tidily computable in linear time and space on all inputs is so on the inputs
satisfying `p`. -/
public theorem restrict {f : α → β} (h : ComputableTidilyInLinearTimeAndSpace f encIn encMid)
    (p : α → Prop) :
    ComputableTidilyInLinearTimeAndSpace (f ∘ Subtype.val)
      ((Function.Embedding.subtype p).trans encIn) encMid :=
  let ⟨c, hc⟩ := h
  ⟨c, hc.restrict p⟩

/-- Case distinctions of functions tidily computable in linear time and space, each branch on the
inputs where it is taken. -/
public theorem ite {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    (hc : ComputableTidilyInLinearTimeAndSpace c encIn encC)
    (hf : ComputableTidilyInLinearTimeAndSpace (f ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = true)).trans encIn) encMid)
    (hg : ComputableTidilyInLinearTimeAndSpace (g ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = false)).trans encIn) encMid) :
    ComputableTidilyInLinearTimeAndSpace (fun x => if c x then f x else g x) encIn encMid := by
  obtain ⟨c₀, h₀⟩ := hc
  obtain ⟨c₁, h₁⟩ := hf
  obtain ⟨c₂, h₂⟩ := hg
  obtain ⟨k, h⟩ := ComputableTidilyInTimeAndSpace.ite h₀
    (tf := fun x => c₁ * ((encIn x).length + 1)) (sf := fun x => c₁ * ((encIn x).length + 1))
    (tg := fun x => c₂ * ((encIn x).length + 1)) (sg := fun x => c₂ * ((encIn x).length + 1))
    h₁ h₂
  refine ⟨c₀ + c₁ + c₂ + k, h.mono (fun x => ?_) (fun x => ?_)⟩ <;> split_ifs <;> nlinarith

/-- Constant functions are tidily computable in linear time and space. -/
public theorem const (b : β) :
    ComputableTidilyInLinearTimeAndSpace (fun _ : α => b) encIn encMid := by
  obtain ⟨c, h⟩ := computableInTimeAndSpace_of_const (encIn := encIn) (encOut := encMid) b
  exact ⟨2 * c + 2, h.computableTidilyInTimeAndSpace.mono
    (fun _ => Nat.le_mul_of_pos_right _ (Nat.succ_pos _)) (fun _ => Nat.zero_le _)⟩

/-- Functions whose encoded value is the encoded input. -/
public theorem of_eq {f : α → β} (h : ∀ a, encMid (f a) = encIn a) :
    ComputableTidilyInLinearTimeAndSpace f encIn encMid :=
  ⟨4, 0, _, inferInstance, tidyCopy Bool, fun a => by
    rw [h]
    exact (computesTidily_tidyCopy _).mono (by beta_reduce; omega) (Nat.zero_le _)⟩

/-- A function whose encoded value is the concatenation of the encoded values of two functions
tidily computable in linear time and space. -/
public theorem append {δ : Type*} {enc₂ : δ ↪ List Bool} {f₁ : α → β} {f₂ : α → δ} {g : α → γ}
    (h₁ : ComputableTidilyInLinearTimeAndSpace f₁ encIn encMid)
    (h₂ : ComputableTidilyInLinearTimeAndSpace f₂ encIn enc₂)
    (hg : ∀ x, encOut (g x) = encMid (f₁ x) ++ enc₂ (f₂ x)) :
    ComputableTidilyInLinearTimeAndSpace g encIn encOut := by
  obtain ⟨c₁, h₁⟩ := h₁
  obtain ⟨c₂, h₂⟩ := h₂
  obtain ⟨k, h⟩ := h₁.append h₂ hg
  refine ⟨c₁ + c₂ + k, h.mono (fun x => ?_) (fun x => ?_)⟩ <;> nlinarith

end ComputableTidilyInLinearTimeAndSpace

/-- A function computed by a transducer with finitely many states is tidily computable in linear
time and space. -/
public theorem Transducer.computableTidilyInLinearTimeAndSpace {Q : Type} [Finite Q]
    (τ : Transducer Bool Q) {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} (hf : ∀ a, encOut (f a) = τ.run τ.q₀ (encIn a)) :
    ComputableTidilyInLinearTimeAndSpace f encIn encOut :=
  ⟨8, (τ.computableTidilyInTimeAndSpace hf).mono (fun _ => by omega) (fun _ => Nat.zero_le _)⟩

/-! ### Encodings of pairs, options and lists -/

section Classes

variable {α β : Type u}

/-- `enc` encodes pairs compatibly with `enc₁` and `enc₂`. -/
public class PairEncoding (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool)
    (enc : α × β ↪ List Bool) : Prop where
  /-- Pairing is a combinator: functions `f` and `g` computable from a common input within
  common bounds combine into `fun x => (f x, g x)`, within a constant factor of those bounds, plus
  space for the encoded pair. Different bounds are covered by
  `Turing.MultiTapeTM.PairEncoding.pair_mono`. -/
  pair {γ : Type u} {encIn : γ ↪ List Bool} {f : γ → α} {g : γ → β} {t s : γ → ℕ} :
    ComputableInTimeAndSpace f encIn enc₁ t s →
    ComputableInTimeAndSpace g encIn enc₂ t s →
    ∃ c, ComputableInTimeAndSpace (fun x => (f x, g x)) encIn enc
      (fun x => c * (t x + 1)) (fun x => c * (s x + (enc (f x, g x)).length + 1))
  /-- The first projection is computable in linear time and space. -/
  fst : ComputableInLinearTimeAndSpace Prod.fst enc enc₁
  /-- The second projection is computable in linear time and space. -/
  snd : ComputableInLinearTimeAndSpace Prod.snd enc enc₂

/-- `enc` encodes options compatibly with `enc₁`: `none` is encoded by the empty word. -/
public class OptionEncoding (enc₁ : α ↪ List Bool) (enc : Option α ↪ List Bool) : Prop where
  /-- `none` is encoded by the empty word. -/
  none_eq : enc none = []
  /-- `some` is computable in linear time and space. -/
  some : ComputableInLinearTimeAndSpace some enc₁ enc
  /-- `Option.getD` is computable in linear time and space. -/
  getD (d : α) : ComputableInLinearTimeAndSpace (fun o => o.getD d) enc enc₁

/-- `enc` encodes lists compatibly with `enc₁`. -/
public class ListEncoding (enc₁ : α ↪ List Bool) (enc : List α ↪ List Bool) : Prop where
  /-- `List.headD` is computable in linear time and space. -/
  headD (d : α) : ComputableInLinearTimeAndSpace (fun l => l.headD d) enc enc₁
  /-- `List.tail` is computable in linear time and space. -/
  tail : ComputableInLinearTimeAndSpace List.tail enc enc
  /-- Testing a list for emptiness is computable in linear time and space. -/
  isEmpty : ComputableInLinearTimeAndSpace List.isEmpty enc encBool

/-- Pairing functions computable within different bounds. -/
public theorem PairEncoding.pair_mono {enc₁ : α ↪ List Bool} {enc₂ : β ↪ List Bool}
    {enc : α × β ↪ List Bool} [h : PairEncoding enc₁ enc₂ enc] {γ : Type u}
    {encIn : γ ↪ List Bool} {f : γ → α} {g : γ → β} {t₁ s₁ t₂ s₂ : γ → ℕ}
    (hf : ComputableInTimeAndSpace f encIn enc₁ t₁ s₁)
    (hg : ComputableInTimeAndSpace g encIn enc₂ t₂ s₂) :
    ∃ c, ComputableInTimeAndSpace (fun x => (f x, g x)) encIn enc
      (fun x => c * (t₁ x + t₂ x + 1))
      (fun x => c * (s₁ x + s₂ x + (enc (f x, g x)).length + 1)) :=
  h.pair (hf.mono (fun _ => Nat.le_add_right _ _) (fun _ => Nat.le_add_right _ _))
    (hg.mono (fun _ => Nat.le_add_left _ _) (fun _ => Nat.le_add_left _ _))

end Classes

/-- Pairing functions tidily computable in linear time and space. -/
public theorem ComputableTidilyInLinearTimeAndSpace.pair {α β₁ β₂ : Type u}
    {encIn : α ↪ List Bool} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {enc : β₁ × β₂ ↪ List Bool} [hP : PairEncoding enc₁ enc₂ enc] {f : α → β₁} {g : α → β₂}
    (hf : ComputableTidilyInLinearTimeAndSpace f encIn enc₁)
    (hg : ComputableTidilyInLinearTimeAndSpace g encIn enc₂) :
    ComputableTidilyInLinearTimeAndSpace (fun x => (f x, g x)) encIn enc := by
  obtain ⟨c₁, h₁⟩ := hf
  obtain ⟨c₂, h₂⟩ := hg
  obtain ⟨c, h⟩ := hP.pair
    (h₁.computableInTimeAndSpace.mono
      (t' := fun x => (c₁ + c₂) * ((encIn x).length + 1))
      (s' := fun x => (c₁ + c₂) * ((encIn x).length + 1))
      (fun x => by ring_nf; omega) (fun x => by ring_nf; omega))
    (h₂.computableInTimeAndSpace.mono
      (fun x => by ring_nf; omega) (fun x => by ring_nf; omega))
  obtain ⟨c, h⟩ := Internal.normalizeBigO ⟨c, h⟩
  refine ⟨c * (c + 2) * (c₁ + c₂ + 1), h.mono (fun x => ?_) (fun x => ?_)⟩
  · ring_nf
    omega
  · have := Nat.mul_le_mul_left c (h.length_le x)
    ring_nf at this ⊢
    omega

end Turing.MultiTapeTM
