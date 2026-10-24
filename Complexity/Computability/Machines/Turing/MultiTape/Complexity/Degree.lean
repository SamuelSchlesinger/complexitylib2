/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: move pure degree bounds to ResourceBounds.Degree and add direct plain certificates.

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Degree
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.Ring

import all Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm

/-!
# Tidy computability with polynomial bounds of a given degree

`ComputableTidilyInDegree f encIn encOut d e`: `f` is tidily computable within time and space
`O(n ^ d)`, and its encoded values have length `O(n ^ e)`, where `n` is the length of the encoded
input. The constants are existential, the degrees are explicit. The closure properties compute the
degrees: composition multiplies the degree of the outer function by the output degree of the inner
one, pairing and case distinctions take maxima, and a left fold adds the output degree of the list
to the degree of a round.

Results are stated with the degrees the closure properties produce; `mono` moves to larger degrees,
proving the inequalities by `decide` or `omega`. Left folds are in
`Cslib.Computability.Machines.Turing.MultiTape.Complexity.Fold`.
For sums, `DegreeBounded.add_max` combines different degrees directly; `DegreeBounded.add` keeps
an already shared degree.

## Main definitions

* `Turing.MultiTapeTM.DegreeBounded`: a function bounded by `c * (size + 1) ^ d`.
* `Turing.MultiTapeTM.ComputableTidilyInDegree`: tidy computability with bounds of given degrees.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInDegree.computableTidilyInPolyTime`: polynomial time.
* `Turing.MultiTapeTM.ComputableTidilyInDegree.comp`, `.ite`, `.append`, `.pair`, `.prod`: closure
  properties.
* `Turing.MultiTapeTM.ComputableTidilyInDegree.of_finite`: functions on finite types.
-/

namespace Turing.MultiTapeTM

universe u

namespace DegreeBounded

variable {α β : Type*} {size : α → ℕ} {u v : α → ℕ} {d d₁ d₂ : ℕ}

public theorem polyBounded (h : DegreeBounded size u d) : PolyBounded size u :=
  let ⟨c, hu⟩ := h
  .of_forall_le c d hu

end DegreeBounded

/-! ### Tidy computability with bounds of given degrees -/

/-- `f` is tidily computable within time and space bounded by polynomials of degree `d` in the
length of the encoded input, and its encoded values have length bounded by a polynomial of
degree `e`. -/
@[expose] public def ComputableTidilyInDegree {α β : Type*} (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) (d e : ℕ) : Prop :=
  (∃ t s, DegreeBounded (fun a => (encIn a).length) t d ∧
    DegreeBounded (fun a => (encIn a).length) s d ∧
    ComputableTidilyInTimeAndSpace f encIn encOut t s) ∧
  DegreeBounded (fun a => (encIn a).length) (fun a => (encOut (f a)).length) e

namespace ComputableTidilyInDegree

variable {α β γ δ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool} {d e d₁ e₁ d₂ e₂ : ℕ}

/-- Moving to larger degrees. -/
public theorem mono {f : α → β} {d' e' : ℕ} (h : ComputableTidilyInDegree f encIn encMid d e)
    (hd : d ≤ d' := by first | decide | omega) (he : e ≤ e' := by first | decide | omega) :
    ComputableTidilyInDegree f encIn encMid d' e' :=
  let ⟨⟨t, s, ht, hs, hf⟩, hl⟩ := h
  ⟨⟨t, s, ht.mono_deg hd, hs.mono_deg hd, hf⟩, hl.mono_deg he⟩

/-- Bounds of degree `d` give tidy computability of degree `d`, with output of degree `d`. -/
public theorem of_bounds {f : α → β} {t s : α → ℕ}
    (ht : DegreeBounded (fun a => (encIn a).length) t d)
    (hs : DegreeBounded (fun a => (encIn a).length) s d)
    (hf : ComputableTidilyInTimeAndSpace f encIn encMid t s) :
    ComputableTidilyInDegree f encIn encMid d d :=
  ⟨⟨t, s, ht, hs, hf⟩, ht.mono hf.length_le⟩

public theorem computableTidilyInPolyTime {f : α → β}
    (h : ComputableTidilyInDegree f encIn encMid d e) : ComputableTidilyInPolyTime f encIn encMid :=
  let ⟨⟨_, _, ht, hs, hf⟩, _⟩ := h
  ⟨_, _, ht.polyBounded, hs.polyBounded, hf⟩

public theorem of_linear {f : α → β} (h : ComputableInLinearTimeAndSpace f encIn encMid) :
    ComputableTidilyInDegree f encIn encMid 1 1 :=
  let ⟨c, hc⟩ := Internal.normalizeLinear h
  of_bounds ⟨c, fun _ => by simp⟩ ⟨c, fun _ => by simp⟩ hc

public theorem comp {f : β → γ} {g : α → β} (hf : ComputableTidilyInDegree f encMid encOut d₂ e₂)
    (hg : ComputableTidilyInDegree g encIn encMid d₁ e₁) :
    ComputableTidilyInDegree (f ∘ g) encIn encOut (max d₁ (e₁ * d₂)) (e₁ * e₂) := by
  obtain ⟨⟨t₁, s₁, ht₁, hs₁, h₁⟩, hl₁⟩ := hg
  obtain ⟨⟨t₂, s₂, ht₂, hs₂, h₂⟩, hl₂⟩ := hf
  -- vendored: crei's `comp` is `comp_linear` here, as cslib #1111 restates `comp`
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.comp_linear h₂ h₁
  -- the length of the intermediate value is bounded by the time of `g`
  have hm := (ht₁.add_const 1).smul c |>.mono fun a =>
    Nat.mul_le_mul_left c (Nat.add_le_add_right (h₁.length_le a) 1)
  have hd₁ : d₁ ≤ max d₁ (e₁ * d₂) := le_max_left _ _
  exact ⟨⟨_, _, (ht₁.add_max (ht₂.comp hl₁)).add (hm.mono_deg hd₁),
    (hs₁.add_max (hs₂.comp hl₁)).add (hm.mono_deg hd₁), h⟩,
    hl₂.comp hl₁⟩

public theorem restrict {f : α → β} (h : ComputableTidilyInDegree f encIn encMid d e)
    (p : α → Prop) :
    ComputableTidilyInDegree (f ∘ Subtype.val) ((Function.Embedding.subtype p).trans encIn) encMid
      d e :=
  let ⟨⟨_, _, ⟨ct, ht⟩, ⟨cs, hs⟩, hf⟩, ⟨cl, hl⟩⟩ := h
  ⟨⟨_, _, ⟨ct, fun a => ht a⟩, ⟨cs, fun a => hs a⟩, hf.restrict p⟩, ⟨cl, fun a => hl a⟩⟩

public theorem ite {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β} {dc ec : ℕ}
    (hc : ComputableTidilyInDegree c encIn encC dc ec)
    (hf : ComputableTidilyInDegree (f ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = true)).trans encIn) encMid d₁ e₁)
    (hg : ComputableTidilyInDegree (g ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = false)).trans encIn) encMid d₂ e₂) :
    ComputableTidilyInDegree (fun x => if c x then f x else g x) encIn encMid
      (max dc (max d₁ d₂)) (max e₁ e₂) := by
  obtain ⟨⟨tc, sc, htc, hsc, h₀⟩, -⟩ := hc
  obtain ⟨⟨tf, sf, ⟨ctf, htf⟩, ⟨csf, hsf⟩, h₁⟩, ⟨clf, hlf⟩⟩ := hf
  obtain ⟨⟨tg, sg, ⟨ctg, htg⟩, ⟨csg, hsg⟩, h₂⟩, ⟨clg, hlg⟩⟩ := hg
  -- the bounds of the branches, extended to all inputs
  let ext (u : {x // c x = true} → ℕ) (v : {x // c x = false} → ℕ) (x : α) : ℕ :=
    if h : c x = true then u ⟨x, h⟩ else v ⟨x, by simpa using h⟩
  obtain ⟨k, h⟩ := ComputableTidilyInTimeAndSpace.ite h₀ (tf := ext tf tg) (sf := ext sf sg)
    (tg := ext tf tg) (sg := ext sf sg)
    (h₁.mono (fun x => by simp [ext, x.2]) (fun x => by simp [ext, x.2]))
    (h₂.mono (fun x => by simp [ext, x.2]) (fun x => by simp [ext, x.2]))
  have hext {u v} {cu du cv dv : ℕ}
      (hu : ∀ x : {x // c x = true}, u x ≤ cu * ((encIn x).length + 1) ^ du)
      (hv : ∀ x : {x // c x = false}, v x ≤ cv * ((encIn x).length + 1) ^ dv) :
      DegreeBounded (fun a => (encIn a).length) (ext u v) (max du dv) :=
    ((DegreeBounded.mono_deg ⟨cu, fun _ => le_rfl⟩ (le_max_left du dv)).add
      (DegreeBounded.mono_deg ⟨cv, fun _ => le_rfl⟩ (le_max_right du dv))).mono fun x => by
      by_cases hx : c x = true
      · simpa [ext, hx] using Nat.le_add_right_of_le (hu ⟨x, hx⟩)
      · simpa [ext, hx] using Nat.le_add_left_of_le (hv ⟨x, by simpa using hx⟩)
  have hd : max d₁ d₂ ≤ max dc (max d₁ d₂) := le_max_right _ _
  refine ⟨⟨_, _, ((htc.mono_deg (le_max_left _ _)).add ((hext htf htg).mono_deg hd)).add_const k,
    ((hsc.mono_deg (le_max_left _ _)).add ((hext hsf hsg).mono_deg hd)).add_const k,
    h.mono (fun x => ?_) (fun x => ?_)⟩, (hext hlf hlg).mono fun x => ?_⟩ <;>
  · by_cases hx : c x = true <;> simp [ext, hx]

public theorem const (b : β) : ComputableTidilyInDegree (fun _ : α => b) encIn encMid 1 0 :=
  ⟨(of_linear (.const b)).1, .const _⟩

public theorem of_eq {f : α → β} (h : ∀ a, encMid (f a) = encIn a) :
    ComputableTidilyInDegree f encIn encMid 1 1 :=
  of_linear (.of_eq h)

public theorem append {enc₂ : δ ↪ List Bool} {f₁ : α → β} {f₂ : α → δ} {g : α → γ}
    (h₁ : ComputableTidilyInDegree f₁ encIn encMid d₁ e₁)
    (h₂ : ComputableTidilyInDegree f₂ encIn enc₂ d₂ e₂)
    (hg : ∀ x, encOut (g x) = encMid (f₁ x) ++ enc₂ (f₂ x)) :
    ComputableTidilyInDegree g encIn encOut (max d₁ d₂) (max e₁ e₂) := by
  obtain ⟨⟨t₁, s₁, ht₁, hs₁, h₁⟩, hl₁⟩ := h₁
  obtain ⟨⟨t₂, s₂, ht₂, hs₂, h₂⟩, hl₂⟩ := h₂
  obtain ⟨k, h⟩ := h₁.append h₂ hg
  exact ⟨⟨_, _, ht₁.add_max ht₂, (hs₁.add_max hs₂).add_const k, h⟩,
    (hl₁.add_max hl₂).mono fun x => by
      simp [hg]⟩

/-- A function whose encoded values are those of a function computable with given degrees. -/
public theorem of_enc_eq {f : α → β} {g : α → γ}
    (hf : ComputableTidilyInDegree f encIn encMid d e) (h : ∀ x, encOut (g x) = encMid (f x)) :
    ComputableTidilyInDegree g encIn encOut d e :=
  -- vendored: reuse the exact-bound output transport rule.
  let ⟨⟨t, s, ht, hs, hf⟩, hl⟩ := hf
  ⟨⟨t, s, ht, hs, hf.of_enc_eq h⟩, hl.mono fun a => by rw [h]⟩

public theorem pair {α β₁ β₂ : Type u} {encIn : α ↪ List Bool}
    {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {enc : β₁ × β₂ ↪ List Bool} [hP : PairEncoding enc₁ enc₂ enc] {f : α → β₁} {g : α → β₂}
    (hf : ComputableTidilyInDegree f encIn enc₁ d₁ e₁)
    (hg : ComputableTidilyInDegree g encIn enc₂ d₂ e₂) :
    ComputableTidilyInDegree (fun x => (f x, g x)) encIn enc (max d₁ d₂) (max d₁ d₂) := by
  obtain ⟨⟨t₁, s₁, ht₁, hs₁, h₁⟩, -⟩ := hf
  obtain ⟨⟨t₂, s₂, ht₂, hs₂, h₂⟩, -⟩ := hg
  obtain ⟨c, h⟩ := hP.pair_mono h₁.computableInTimeAndSpace h₂.computableInTimeAndSpace
  obtain ⟨c, h⟩ := Internal.normalizeBigO ⟨c, h⟩
  have ht := ((ht₁.add_max ht₂).add_const 1).smul c
  refine of_bounds ht ((((hs₁.add_max hs₂).add ht).add_const 1).smul c)
    (h.mono (fun _ => le_rfl) (fun x => Nat.mul_le_mul_left c ?_))
  have := h.length_le x
  omega

/-- Pairing with the framed encoding of pairs. -/
public theorem prod {α β₁ β₂ : Type u} {encIn : α ↪ List Bool}
    {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {f : α → β₁} {g : α → β₂} (hf : ComputableTidilyInDegree f encIn enc₁ d₁ e₁)
    (hg : ComputableTidilyInDegree g encIn enc₂ d₂ e₂) :
    ComputableTidilyInDegree (fun x => (f x, g x)) encIn (encPair enc₁ enc₂) (max d₁ d₂)
      (max e₁ e₂) :=
  ⟨(hf.pair hg).1, (((hf.2.smul 2).add_const 1).add_max hg.2).mono fun x => by simp⟩

/-- The first projection of the framed encoding of pairs. -/
public theorem fst {β₁ β₂ : Type u} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableTidilyInDegree Prod.fst (encPair enc₁ enc₂) enc₁ 1 1 :=
  of_linear (.of_unframe fun p => by simp)

/-- The second projection of the framed encoding of pairs. -/
public theorem snd {β₁ β₂ : Type u} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableTidilyInDegree Prod.snd (encPair enc₁ enc₂) enc₂ 1 1 :=
  of_linear (.of_dropFrame fun p => by simp)

/-- The first component of a pair computed with given degrees. -/
public theorem fst' {α β₁ β₂ : Type u} {encIn : α ↪ List Bool}
    {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {f : α → β₁ × β₂} (h : ComputableTidilyInDegree f encIn (encPair enc₁ enc₂) d e) :
    ComputableTidilyInDegree (fun x => (f x).1) encIn enc₁ (max d e) e :=
  ((fst enc₁ enc₂).comp h).mono

/-- The second component of a pair computed with given degrees. -/
public theorem snd' {α β₁ β₂ : Type u} {encIn : α ↪ List Bool}
    {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {f : α → β₁ × β₂} (h : ComputableTidilyInDegree f encIn (encPair enc₁ enc₂) d e) :
    ComputableTidilyInDegree (fun x => (f x).2) encIn enc₂ (max d e) e :=
  ((snd enc₁ enc₂).comp h).mono

/-- Functions on finite types, in linear time and zero space, with output of constant length. -/
public theorem of_finite [Finite α] (f : α → β) : ComputableTidilyInDegree f encIn encMid 1 0 := by
  obtain ⟨c, h⟩ := computableInTimeAndSpace_of_finite (encIn := encIn) (encOut := encMid) f
  refine ⟨(of_linear ⟨c, h.mono
    (fun _ => Nat.le_mul_of_pos_right _ (Nat.succ_pos _)) (fun _ => Nat.zero_le _)⟩).1, ?_⟩
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨0, fun a => isEmptyElim a⟩
  · obtain ⟨a₀, ha₀⟩ := Finite.exists_max fun a => (encMid (f a)).length
    exact ⟨_, fun a => by simpa using ha₀ a⟩

variable {enc₁ : β ↪ List Bool}

/-- `Option.some`. -/
public theorem optionSome {enc : Option β ↪ List Bool} [OptionEncoding enc₁ enc] :
    ComputableTidilyInDegree some enc₁ enc 1 1 :=
  of_linear OptionEncoding.some

/-- `Option.getD`. -/
public theorem getD {enc : Option β ↪ List Bool} [OptionEncoding enc₁ enc] (d : β) :
    ComputableTidilyInDegree (fun o => o.getD d) enc enc₁ 1 1 :=
  of_linear ((OptionEncoding.getD d))

/-- `List.headD`. -/
public theorem headD {enc : List β ↪ List Bool} [ListEncoding enc₁ enc] (d : β) :
    ComputableTidilyInDegree (fun l => l.headD d) enc enc₁ 1 1 :=
  of_linear ((ListEncoding.headD d))

/-- `List.tail`. -/
public theorem tail {enc : List β ↪ List Bool} [ListEncoding enc₁ enc] :
    ComputableTidilyInDegree List.tail enc enc 1 1 :=
  of_linear ((ListEncoding.tail (enc₁ := enc₁)))

/-- `List.isEmpty`. -/
public theorem isEmpty {enc : List β ↪ List Bool} [ListEncoding enc₁ enc] :
    ComputableTidilyInDegree List.isEmpty enc encBool 1 1 :=
  of_linear ((ListEncoding.isEmpty (enc₁ := enc₁)))

end ComputableTidilyInDegree

namespace ComputableInDegree

variable {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
  {d e d' e' : ℕ}

/-- Increasing either degree retains the same realizing machine. -/
public theorem mono (h : ComputableInDegree f encIn encOut d e)
    (hd : d ≤ d' := by first | decide | omega) (he : e ≤ e' := by first | decide | omega) :
    ComputableInDegree f encIn encOut d' e' :=
  let ⟨⟨t, s, ht, hs, hf⟩, hl⟩ := h
  ⟨⟨t, s, ht.mono_deg hd, hs.mono_deg hd, hf⟩, hl.mono_deg he⟩

/-- Exact time and workspace bounds of degree `d` also bound the output length in degree `d`. -/
public theorem of_bounds {t s : α → ℕ}
    (ht : DegreeBounded (fun a => (encIn a).length) t d)
    (hs : DegreeBounded (fun a => (encIn a).length) s d)
    (hf : ComputableInTimeAndSpace f encIn encOut t s) :
    ComputableInDegree f encIn encOut d d :=
  ⟨⟨t, s, ht, hs, hf⟩, ht.mono hf.length_le⟩

/-- Fixed time and workspace degrees give plain polynomial-time computability, including degree
zero. Encoded output is bounded separately and is not charged to workspace. -/
public theorem computableInPolyTime (h : ComputableInDegree f encIn encOut d e) :
    ComputableInPolyTime f encIn encOut := by
  obtain ⟨⟨_, _, ht, hs, h⟩, _⟩ := h
  obtain ⟨T, hT, ht⟩ := ht.polyBounded
  obtain ⟨S, hS, hs⟩ := hs.polyBounded
  exact ⟨T, S, hT, hS, h.mono ht hs⟩

end ComputableInDegree

end Turing.MultiTapeTM
