/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Mathlib.Tactic.FunProp
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Foldl
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
import Mathlib.Tactic.Ring

/-!
# Tidy computability in polynomial time

`ComputableTidilyInPolyTime f encIn encOut`: `f` is tidily computable within time and space
bounded by a polynomial in the length of the encoded input. The class is closed under composition,
case distinctions and pairing, contains every function tidily computable in linear time and space,
and does not depend on the encodings up to polynomial-time conversions
(`Turing.MultiTapeTM.EncodingEquiv`).

## Main definitions

* `Turing.MultiTapeTM.PolyBounded`: a function bounded by a polynomial in a size.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime`: tidy computability in polynomial time and space.
* `Turing.MultiTapeTM.EncodingEquiv`: encodings that convert into each other in polynomial time.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.comp`, `.ite`, `.pair`: closure properties.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldl`: left folds with polynomially bounded
  intermediate states.
* `Turing.MultiTapeTM.EncodingEquiv.computableTidilyInPolyTime_iff`: polynomial-time computability
  transfers along equivalent encodings.
* `Turing.MultiTapeTM.computableTidilyInPolyTime_succ`: the successor in binary.

The closure properties are registered with `fun_prop`, so polynomial-time computability of a
composite function follows from that of its parts.
-/

namespace Turing.MultiTapeTM

universe u

/-! ### Polynomial bounds -/

/-- `u` is bounded by a polynomial in `size`. -/
@[expose] public def PolyBounded {α : Type*} (size u : α → ℕ) : Prop :=
  ∃ c d, ∀ a, u a ≤ c * (size a + 1) ^ d

namespace PolyBounded

variable {α β : Type*} {size : α → ℕ} {u v : α → ℕ}

public theorem mono (h : PolyBounded size v) (huv : ∀ a, u a ≤ v a) : PolyBounded size u :=
  let ⟨c, d, hv⟩ := h
  ⟨c, d, fun a => (huv a).trans (hv a)⟩

public theorem const (k : ℕ) : PolyBounded size fun _ => k :=
  ⟨k, 0, fun _ => by simp⟩

public theorem self : PolyBounded size size :=
  ⟨1, 1, fun _ => by simp⟩

public theorem add (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size fun a => u a + v a := by
  obtain ⟨c₁, d₁, h₁⟩ := hu
  obtain ⟨c₂, d₂, h₂⟩ := hv
  refine ⟨c₁ + c₂, max d₁ d₂, fun a => (add_le_add (h₁ a) (h₂ a)).trans ?_⟩
  rw [Nat.add_mul]
  gcongr <;> omega

public theorem mul (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size fun a => u a * v a := by
  obtain ⟨c₁, d₁, h₁⟩ := hu
  obtain ⟨c₂, d₂, h₂⟩ := hv
  refine ⟨c₁ * c₂, d₁ + d₂, fun a => (Nat.mul_le_mul (h₁ a) (h₂ a)).trans_eq ?_⟩
  rw [Nat.pow_add]
  ring

/-- Substitution: if `v` is bounded by a polynomial in `size'` and `size' ∘ g` by a polynomial in
`size`, then `v ∘ g` is bounded by a polynomial in `size`. -/
public theorem comp {size' : β → ℕ} {v : β → ℕ} {g : α → β} (hv : PolyBounded size' v)
    (hg : PolyBounded size fun a => size' (g a)) : PolyBounded size fun a => v (g a) := by
  obtain ⟨c₁, d₁, h₁⟩ := hg
  obtain ⟨c₂, d₂, h₂⟩ := hv
  refine ⟨c₂ * (c₁ + 1) ^ d₂, d₁ * d₂, fun a => (h₂ (g a)).trans ?_⟩
  have h : size' (g a) + 1 ≤ (c₁ + 1) * (size a + 1) ^ d₁ := by
    have := h₁ a
    dsimp only at this
    have := Nat.one_le_pow d₁ (size a + 1) (Nat.succ_pos _)
    rw [Nat.add_one_mul]
    omega
  refine (Nat.mul_le_mul_left c₂ (Nat.pow_le_pow_left h d₂)).trans_eq ?_
  rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc]

end PolyBounded

/-! ### Polynomial time -/

/-- `f` is tidily computable within time and space bounded by a polynomial in the length of the
encoded input. -/
@[expose] public def ComputableTidilyInPolyTime {α β : Type*} (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) : Prop :=
  ∃ t s, PolyBounded (fun a => (encIn a).length) t ∧ PolyBounded (fun a => (encIn a).length) s ∧
    ComputableTidilyInTimeAndSpace f encIn encOut t s

namespace ComputableTidilyInPolyTime

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- The encoded value of a function computable in polynomial time has polynomial length. -/
public theorem polyBounded_length {f : α → β} (h : ComputableTidilyInPolyTime f encIn encMid) :
    PolyBounded (fun a => (encIn a).length) fun a => (encMid (f a)).length :=
  let ⟨_, _, ht, _, hf⟩ := h
  ht.mono hf.length_le

public theorem of_linear {f : α → β} (h : ComputableTidilyInLinearTimeAndSpace f encIn encMid) :
    ComputableTidilyInPolyTime f encIn encMid :=
  let ⟨c, hc⟩ := h
  ⟨_, _, ⟨c, 1, fun _ => by simp⟩, ⟨c, 1, fun _ => by simp⟩, hc⟩

public theorem comp {f : β → γ} {g : α → β} (hf : ComputableTidilyInPolyTime f encMid encOut)
    (hg : ComputableTidilyInPolyTime g encIn encMid) :
    ComputableTidilyInPolyTime (f ∘ g) encIn encOut := by
  have hl := hg.polyBounded_length
  obtain ⟨t₁, s₁, ht₁, hs₁, h₁⟩ := hg
  obtain ⟨t₂, s₂, ht₂, hs₂, h₂⟩ := hf
  -- vendored: crei's `comp` is `comp_linear` here, as cslib #1111 restates `comp`
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.comp_linear h₂ h₁
  have hm := (PolyBounded.const c).mul (hl.add (PolyBounded.const 1))
  exact ⟨_, _, (ht₁.add (ht₂.comp hl)).add hm, (hs₁.add (hs₂.comp hl)).add hm, h⟩

public theorem restrict {f : α → β} (h : ComputableTidilyInPolyTime f encIn encMid)
    (p : α → Prop) :
    ComputableTidilyInPolyTime (f ∘ Subtype.val) ((Function.Embedding.subtype p).trans encIn)
      encMid :=
  let ⟨_, _, ⟨ct, dt, ht⟩, ⟨cs, ds, hs⟩, hf⟩ := h
  ⟨_, _, ⟨ct, dt, fun a => ht a⟩, ⟨cs, ds, fun a => hs a⟩, hf.restrict p⟩

public theorem ite {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    (hc : ComputableTidilyInPolyTime c encIn encC)
    (hf : ComputableTidilyInPolyTime (f ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = true)).trans encIn) encMid)
    (hg : ComputableTidilyInPolyTime (g ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = false)).trans encIn) encMid) :
    ComputableTidilyInPolyTime (fun x => if c x then f x else g x) encIn encMid := by
  obtain ⟨tc, sc, htc, hsc, h₀⟩ := hc
  obtain ⟨tf, sf, ⟨ctf, dtf, htf⟩, ⟨csf, dsf, hsf⟩, h₁⟩ := hf
  obtain ⟨tg, sg, ⟨ctg, dtg, htg⟩, ⟨csg, dsg, hsg⟩, h₂⟩ := hg
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
      PolyBounded (fun a => (encIn a).length) (ext u v) :=
    (PolyBounded.add ⟨cu, du, fun _ => le_rfl⟩ ⟨cv, dv, fun _ => le_rfl⟩).mono fun x => by
      by_cases hx : c x = true
      · simpa [ext, hx] using Nat.le_add_right_of_le (hu ⟨x, hx⟩)
      · simpa [ext, hx] using Nat.le_add_left_of_le (hv ⟨x, by simpa using hx⟩)
  refine ⟨_, _, (htc.add (hext htf htg)).add (.const k), (hsc.add (hext hsf hsg)).add (.const k),
    h.mono (fun x => ?_) (fun x => ?_)⟩ <;>
  · by_cases hx : c x = true <;> simp [ext, hx]

public theorem const (b : β) : ComputableTidilyInPolyTime (fun _ : α => b) encIn encMid :=
  of_linear (.const b)

public theorem of_eq {f : α → β} (h : ∀ a, encMid (f a) = encIn a) :
    ComputableTidilyInPolyTime f encIn encMid :=
  of_linear (.of_eq h)

public theorem append {δ : Type*} {enc₂ : δ ↪ List Bool} {f₁ : α → β} {f₂ : α → δ} {g : α → γ}
    (h₁ : ComputableTidilyInPolyTime f₁ encIn encMid)
    (h₂ : ComputableTidilyInPolyTime f₂ encIn enc₂)
    (hg : ∀ x, encOut (g x) = encMid (f₁ x) ++ enc₂ (f₂ x)) :
    ComputableTidilyInPolyTime g encIn encOut := by
  obtain ⟨t₁, s₁, ht₁, hs₁, h₁⟩ := h₁
  obtain ⟨t₂, s₂, ht₂, hs₂, h₂⟩ := h₂
  obtain ⟨k, h⟩ := h₁.append h₂ hg
  exact ⟨_, _, ht₁.add ht₂, (hs₁.add hs₂).add (.const k), h⟩

public theorem pair {α β₁ β₂ : Type u} {encIn : α ↪ List Bool} {enc₁ : β₁ ↪ List Bool}
    {enc₂ : β₂ ↪ List Bool} {enc : β₁ × β₂ ↪ List Bool} [hP : PairEncoding enc₁ enc₂ enc]
    {f : α → β₁} {g : α → β₂} (hf : ComputableTidilyInPolyTime f encIn enc₁)
    (hg : ComputableTidilyInPolyTime g encIn enc₂) :
    ComputableTidilyInPolyTime (fun x => (f x, g x)) encIn enc := by
  obtain ⟨t₁, s₁, ht₁, hs₁, h₁⟩ := hf
  obtain ⟨t₂, s₂, ht₂, hs₂, h₂⟩ := hg
  obtain ⟨c, h⟩ := hP.pair_mono h₁ h₂
  have ht := (PolyBounded.const c).mul ((ht₁.add ht₂).add (.const 1))
  refine ⟨_, _, ht, (PolyBounded.const c).mul (((hs₁.add hs₂).add ht).add (.const 1)),
    h.mono (fun _ => le_rfl) (fun x => Nat.mul_le_mul_left c ?_)⟩
  have := h.length_le x
  omega

/-! ### Automation -/

attribute [fun_prop] ComputableTidilyInPolyTime

attribute [fun_prop] const

@[fun_prop]
public theorem id' : ComputableTidilyInPolyTime (fun a : α => a) encIn encIn :=
  of_eq fun _ => rfl

@[fun_prop]
public theorem comp' {f : β → γ} {g : α → β} (hf : ComputableTidilyInPolyTime f encMid encOut)
    (hg : ComputableTidilyInPolyTime g encIn encMid) :
    ComputableTidilyInPolyTime (fun a => f (g a)) encIn encOut :=
  hf.comp hg

@[fun_prop]
public theorem prod {α β₁ β₂ : Type u} {encIn : α ↪ List Bool} {enc₁ : β₁ ↪ List Bool}
    {enc₂ : β₂ ↪ List Bool} {f : α → β₁} {g : α → β₂}
    (hf : ComputableTidilyInPolyTime f encIn enc₁) (hg : ComputableTidilyInPolyTime g encIn enc₂) :
    ComputableTidilyInPolyTime (fun x => (f x, g x)) encIn (encPair enc₁ enc₂) :=
  hf.pair hg

@[fun_prop]
public theorem fst {β₁ β₂ : Type u} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableTidilyInPolyTime (fun p : β₁ × β₂ => p.1) (encPair enc₁ enc₂) enc₁ :=
  of_linear (.of_unframe fun p => by simp)

@[fun_prop]
public theorem snd {β₁ β₂ : Type u} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableTidilyInPolyTime (fun p : β₁ × β₂ => p.2) (encPair enc₁ enc₂) enc₂ :=
  of_linear (.of_dropFrame fun p => by simp)

/-- A case distinction between functions computable in polynomial time on all inputs. -/
@[fun_prop]
public theorem ite' {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    (hc : ComputableTidilyInPolyTime c encIn encC) (hf : ComputableTidilyInPolyTime f encIn encMid)
    (hg : ComputableTidilyInPolyTime g encIn encMid) :
    ComputableTidilyInPolyTime (fun x => if c x then f x else g x) encIn encMid :=
  hc.ite (hf.restrict _) (hg.restrict _)

end ComputableTidilyInPolyTime

/-! ### Equivalent encodings -/

/-- Encodings that convert into each other in polynomial time. -/
public def EncodingEquiv {α : Type*} (enc₁ enc₂ : α ↪ List Bool) : Prop :=
  ComputableTidilyInPolyTime id enc₁ enc₂ ∧ ComputableTidilyInPolyTime id enc₂ enc₁

namespace EncodingEquiv

variable {α β : Type*} {enc₁ enc₂ enc₃ : α ↪ List Bool}

@[refl]
public theorem refl (enc : α ↪ List Bool) : EncodingEquiv enc enc :=
  ⟨.of_eq fun _ => rfl, .of_eq fun _ => rfl⟩

@[symm]
public theorem symm (h : EncodingEquiv enc₁ enc₂) : EncodingEquiv enc₂ enc₁ := ⟨h.2, h.1⟩

@[trans]
public theorem trans (h₁₂ : EncodingEquiv enc₁ enc₂) (h₂₃ : EncodingEquiv enc₂ enc₃) :
    EncodingEquiv enc₁ enc₃ :=
  ⟨h₂₃.1.comp h₁₂.1, h₁₂.2.comp h₂₃.2⟩

/-- Polynomial-time computability does not depend on the encodings, up to equivalence. -/
public theorem computableTidilyInPolyTime_iff {encIn encIn' : α ↪ List Bool}
    {encOut encOut' : β ↪ List Bool} (hIn : EncodingEquiv encIn encIn')
    (hOut : EncodingEquiv encOut encOut') {f : α → β} :
    ComputableTidilyInPolyTime f encIn encOut ↔ ComputableTidilyInPolyTime f encIn' encOut' :=
  ⟨fun h => (hOut.1.comp h).comp hIn.2, fun h => (hOut.2.comp h).comp hIn.1⟩

end EncodingEquiv

/-! ### Left folds -/

/-- Left folds are tidily computable in polynomial time if the list, the initial value and `step`
are, and the length of the list, the intermediate states and the arguments of `step` are bounded by
a polynomial in the length of the encoded input. -/
public theorem ComputableTidilyInPolyTime.foldl {γ α β : Type u} {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encL : List α ↪ List Bool}
    {encBA : β × α ↪ List Bool} {encS : List α × β ↪ List Bool}
    {encO : Option (List α × β) ↪ List Bool}
    [ListEncoding encA encL] [PairEncoding encB encA encBA] [PairEncoding encL encB encS]
    [OptionEncoding encS encO] {list : γ → List α} {init : γ → β} {step : β → α → β}
    (hlist : ComputableTidilyInPolyTime list encIn encL)
    (hinit : ComputableTidilyInPolyTime init encIn encB)
    (hstep : ComputableTidilyInPolyTime (fun p : β × α => step p.1 p.2) encBA encB)
    {lMax aMax : γ → ℕ} (hlMax' : PolyBounded (fun x => (encIn x).length) lMax)
    (haMax' : PolyBounded (fun x => (encIn x).length) aMax)
    (hlen : PolyBounded (fun x => (encIn x).length) fun x => (list x).length)
    (haMax : ∀ x i (hi : i < (list x).length),
      (encBA (((list x).take i).foldl step (init x), (list x)[i])).length ≤ aMax x)
    (hlMax : ∀ x, ∀ i ≤ (list x).length,
      (encS ((list x).drop i, ((list x).take i).foldl step (init x))).length ≤ lMax x) :
    ComputableTidilyInPolyTime (fun x => (list x).foldl step (init x)) encIn encB := by
  obtain ⟨t₁, s₁, ht₁, hs₁, h₁⟩ := hlist
  obtain ⟨t₂, s₂, ht₂, hs₂, h₂⟩ := hinit
  obtain ⟨tS, sS, ⟨ct, dt, htS⟩, ⟨cs, ds, hsS⟩, hS⟩ := hstep
  have hmax {c d : ℕ} : PolyBounded (fun x => (encIn x).length) fun x => c * (aMax x + 1) ^ d :=
    PolyBounded.comp (size' := id) (v := fun n => c * (n + 1) ^ d) ⟨c, d, fun _ => le_rfl⟩ haMax'
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.foldl (encA := encA) (encL := encL)
    (encBA := encBA) (encS := encS) (encO := encO)
    (h₁.mono (t' := fun x => t₁ x + t₂ x) (s' := fun x => s₁ x + s₂ x)
      (fun _ => Nat.le_add_right _ _) (fun _ => Nat.le_add_right _ _))
    (h₂.mono (fun _ => Nat.le_add_left _ _) (fun _ => Nat.le_add_left _ _)) hS
    (tMax := fun x => ct * (aMax x + 1) ^ dt) (sMax := fun x => cs * (aMax x + 1) ^ ds)
    (fun x i hi => (htS _).trans (Nat.mul_le_mul_left ct (Nat.pow_le_pow_left
      (Nat.add_le_add_right (haMax x i hi) 1) dt)))
    (fun x i hi => (hsS _).trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left
      (Nat.add_le_add_right (haMax x i hi) 1) ds)))
    hlMax
  exact ⟨_, _, (PolyBounded.const c).mul ((ht₁.add ht₂).add
      ((hlen.add (.const 1)).mul ((hmax.add hlMax').add (.const 1)))),
    (PolyBounded.const c).mul ((((hs₁.add hs₂).add hmax).add hlMax').add (.const 1)), h⟩

/-- The successor is tidily computable in polynomial time, in the binary encoding `encNat`. -/
@[fun_prop]
public theorem computableTidilyInPolyTime_succ : ComputableTidilyInPolyTime (· + 1) encNat encNat :=
  let ⟨c, h⟩ := computableTidilyInTimeAndSpace_succ
  ⟨_, _, ⟨c, 2, fun _ => le_rfl⟩, ⟨c, 1, fun _ => by simp⟩, h⟩

end Turing.MultiTapeTM
