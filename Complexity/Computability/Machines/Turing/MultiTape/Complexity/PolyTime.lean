/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import all Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
public import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Foldl
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat

/-!
# Polynomial-time computability

`ComputableInPolyTime f encIn encOut`: `f` is computable within time and space
bounded by a polynomial in the length of the encoded input. The class is closed under composition,
case distinctions and pairing, contains every function computable in linear time and space,
and does not depend on the encodings up to polynomial-time conversions
(`Turing.MultiTapeTM.EncodingEquiv`).

## Main definitions

* `Turing.MultiTapeTM.PolyBounded`: a function bounded by a polynomial in a size.
* `Turing.MultiTapeTM.ComputableInPolyTime`: ordinary polynomial-time computability with
  independent time and space bounds.
* `Turing.MultiTapeTM.EncodingEquiv`: encodings that convert into each other in polynomial time.

## Main results

* `Turing.MultiTapeTM.PolyBounded.exists_le`, `.of_forall_le`: recover and supply explicit
  polynomial bounds for the size adapter over `Cslib.PolynomiallyBounded`.
* `Turing.MultiTapeTM.ComputableInPolyTime.comp`, `.ite`, `.pair`: closure properties.
* `Turing.MultiTapeTM.ComputableInPolyTime.foldl`: left folds with polynomially bounded
  intermediate states.
* `Turing.MultiTapeTM.EncodingEquiv.computableInPolyTime_iff`: polynomial-time computability
  transfers along equivalent encodings.
* `Turing.MultiTapeTM.computableInPolyTime_succ`: the successor in binary.

The closure properties are registered with `fun_prop`, so polynomial-time computability of a
composite function follows from that of its parts.
-/

namespace Turing.MultiTapeTM

universe u

/-! ### Polynomial bounds -/

-- vendored: express size-dependent bounds through cslib's `PolynomiallyBounded` and reuse
-- its closure rules; `exists_le` and `of_forall_le` preserve the original explicit-bound contract.
/-- `u` is bounded by a polynomially bounded function of `size`. This adapts
`Cslib.PolynomiallyBounded` to arbitrary inputs; it does not assert computability. -/
@[expose] public def PolyBounded {α : Type*} (size u : α → ℕ) : Prop :=
  ∃ bound : ℕ → ℕ, Cslib.PolynomiallyBounded bound ∧ ∀ a, u a ≤ bound (size a)

namespace PolyBounded

variable {α β : Type*} {size : α → ℕ} {u v : α → ℕ}

/-- Recover an explicit polynomial bound valid at every input, including size zero. -/
public theorem exists_le (h : PolyBounded size u) :
    ∃ c d, ∀ a, u a ≤ c * (size a + 1) ^ d := by
  obtain ⟨bound, hbound, h⟩ := h
  obtain ⟨c, d, hp⟩ := Cslib.polynomiallyBounded_iff_le.mp hbound
  exact ⟨c, d, fun a => (h a).trans (hp (size a))⟩

/-- Supply an explicit polynomial bound in the input size. -/
public theorem of_forall_le (c d : ℕ) (h : ∀ a, u a ≤ c * (size a + 1) ^ d) :
    PolyBounded size u :=
  ⟨_, Cslib.PolynomiallyBounded.of_forall_le c d (fun _ => le_rfl), h⟩

/-- Apply a polynomial bound to any input-size function. -/
public theorem of_polynomiallyBounded (size : α → ℕ) {bound : ℕ → ℕ}
    (hbound : Cslib.PolynomiallyBounded bound) : PolyBounded size (fun a => bound (size a)) :=
  ⟨bound, hbound, fun _ => le_rfl⟩

/-- With the identity size, the adapter gives CSLib's polynomial-growth predicate. -/
public theorem polynomiallyBounded {f : ℕ → ℕ} (h : PolyBounded id f) :
    Cslib.PolynomiallyBounded f :=
  let ⟨_, hbound, h⟩ := h
  hbound.mono_of_le h

public theorem mono (h : PolyBounded size v) (huv : ∀ a, u a ≤ v a) : PolyBounded size u :=
  let ⟨bound, hbound, hv⟩ := h
  ⟨bound, hbound, fun a => (huv a).trans (hv a)⟩

public theorem const (k : ℕ) : PolyBounded size fun _ => k :=
  of_polynomiallyBounded size (.const k)

public theorem self : PolyBounded size size :=
  of_polynomiallyBounded size .id

public theorem add (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size fun a => u a + v a :=
  let ⟨_, hp, hu⟩ := hu
  let ⟨_, hq, hv⟩ := hv
  ⟨_, hp.add hq, fun a => Nat.add_le_add (hu a) (hv a)⟩

public theorem mul (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size fun a => u a * v a :=
  let ⟨_, hp, hu⟩ := hu
  let ⟨_, hq, hv⟩ := hv
  ⟨_, hp.mul hq, fun a => Nat.mul_le_mul (hu a) (hv a)⟩

/-- Substitution: if `v` is bounded by a polynomial in `size'` and `size' ∘ g` by a polynomial in
`size`, then `v ∘ g` is bounded by a polynomial in `size`. -/
public theorem comp {size' : β → ℕ} {v : β → ℕ} {g : α → β} (hv : PolyBounded size' v)
    (hg : PolyBounded size fun a => size' (g a)) : PolyBounded size fun a => v (g a) := by
  obtain ⟨c, d, hv⟩ := hv.exists_le
  obtain ⟨bound, hbound, hg⟩ := hg
  refine ⟨fun n => c * (bound n + 1) ^ d, by fun_prop, fun a => ?_⟩
  exact (hv (g a)).trans (Nat.mul_le_mul_left c
    (Nat.pow_le_pow_left (Nat.add_le_add_right (hg a) 1) d))

end PolyBounded

/-! ### Polynomial time -/

/-- `f` is tidily computable within time and space bounded by a polynomial in the length of the
encoded input. -/
@[expose] public def ComputableTidilyInPolyTime {α β : Type*} (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) : Prop :=
  ∃ t s, PolyBounded (fun a => (encIn a).length) t ∧ PolyBounded (fun a => (encIn a).length) s ∧
    ComputableTidilyInTimeAndSpace f encIn encOut t s



-- Transitional registration while the remaining topic providers are being cut over.
attribute [fun_prop] ComputableTidilyInPolyTime

namespace ComputableInPolyTime

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- A common linear bound gives polynomial-time computability without a clean-tape premise. -/
public theorem of_linear {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} (h : ComputableInLinearTimeAndSpace f encIn encOut) :
    ComputableInPolyTime f encIn encOut := by
  obtain ⟨c, h⟩ := h
  exact ⟨fun n => c * (n + 1), fun n => c * (n + 1),
    Cslib.PolynomiallyBounded.mul (.const c) (.add .id (.const 1)),
    Cslib.PolynomiallyBounded.mul (.const c) (.add .id (.const 1)), h⟩

/-- Composition preserves polynomial-time computability with independent time and space bounds. -/
public theorem comp {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
    {encOut : γ ↪ List Bool} {f : β → γ} {g : α → β}
    (hf : ComputableInPolyTime f encMid encOut) (hg : ComputableInPolyTime g encIn encMid) :
    ComputableInPolyTime (f ∘ g) encIn encOut := by
  obtain ⟨t₁, s₁, ht₁, hs₁, h₁⟩ := Internal.normalizePolyTime hg
  obtain ⟨t₂, s₂, ht₂, hs₂, h₂⟩ := Internal.normalizePolyTime hf
  have hl : PolyBounded (fun a => (encIn a).length) (fun a => (encMid (g a)).length) :=
    (PolyBounded.of_polynomiallyBounded _ ht₁).mono h₁.length_le
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.comp_linear h₂ h₁
  have hm := (PolyBounded.const c).mul (hl.add (PolyBounded.const 1))
  have ht := ((PolyBounded.of_polynomiallyBounded _ ht₁).add
    ((PolyBounded.of_polynomiallyBounded _ ht₂).comp hl)).add hm
  have hs := ((PolyBounded.of_polynomiallyBounded _ hs₁).add
    ((PolyBounded.of_polynomiallyBounded _ hs₂).comp hl)).add hm
  obtain ⟨T, hT, ht⟩ := ht
  obtain ⟨S, hS, hs⟩ := hs
  exact Internal.forgetPolyTime hT hS (h.mono ht hs)


/-- The encoded value of a polynomial-time computation has polynomial length. -/
public theorem polyBounded_length {f : α → β} (h : ComputableInPolyTime f encIn encMid) :
    PolyBounded (fun a => (encIn a).length) fun a => (encMid (f a)).length :=
  let ⟨_, _, ht, _, h⟩ := h
  (PolyBounded.of_polynomiallyBounded _ ht).mono h.length_le

/-- Restrict a polynomial-time computation to a subset of its inputs. -/
public theorem restrict {f : α → β} (h : ComputableInPolyTime f encIn encMid)
    (p : α → Prop) :
    ComputableInPolyTime (f ∘ Subtype.val) ((Function.Embedding.subtype p).trans encIn) encMid :=
  let ⟨t, s, ht, hs, k, State, hfinite, tm, htm⟩ := h
  ⟨t, s, ht, hs, k, State, hfinite, tm, fun a => htm a.val⟩

/-- Compute a conditional from a computed Boolean and certified branches on their input subsets. -/
public theorem ite {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    (hc : ComputableInPolyTime c encIn encC)
    (hf : ComputableInPolyTime (f ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = true)).trans encIn) encMid)
    (hg : ComputableInPolyTime (g ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = false)).trans encIn) encMid) :
    ComputableInPolyTime (fun x => if c x then f x else g x) encIn encMid := by
  have rawC : ∃ t s, PolyBounded (fun a => (encIn a).length) t ∧
      PolyBounded (fun a => (encIn a).length) s ∧
      ComputableTidilyInTimeAndSpace c encIn encC t s := by
    obtain ⟨T, S, hT, hS, h⟩ := Internal.normalizePolyTime hc
    exact ⟨_, _, PolyBounded.of_polynomiallyBounded _ hT,
      PolyBounded.of_polynomiallyBounded _ hS, h⟩
  have rawF : ∃ t s,
      PolyBounded (fun a => (((Function.Embedding.subtype (c · = true)).trans encIn) a).length) t ∧
      PolyBounded (fun a => (((Function.Embedding.subtype (c · = true)).trans encIn) a).length) s ∧
      ComputableTidilyInTimeAndSpace (f ∘ Subtype.val)
        ((Function.Embedding.subtype (c · = true)).trans encIn) encMid t s := by
    obtain ⟨T, S, hT, hS, h⟩ := Internal.normalizePolyTime hf
    exact ⟨_, _, PolyBounded.of_polynomiallyBounded _ hT,
      PolyBounded.of_polynomiallyBounded _ hS, h⟩
  have rawG : ∃ t s,
      PolyBounded (fun a => (((Function.Embedding.subtype (c · = false)).trans encIn) a).length) t ∧
      PolyBounded (fun a => (((Function.Embedding.subtype (c · = false)).trans encIn) a).length) s ∧
      ComputableTidilyInTimeAndSpace (g ∘ Subtype.val)
        ((Function.Embedding.subtype (c · = false)).trans encIn) encMid t s := by
    obtain ⟨T, S, hT, hS, h⟩ := Internal.normalizePolyTime hg
    exact ⟨_, _, PolyBounded.of_polynomiallyBounded _ hT,
      PolyBounded.of_polynomiallyBounded _ hS, h⟩
  suffices h : ∃ t s, PolyBounded (fun a => (encIn a).length) t ∧
      PolyBounded (fun a => (encIn a).length) s ∧
      ComputableTidilyInTimeAndSpace (fun x => if c x then f x else g x) encIn encMid t s by
    obtain ⟨_, _, ⟨T, hT, ht⟩, ⟨S, hS, hs⟩, h⟩ := h
    exact Internal.forgetPolyTime hT hS (h.mono ht hs)
  obtain ⟨tc, sc, htc, hsc, h₀⟩ := rawC
  obtain ⟨tf, sf, htf, hsf, h₁⟩ := rawF
  obtain ⟨tg, sg, htg, hsg, h₂⟩ := rawG
  -- the bounds of the branches, extended to all inputs
  let ext (u : {x // c x = true} → ℕ) (v : {x // c x = false} → ℕ) (x : α) : ℕ :=
    if h : c x = true then u ⟨x, h⟩ else v ⟨x, by simpa using h⟩
  obtain ⟨k, h⟩ := ComputableTidilyInTimeAndSpace.ite h₀ (tf := ext tf tg) (sf := ext sf sg)
    (tg := ext tf tg) (sg := ext sf sg)
    (h₁.mono (fun x => by simp [ext, x.2]) (fun x => by simp [ext, x.2]))
    (h₂.mono (fun x => by simp [ext, x.2]) (fun x => by simp [ext, x.2]))
  have hext {u v}
      (hu : PolyBounded (fun x : {x // c x = true} => (encIn x).length) u)
      (hv : PolyBounded (fun x : {x // c x = false} => (encIn x).length) v) :
      PolyBounded (fun a => (encIn a).length) (ext u v) := by
    obtain ⟨_, hbu, hu⟩ := hu
    obtain ⟨_, hbv, hv⟩ := hv
    refine ⟨_, hbu.add hbv, fun x => ?_⟩
    by_cases hx : c x = true
    · simpa [ext, hx] using Nat.le_add_right_of_le (hu ⟨x, hx⟩)
    · simpa [ext, hx] using Nat.le_add_left_of_le (hv ⟨x, by simpa using hx⟩)
  refine ⟨_, _, (htc.add (hext htf htg)).add (.const k), (hsc.add (hext hsf hsg)).add (.const k),
    h.mono (fun x => ?_) (fun x => ?_)⟩ <;>
  · by_cases hx : c x = true <;> simp [ext, hx]

/-- Concatenate two computed encoded values without requiring an inverse encoding. -/
public theorem append {δ : Type*} {enc₂ : δ ↪ List Bool} {f₁ : α → β} {f₂ : α → δ} {g : α → γ}
    (h₁ : ComputableInPolyTime f₁ encIn encMid)
    (h₂ : ComputableInPolyTime f₂ encIn enc₂)
    (hg : ∀ x, encOut (g x) = encMid (f₁ x) ++ enc₂ (f₂ x)) :
    ComputableInPolyTime g encIn encOut := by
  have raw1 : ∃ t s, PolyBounded (fun a => (encIn a).length) t ∧
      PolyBounded (fun a => (encIn a).length) s ∧
      ComputableTidilyInTimeAndSpace f₁ encIn encMid t s := by
    obtain ⟨T, S, hT, hS, h⟩ := Internal.normalizePolyTime h₁
    exact ⟨_, _, PolyBounded.of_polynomiallyBounded _ hT,
      PolyBounded.of_polynomiallyBounded _ hS, h⟩
  have raw2 : ∃ t s, PolyBounded (fun a => (encIn a).length) t ∧
      PolyBounded (fun a => (encIn a).length) s ∧
      ComputableTidilyInTimeAndSpace f₂ encIn enc₂ t s := by
    obtain ⟨T, S, hT, hS, h⟩ := Internal.normalizePolyTime h₂
    exact ⟨_, _, PolyBounded.of_polynomiallyBounded _ hT,
      PolyBounded.of_polynomiallyBounded _ hS, h⟩
  suffices h : ∃ t s, PolyBounded (fun a => (encIn a).length) t ∧
      PolyBounded (fun a => (encIn a).length) s ∧
      ComputableTidilyInTimeAndSpace g encIn encOut t s by
    obtain ⟨_, _, ⟨T, hT, ht⟩, ⟨S, hS, hs⟩, h⟩ := h
    exact Internal.forgetPolyTime hT hS (h.mono ht hs)
  obtain ⟨t₁, s₁, ht₁, hs₁, h₁⟩ := raw1
  obtain ⟨t₂, s₂, ht₂, hs₂, h₂⟩ := raw2
  obtain ⟨k, h⟩ := h₁.append h₂ hg
  exact ⟨_, _, ht₁.add ht₂, (hs₁.add hs₂).add (.const k), h⟩

/-- Pair computed values using the declared pair interface and its explicit output-space charge. -/
public theorem pair {α β₁ β₂ : Type u} {encIn : α ↪ List Bool} {enc₁ : β₁ ↪ List Bool}
    {enc₂ : β₂ ↪ List Bool} {enc : β₁ × β₂ ↪ List Bool} [PairEncoding enc₁ enc₂ enc]
    {f : α → β₁} {g : α → β₂} (hf : ComputableInPolyTime f encIn enc₁)
    (hg : ComputableInPolyTime g encIn enc₂) :
    ComputableInPolyTime (fun x => (f x, g x)) encIn enc := by
  let hP : PairEncoding enc₁ enc₂ enc := inferInstance
  have rawF : ∃ t s, PolyBounded (fun a => (encIn a).length) t ∧
      PolyBounded (fun a => (encIn a).length) s ∧
      ComputableTidilyInTimeAndSpace f encIn enc₁ t s := by
    obtain ⟨T, S, hT, hS, h⟩ := Internal.normalizePolyTime hf
    exact ⟨_, _, PolyBounded.of_polynomiallyBounded _ hT,
      PolyBounded.of_polynomiallyBounded _ hS, h⟩
  have rawG : ∃ t s, PolyBounded (fun a => (encIn a).length) t ∧
      PolyBounded (fun a => (encIn a).length) s ∧
      ComputableTidilyInTimeAndSpace g encIn enc₂ t s := by
    obtain ⟨T, S, hT, hS, h⟩ := Internal.normalizePolyTime hg
    exact ⟨_, _, PolyBounded.of_polynomiallyBounded _ hT,
      PolyBounded.of_polynomiallyBounded _ hS, h⟩
  suffices h : ∃ t s, PolyBounded (fun a => (encIn a).length) t ∧
      PolyBounded (fun a => (encIn a).length) s ∧
      ComputableTidilyInTimeAndSpace (fun x => (f x, g x)) encIn enc t s by
    obtain ⟨_, _, ⟨T, hT, ht⟩, ⟨S, hS, hs⟩, h⟩ := h
    exact Internal.forgetPolyTime hT hS (h.mono ht hs)
  obtain ⟨t₁, s₁, ht₁, hs₁, h₁⟩ := rawF
  obtain ⟨t₂, s₂, ht₂, hs₂, h₂⟩ := rawG
  obtain ⟨c, h⟩ := hP.pair_mono h₁.computableInTimeAndSpace h₂.computableInTimeAndSpace
  obtain ⟨c, h⟩ := Internal.normalizeBigO ⟨c, h⟩
  have ht := (PolyBounded.const c).mul ((ht₁.add ht₂).add (.const 1))
  refine ⟨_, _, ht, (PolyBounded.const c).mul (((hs₁.add hs₂).add ht).add (.const 1)),
    h.mono (fun _ => le_rfl) (fun x => Nat.mul_le_mul_left c ?_)⟩
  have := h.length_le x
  omega

/-- Composition in ordinary lambda notation. -/
@[fun_prop]
public theorem comp' {f : β → γ} {g : α → β} (hf : ComputableInPolyTime f encMid encOut)
    (hg : ComputableInPolyTime g encIn encMid) :
    ComputableInPolyTime (fun a => f (g a)) encIn encOut :=
  hf.comp hg

/-- Pair computed values in the framed pair encoding. -/
@[fun_prop]
public theorem prod {α β₁ β₂ : Type u} {encIn : α ↪ List Bool} {enc₁ : β₁ ↪ List Bool}
    {enc₂ : β₂ ↪ List Bool} {f : α → β₁} {g : α → β₂} (hf : ComputableInPolyTime f encIn enc₁)
    (hg : ComputableInPolyTime g encIn enc₂) :
    ComputableInPolyTime (fun x => (f x, g x)) encIn (encPair enc₁ enc₂) :=
  hf.pair hg

/-- Composition in execution order, fixing the intermediate encoding from the inner certificate. -/
@[fun_prop]
public theorem trans {f : α → β} {g : β → γ} (hf : ComputableInPolyTime f encIn encMid)
    (hg : ComputableInPolyTime g encMid encOut) :
    ComputableInPolyTime (fun x => g (f x)) encIn encOut :=
  hg.comp hf

/-- The first projection of a framed pair is polynomial-time. -/
@[fun_prop]
public theorem fst {β₁ β₂ : Type u} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableInPolyTime (fun p : β₁ × β₂ => p.1) (encPair enc₁ enc₂) enc₁ :=
  .of_linear (.of_unframe fun p => by simp)

/-- The second projection of a framed pair is polynomial-time. -/
@[fun_prop]
public theorem snd {β₁ β₂ : Type u} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableInPolyTime (fun p : β₁ × β₂ => p.2) (encPair enc₁ enc₂) enc₂ :=
  .of_linear (.of_dropFrame fun p => by simp)

-- This explicit projection must stay unregistered: automatic primitive and encoding-aware
-- projection rules determine component encodings before composition.
/-- Explicitly project the first component after computing a pair-valued function. -/
public theorem fst' {β₁ β₂ : Type u} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {f : α → β₁ × β₂} (hf : ComputableInPolyTime f encIn (encPair enc₁ enc₂)) :
    ComputableInPolyTime (fun x => (f x).1) encIn enc₁ :=
  (fst enc₁ enc₂).comp hf

/-- Project the second component after computing a pair-valued function. -/
@[fun_prop]
public theorem snd' {β₁ β₂ : Type u} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {f : α → β₁ × β₂} (hf : ComputableInPolyTime f encIn (encPair enc₁ enc₂)) :
    ComputableInPolyTime (fun x => (f x).2) encIn enc₂ :=
  (snd enc₁ enc₂).comp hf

/-- A Boolean conditional whose two branches are certified on every input. -/
@[fun_prop]
public theorem ite' {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    (hc : ComputableInPolyTime c encIn encC) (hf : ComputableInPolyTime f encIn encMid)
    (hg : ComputableInPolyTime g encIn encMid) :
    ComputableInPolyTime (fun x => if c x then f x else g x) encIn encMid :=
  hc.ite (hf.restrict _) (hg.restrict _)

end ComputableInPolyTime

/-! ### Equivalent encodings -/

/-- Encodings that convert into each other in polynomial time. -/
public def EncodingEquiv {α : Type*} (enc₁ enc₂ : α ↪ List Bool) : Prop :=
  ComputableInPolyTime id enc₁ enc₂ ∧ ComputableInPolyTime id enc₂ enc₁

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
public theorem computableInPolyTime_iff {encIn encIn' : α ↪ List Bool}
    {encOut encOut' : β ↪ List Bool} (hIn : EncodingEquiv encIn encIn')
    (hOut : EncodingEquiv encOut encOut') {f : α → β} :
    ComputableInPolyTime f encIn encOut ↔ ComputableInPolyTime f encIn' encOut' :=
  ⟨fun h => (hOut.1.comp h).comp hIn.2, fun h => (hOut.2.comp h).comp hIn.1⟩

end EncodingEquiv

/-! ### Left folds -/

/-- Left folds are computable in polynomial time if the list, the initial value and `step`
are, and the length of the list, the intermediate states and the arguments of `step` are bounded by
a polynomial in the length of the encoded input. -/
public theorem ComputableInPolyTime.foldl {γ α β : Type u} {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encL : List α ↪ List Bool}
    {encBA : β × α ↪ List Bool} {encS : List α × β ↪ List Bool}
    {encO : Option (List α × β) ↪ List Bool}
    [ListEncoding encA encL] [PairEncoding encB encA encBA] [PairEncoding encL encB encS]
    [OptionEncoding encS encO] {list : γ → List α} {init : γ → β} {step : β → α → β}
    (hlist : ComputableInPolyTime list encIn encL)
    (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun p : β × α => step p.1 p.2) encBA encB)
    {lMax aMax : γ → ℕ} (hlMax' : PolyBounded (fun x => (encIn x).length) lMax)
    (haMax' : PolyBounded (fun x => (encIn x).length) aMax)
    (hlen : PolyBounded (fun x => (encIn x).length) fun x => (list x).length)
    (haMax : ∀ x i (hi : i < (list x).length),
      (encBA (((list x).take i).foldl step (init x), (list x)[i])).length ≤ aMax x)
    (hlMax : ∀ x, ∀ i ≤ (list x).length,
      (encS ((list x).drop i, ((list x).take i).foldl step (init x))).length ≤ lMax x) :
    ComputableInPolyTime (fun x => (list x).foldl step (init x)) encIn encB := by
  have rawList : ∃ t s, PolyBounded (fun a => (encIn a).length) t ∧
      PolyBounded (fun a => (encIn a).length) s ∧
      ComputableTidilyInTimeAndSpace list encIn encL t s := by
    obtain ⟨T, S, hT, hS, h⟩ := Internal.normalizePolyTime hlist
    exact ⟨_, _, PolyBounded.of_polynomiallyBounded _ hT,
      PolyBounded.of_polynomiallyBounded _ hS, h⟩
  have rawInit : ∃ t s, PolyBounded (fun a => (encIn a).length) t ∧
      PolyBounded (fun a => (encIn a).length) s ∧
      ComputableTidilyInTimeAndSpace init encIn encB t s := by
    obtain ⟨T, S, hT, hS, h⟩ := Internal.normalizePolyTime hinit
    exact ⟨_, _, PolyBounded.of_polynomiallyBounded _ hT,
      PolyBounded.of_polynomiallyBounded _ hS, h⟩
  have rawStep : ∃ t s, PolyBounded (fun a => (encBA a).length) t ∧
      PolyBounded (fun a => (encBA a).length) s ∧
      ComputableTidilyInTimeAndSpace (fun p : β × α => step p.1 p.2) encBA encB t s := by
    obtain ⟨T, S, hT, hS, h⟩ := Internal.normalizePolyTime hstep
    exact ⟨_, _, PolyBounded.of_polynomiallyBounded _ hT,
      PolyBounded.of_polynomiallyBounded _ hS, h⟩
  suffices h : ∃ t s, PolyBounded (fun a => (encIn a).length) t ∧
      PolyBounded (fun a => (encIn a).length) s ∧
      ComputableTidilyInTimeAndSpace (fun x => (list x).foldl step (init x)) encIn encB t s by
    obtain ⟨_, _, ⟨T, hT, ht⟩, ⟨S, hS, hs⟩, h⟩ := h
    exact Internal.forgetPolyTime hT hS (h.mono ht hs)
  obtain ⟨t₁, s₁, ht₁, hs₁, h₁⟩ := rawList
  obtain ⟨t₂, s₂, ht₂, hs₂, h₂⟩ := rawInit
  obtain ⟨tS, sS, htS, hsS, hS⟩ := rawStep
  obtain ⟨ct, dt, htS⟩ := htS.exists_le
  obtain ⟨cs, ds, hsS⟩ := hsS.exists_le
  have hmax {c d : ℕ} : PolyBounded (fun x => (encIn x).length) fun x => c * (aMax x + 1) ^ d :=
    PolyBounded.comp (size' := id) (v := fun n => c * (n + 1) ^ d)
      (.of_forall_le c d (fun _ => le_rfl)) haMax'
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

/-- The successor is computable in polynomial time, in the binary encoding `encNat`. -/
@[fun_prop]
public theorem computableInPolyTime_succ : ComputableInPolyTime (· + 1) encNat encNat := by
  suffices h : ∃ t s, PolyBounded (fun a => (encNat a).length) t ∧
      PolyBounded (fun a => (encNat a).length) s ∧
      ComputableTidilyInTimeAndSpace (· + 1) encNat encNat t s by
    obtain ⟨_, _, ⟨T, hT, ht⟩, ⟨S, hS, hs⟩, h⟩ := h
    exact Internal.forgetPolyTime hT hS (h.mono ht hs)
  obtain ⟨c, h⟩ := computableTidilyInTimeAndSpace_succ
  exact ⟨_, _, PolyBounded.of_forall_le c 2 (fun _ => le_rfl),
    PolyBounded.of_forall_le c 1 (fun _ => by simp), h⟩

end Turing.MultiTapeTM
