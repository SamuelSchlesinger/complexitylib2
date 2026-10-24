/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.NormalForm
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Foldl
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial

/-!
# Direct plain polynomial-time primitives

The canonical rules normalize plain realizing machines inside the internal proof, combine them
with machine-level combinators, and conclude plain computability. No tidy asymptotic predicate
or bridge participates in their statements or derivations.

## Main results

* `ComputableInPolyTime.comp`, `.pair`, `.ite`, `.foldl`: direct closure rules.
* `ComputableInPolyTime.fst`, `.snd`: ordinary encoded-pair projections.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

open Cslib

universe u
variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- A tidy machine within resources bounded by a polynomially bounded function of the length of
the encoded input certifies plain polynomial time. -/
private theorem of_computesTidily {f : α → β} {k : ℕ} {State : Type} [Finite State]
    {tm : MultiTapeTM k Bool State} {t s : α → ℕ} {T : ℕ → ℕ} (hT : PolynomiallyBounded T)
    (h : ∀ a, tm.ComputesTidilyInTimeAndSpace (encIn a) (encMid (f a)) (t a) (s a))
    (ht : ∀ a, t a ≤ T (encIn a).length) (hs : ∀ a, s a ≤ T (encIn a).length) :
    ComputableInPolyTime f encIn encMid :=
  ⟨T, T, hT, hT, k, State, inferInstance, tm,
    fun a => ((h a).mono (ht a) (hs a)).computesInTimeAndSpace⟩

/-- **Composition**, through the machine-level composition of tidy machines. The intermediate word
is no longer than the time of the inner machine. -/
@[fun_prop]
theorem comp {f : β → γ} {g : α → β} (hf : ComputableInPolyTime f encMid encOut)
    (hg : ComputableInPolyTime g encIn encMid) :
    ComputableInPolyTime (fun a => f (g a)) encIn encOut := by
  obtain ⟨c₁, d₁, k₁, S₁, _, tm₁, h₁⟩ := Internal.NormalForm.polyTime hg
  obtain ⟨c₂, d₂, k₂, S₂, _, tm₂, h₂⟩ := Internal.NormalForm.polyTime hf
  refine of_computesTidily (tm := tm₂.comp tm₁ true)
    (T := fun n => 6 * (c₁ * (n + 1) ^ d₁) + c₂ * (c₁ * (n + 1) ^ d₁ + 1) ^ d₂ +
      (6 * max k₁ k₂ + 20)) (by fun_prop) (fun a => (h₁ a).comp (h₂ (g a)) true)
    (fun a => ?_) (fun a => ?_) <;>
  · have hl := (h₁ a).length_output_le
    have := Nat.mul_le_mul_left c₂ (Nat.pow_le_pow_left (Nat.add_le_add_right hl 1) d₂)
    omega

/-- **Pairing**, for any encoding of pairs, through its pairing combinator. -/
@[fun_prop]
theorem pair {α β₁ β₂ : Type u} {encIn : α ↪ List Bool} {enc₁ : β₁ ↪ List Bool}
    {enc₂ : β₂ ↪ List Bool} {enc : β₁ × β₂ ↪ List Bool} [PairEncoding enc₁ enc₂ enc]
    {f : α → β₁} {g : α → β₂} (hf : ComputableInPolyTime f encIn enc₁)
    (hg : ComputableInPolyTime g encIn enc₂) :
    ComputableInPolyTime (fun x => (f x, g x)) encIn enc := by
  obtain ⟨c₁, d₁, k₁, S₁, _, tm₁, h₁⟩ := Internal.NormalForm.polyTime hf
  obtain ⟨c₂, d₂, k₂, S₂, _, tm₂, h₂⟩ := Internal.NormalForm.polyTime hg
  obtain ⟨c, k, S, _, tm, h⟩ := PairEncoding.pair_mono (enc := enc)
    (t₁ := fun a => c₁ * ((encIn a).length + 1) ^ d₁)
    (s₁ := fun a => c₁ * ((encIn a).length + 1) ^ d₁)
    (t₂ := fun a => c₂ * ((encIn a).length + 1) ^ d₂)
    (s₂ := fun a => c₂ * ((encIn a).length + 1) ^ d₂)
    ⟨k₁, S₁, inferInstance, tm₁, h₁⟩ ⟨k₂, S₂, inferInstance, tm₂, h₂⟩
  -- the encoded pair, kept in the space bound, is no longer than the time bound
  refine of_computesTidily (T := fun n =>
      c * (c₁ * (n + 1) ^ d₁ + c₂ * (n + 1) ^ d₂ + 1) +
      c * (c₁ * (n + 1) ^ d₁ + c₂ * (n + 1) ^ d₂ +
        c * (c₁ * (n + 1) ^ d₁ + c₂ * (n + 1) ^ d₂ + 1) + 1))
    (by fun_prop) h (fun a => ?_) (fun a => ?_)
  · exact Nat.le_add_right _ _
  · have hl := (h a).length_output_le
    beta_reduce at hl
    exact (Nat.mul_le_mul_left c (by omega)).trans (Nat.le_add_left _ _)

/-- **Case distinction** on a Boolean test computable in polynomial time, in any encoding of
`Bool`. -/
@[fun_prop]
theorem ite {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    (hc : ComputableInPolyTime c encIn encC) (hf : ComputableInPolyTime f encIn encMid)
    (hg : ComputableInPolyTime g encIn encMid) :
    ComputableInPolyTime (fun x => if c x then f x else g x) encIn encMid := by
  obtain ⟨c₀, d₀, k₀, S₀, _, tm₀, h₀⟩ := Internal.NormalForm.polyTime hc
  obtain ⟨c₁, d₁, k₁, S₁, _, tm₁, h₁⟩ := Internal.NormalForm.polyTime hf
  obtain ⟨c₂, d₂, k₂, S₂, _, tm₂, h₂⟩ := Internal.NormalForm.polyTime hg
  obtain ⟨k, K, S, _, tm, h⟩ := ComputableTidilyInTimeAndSpace.ite (encOut := encMid)
    (f := f) (g := g)
    (tc := fun a => c₀ * ((encIn a).length + 1) ^ d₀)
    (sc := fun a => c₀ * ((encIn a).length + 1) ^ d₀)
    (tf := fun a => c₁ * ((encIn a).length + 1) ^ d₁)
    (sf := fun a => c₁ * ((encIn a).length + 1) ^ d₁)
    (tg := fun a => c₂ * ((encIn a).length + 1) ^ d₂)
    (sg := fun a => c₂ * ((encIn a).length + 1) ^ d₂)
    ⟨k₀, S₀, inferInstance, tm₀, h₀⟩ ⟨k₁, S₁, inferInstance, tm₁, fun x => h₁ x.1⟩
    ⟨k₂, S₂, inferInstance, tm₂, fun x => h₂ x.1⟩
  refine of_computesTidily (T := fun n =>
      c₀ * (n + 1) ^ d₀ + (c₁ * (n + 1) ^ d₁ + c₂ * (n + 1) ^ d₂) + k)
    (by fun_prop) h (fun a => ?_) (fun a => ?_) <;>
  · split_ifs <;> omega

/-- **Left folds**, through the machine-level loop. Besides certificates for the list, the initial
value and the step, a polynomially bounded `L` must bound the length of the list, the encoded
arguments of every step and the encoded intermediate states. -/
theorem foldl {γ α β : Type u} {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encL : List α ↪ List Bool}
    {encBA : β × α ↪ List Bool} {encS : List α × β ↪ List Bool}
    {encO : Option (List α × β) ↪ List Bool}
    [ListEncoding encA encL] [PairEncoding encB encA encBA] [PairEncoding encL encB encS]
    [OptionEncoding encS encO] {list : γ → List α} {init : γ → β} {step : β → α → β}
    (hlist : ComputableInPolyTime list encIn encL) (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun p : β × α => step p.1 p.2) encBA encB)
    {L : ℕ → ℕ} (hL : PolynomiallyBounded L)
    (hlen : ∀ x, (list x).length ≤ L (encIn x).length)
    (harg : ∀ x i (hi : i < (list x).length),
      (encBA (((list x).take i).foldl step (init x), (list x)[i])).length ≤ L (encIn x).length)
    (hstate : ∀ x, ∀ i ≤ (list x).length,
      (encS ((list x).drop i, ((list x).take i).foldl step (init x))).length ≤
        L (encIn x).length) :
    ComputableInPolyTime (fun x => (list x).foldl step (init x)) encIn encB := by
  obtain ⟨c₁, d₁, k₁, S₁, _, tm₁, h₁⟩ := Internal.NormalForm.polyTime hlist
  obtain ⟨c₂, d₂, k₂, S₂, _, tm₂, h₂⟩ := Internal.NormalForm.polyTime hinit
  obtain ⟨c₃, d₃, k₃, S₃, _, tm₃, h₃⟩ := Internal.NormalForm.polyTime hstep
  -- the step on the arguments that occur, within the bound at the largest argument
  have hmax (x : γ) (i : ℕ) (hi : i < (list x).length) :
      c₃ * ((encBA (((list x).take i).foldl step (init x), (list x)[i])).length + 1) ^ d₃ ≤
        c₃ * (L (encIn x).length + 1) ^ d₃ :=
    Nat.mul_le_mul_left c₃ (Nat.pow_le_pow_left (Nat.add_le_add_right (harg x i hi) 1) d₃)
  obtain ⟨c, k, S, _, tm, h⟩ := ComputableTidilyInTimeAndSpace.foldl (encA := encA)
    (encL := encL) (encBA := encBA) (encS := encS) (encO := encO) (step := step)
    (t := fun x => c₁ * ((encIn x).length + 1) ^ d₁ + c₂ * ((encIn x).length + 1) ^ d₂)
    (s := fun x => c₁ * ((encIn x).length + 1) ^ d₁ + c₂ * ((encIn x).length + 1) ^ d₂)
    (tStep := fun p => c₃ * ((encBA p).length + 1) ^ d₃)
    (sStep := fun p => c₃ * ((encBA p).length + 1) ^ d₃)
    (tMax := fun x => c₃ * (L (encIn x).length + 1) ^ d₃)
    (sMax := fun x => c₃ * (L (encIn x).length + 1) ^ d₃)
    (lMax := fun x => L (encIn x).length)
    ⟨k₁, S₁, inferInstance, tm₁,
      fun x => (h₁ x).mono (Nat.le_add_right _ _) (Nat.le_add_right _ _)⟩
    ⟨k₂, S₂, inferInstance, tm₂,
      fun x => (h₂ x).mono (Nat.le_add_left _ _) (Nat.le_add_left _ _)⟩
    ⟨k₃, S₃, inferInstance, tm₃, h₃⟩ hmax hmax hstate
  refine of_computesTidily (T := fun n =>
      c * (c₁ * (n + 1) ^ d₁ + c₂ * (n + 1) ^ d₂ +
        (L n + 1) * (c₃ * (L n + 1) ^ d₃ + L n + 1)) +
      c * (c₁ * (n + 1) ^ d₁ + c₂ * (n + 1) ^ d₂ + c₃ * (L n + 1) ^ d₃ + L n + 1))
    (by fun_prop) h (fun x => ?_) (fun x => ?_)
  · have := Nat.mul_le_mul_right (c₃ * (L (encIn x).length + 1) ^ d₃ + L (encIn x).length + 1)
      (Nat.add_le_add_right (hlen x) 1)
    exact (Nat.mul_le_mul_left c (by omega)).trans (Nat.le_add_right _ _)
  · exact Nat.le_add_left _ _

/-- The first projection of an encoding of pairs, from its linear-time machine. -/
theorem _root_.Turing.MultiTapeTM.PairEncoding.computableInPolyTime_fst
    {β₁ β₂ : Type u} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {enc : β₁ × β₂ ↪ List Bool} [h : PairEncoding enc₁ enc₂ enc] :
    ComputableInPolyTime (fun p : β₁ × β₂ => p.1) enc enc₁ :=
  let ⟨c, _, _, _, _, htm⟩ := h.fst
  of_computesTidily (T := fun n => c * (n + 1)) (by fun_prop) htm (fun _ => le_rfl)
    (fun _ => le_rfl)

/-- The second projection of an encoding of pairs, from its linear-time machine. -/
theorem _root_.Turing.MultiTapeTM.PairEncoding.computableInPolyTime_snd
    {β₁ β₂ : Type u} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {enc : β₁ × β₂ ↪ List Bool} [h : PairEncoding enc₁ enc₂ enc] :
    ComputableInPolyTime (fun p : β₁ × β₂ => p.2) enc enc₂ :=
  let ⟨c, _, _, _, _, htm⟩ := h.snd
  of_computesTidily (T := fun n => c * (n + 1)) (by fun_prop) htm (fun _ => le_rfl)
    (fun _ => le_rfl)


/-- Project the first entry of an ordinary framed pair. -/
@[fun_prop]
theorem fst {α β : Type u} (encA : α ↪ List Bool) (encB : β ↪ List Bool) :
    ComputableInPolyTime (fun p : α × β => p.1) (encPair encA encB) encA :=
  PairEncoding.computableInPolyTime_fst (enc₁ := encA) (enc₂ := encB) (enc := encPair encA encB)

/-- Project the second entry of an ordinary framed pair. -/
@[fun_prop]
theorem snd {α β : Type u} (encA : α ↪ List Bool) (encB : β ↪ List Bool) :
    ComputableInPolyTime (fun p : α × β => p.2) (encPair encA encB) encB :=
  PairEncoding.computableInPolyTime_snd (enc₁ := encA) (enc₂ := encB) (enc := encPair encA encB)

/-- Reuse the same realizing machine for an equal encoded output. -/
theorem of_enc_eq {δ : Type*} {encD : δ ↪ List Bool} {f : α → β} {g : α → δ}
    (hf : ComputableInPolyTime f encIn encMid)
    (h : ∀ a, encD (g a) = encMid (f a)) : ComputableInPolyTime g encIn encD :=
  let ⟨t, s, ht, hs, k, State, hfinite, tm, htm⟩ := hf
  ⟨t, s, ht, hs, k, State, hfinite, tm, fun a => h a ▸ htm a⟩

/-- The complete encoded output is bounded by the actual time of its realizing machine. -/
theorem polyBounded_length {f : α → β} (hf : ComputableInPolyTime f encIn encMid) :
    PolyBounded (fun a => (encIn a).length) (fun a => (encMid (f a)).length) := by
  obtain ⟨c, d, _, _, _, _, h⟩ := Internal.NormalForm.polyTime hf
  exact PolyBounded.of_forall_le c d fun a => (h a).length_output_le

/-- Pair two computed outputs using the standard pair encoding. -/
@[fun_prop]
theorem prod {α β γ : Type u} {encIn : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {f : α → β} {g : α → γ}
    (hf : ComputableInPolyTime f encIn encB) (hg : ComputableInPolyTime g encIn encC) :
    ComputableInPolyTime (fun a => (f a, g a)) encIn (encPair encB encC) := pair hf hg

/-- Project the first entry after computing a pair; the pair fixes its encodings. -/
theorem fst' {α β γ : Type u} {encIn : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {f : α → β × γ}
    (hf : ComputableInPolyTime f encIn (encPair encB encC)) :
    ComputableInPolyTime (fun a => (f a).1) encIn encB := (fst encB encC).comp hf

/-- Project the second entry after computing a pair. -/
theorem snd' {α β γ : Type u} {encIn : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {f : α → β × γ}
    (hf : ComputableInPolyTime f encIn (encPair encB encC)) :
    ComputableInPolyTime (fun a => (f a).2) encIn encC := (snd encB encC).comp hf

/-- Boolean conjunction on its fixed finite input domain. -/
@[fun_prop]
theorem bool_and : ComputableInPolyTime (fun p : Bool × Bool => p.1 && p.2)
    (encPair encBool encBool) encBool := of_finite _

/-- Boolean negation on its fixed finite input domain. -/
@[fun_prop]
theorem bool_not : ComputableInPolyTime Bool.not encBool encBool := of_finite _

end Turing.MultiTapeTM.ComputableInPolyTime
