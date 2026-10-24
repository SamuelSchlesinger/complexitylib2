/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (spike for #862, not for merge)

public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Foldl
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm

/-!
# Plain polynomial time without a tidy calculus (spike)

The closure rules of `Turing.MultiTapeTM.ComputableInPolyTime`, proved directly from plain
hypotheses. No tidy asymptotic predicate (`ComputableTidilyInPolyTime` and its relatives) is
imported or used: each proof unpacks the plain machines, makes them tidy with the tidy normal form
(`Turing.MultiTapeTM.ComputesInTimeAndSpace.computesTidily_tidy`), combines the tidy machines with
the existing machine combinators, and concludes plain computability from the combined machine
(`Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.computesInTimeAndSpace`).

Composition is entirely machine-level (`Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.comp`).
Pairing, case distinctions and left folds call the explicit-bound combinators
`Turing.MultiTapeTM.PairEncoding.pair_mono`,
`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.ite` and
`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl`, whose arguments are tidy machines with
explicit bounds; the proofs pass them anonymous constructors and never name a tidy predicate.

Two private helpers are the only interface between the plain and the tidy worlds:
`exists_computesTidily` (a plain polynomial-time certificate gives a tidy machine within one bound
`c (n + 1) ^ d`) and `of_computesTidily` (a tidy machine within polynomially bounded resources gives
a plain certificate). No public statement of this module mentions tidiness.

## Main results

* `Turing.MultiTapeTM.PlainDirect.comp`, `.pair`, `.ite`, `.foldl`: closure rules.
* `Turing.MultiTapeTM.PlainDirect.fst`, `.snd`: projections of `Turing.MultiTapeTM.PairEncoding`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.PlainDirect

open Cslib

universe u

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-! ### Tidy machines inside proofs -/

/-- A plain polynomial-time certificate gives a tidy machine within the single bound
`c (n + 1) ^ d` on time and space, where `n` is the length of the encoded input. The tidy normal
form costs `2 t + 3 s + O(1)` steps and `O(s + 1)` cells. -/
private theorem exists_computesTidily {f : α → β} (h : ComputableInPolyTime f encIn encMid) :
    ∃ c d : ℕ, ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
      ∀ a, tm.ComputesTidilyInTimeAndSpace (encIn a) (encMid (f a))
        (c * ((encIn a).length + 1) ^ d) (c * ((encIn a).length + 1) ^ d) := by
  obtain ⟨t, s, ht, hs, k, State, hfin, tm, htm⟩ := h
  have hp : PolynomiallyBounded fun n => (2 * t n + 3 * s n + 2 * k + 4) +
      (2 * s n + 2 * k * (3 * s n + 2 * k + 3)) := by fun_prop
  obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.mp hp
  refine ⟨c, d, k + k, _, inferInstance, tidy false true tm, fun a => ?_⟩
  have hb := hcd (encIn a).length
  exact ((htm a).computesTidily_tidy Bool.false_ne_true).mono
    ((Nat.le_add_right _ _).trans hb) ((Nat.le_add_left _ _).trans hb)

/-- A tidy machine within resources bounded by a polynomially bounded function of the length of
the encoded input certifies plain polynomial time. -/
private theorem of_computesTidily {f : α → β} {k : ℕ} {State : Type} [Finite State]
    {tm : MultiTapeTM k Bool State} {t s : α → ℕ} {T : ℕ → ℕ} (hT : PolynomiallyBounded T)
    (h : ∀ a, tm.ComputesTidilyInTimeAndSpace (encIn a) (encMid (f a)) (t a) (s a))
    (ht : ∀ a, t a ≤ T (encIn a).length) (hs : ∀ a, s a ≤ T (encIn a).length) :
    ComputableInPolyTime f encIn encMid :=
  ⟨T, T, hT, hT, k, State, inferInstance, tm,
    fun a => ((h a).mono (ht a) (hs a)).computesInTimeAndSpace⟩

/-! ### Closure rules -/

/-- **Composition**, through the machine-level composition of tidy machines. The intermediate word
is no longer than the time of the inner machine. -/
theorem comp {f : β → γ} {g : α → β} (hf : ComputableInPolyTime f encMid encOut)
    (hg : ComputableInPolyTime g encIn encMid) :
    ComputableInPolyTime (fun a => f (g a)) encIn encOut := by
  obtain ⟨c₁, d₁, k₁, S₁, _, tm₁, h₁⟩ := exists_computesTidily hg
  obtain ⟨c₂, d₂, k₂, S₂, _, tm₂, h₂⟩ := exists_computesTidily hf
  refine of_computesTidily (tm := tm₂.comp tm₁ true)
    (T := fun n => 6 * (c₁ * (n + 1) ^ d₁) + c₂ * (c₁ * (n + 1) ^ d₁ + 1) ^ d₂ +
      (6 * max k₁ k₂ + 20)) (by fun_prop) (fun a => (h₁ a).comp (h₂ (g a)) true)
    (fun a => ?_) (fun a => ?_) <;>
  · have hl := (h₁ a).length_output_le
    have := Nat.mul_le_mul_left c₂ (Nat.pow_le_pow_left (Nat.add_le_add_right hl 1) d₂)
    omega

/-- **Pairing**, for any encoding of pairs, through its pairing combinator. -/
theorem pair {α β₁ β₂ : Type u} {encIn : α ↪ List Bool} {enc₁ : β₁ ↪ List Bool}
    {enc₂ : β₂ ↪ List Bool} {enc : β₁ × β₂ ↪ List Bool} [PairEncoding enc₁ enc₂ enc]
    {f : α → β₁} {g : α → β₂} (hf : ComputableInPolyTime f encIn enc₁)
    (hg : ComputableInPolyTime g encIn enc₂) :
    ComputableInPolyTime (fun x => (f x, g x)) encIn enc := by
  obtain ⟨c₁, d₁, k₁, S₁, _, tm₁, h₁⟩ := exists_computesTidily hf
  obtain ⟨c₂, d₂, k₂, S₂, _, tm₂, h₂⟩ := exists_computesTidily hg
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
theorem ite {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    (hc : ComputableInPolyTime c encIn encC) (hf : ComputableInPolyTime f encIn encMid)
    (hg : ComputableInPolyTime g encIn encMid) :
    ComputableInPolyTime (fun x => if c x then f x else g x) encIn encMid := by
  obtain ⟨c₀, d₀, k₀, S₀, _, tm₀, h₀⟩ := exists_computesTidily hc
  obtain ⟨c₁, d₁, k₁, S₁, _, tm₁, h₁⟩ := exists_computesTidily hf
  obtain ⟨c₂, d₂, k₂, S₂, _, tm₂, h₂⟩ := exists_computesTidily hg
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
  obtain ⟨c₁, d₁, k₁, S₁, _, tm₁, h₁⟩ := exists_computesTidily hlist
  obtain ⟨c₂, d₂, k₂, S₂, _, tm₂, h₂⟩ := exists_computesTidily hinit
  obtain ⟨c₃, d₃, k₃, S₃, _, tm₃, h₃⟩ := exists_computesTidily hstep
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

/-! ### Projections -/

/-- The first projection of an encoding of pairs, from its linear-time machine. -/
theorem fst {β₁ β₂ : Type u} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {enc : β₁ × β₂ ↪ List Bool} [h : PairEncoding enc₁ enc₂ enc] :
    ComputableInPolyTime (fun p : β₁ × β₂ => p.1) enc enc₁ :=
  let ⟨c, _, _, _, _, htm⟩ := h.fst
  of_computesTidily (T := fun n => c * (n + 1)) (by fun_prop) htm (fun _ => le_rfl)
    (fun _ => le_rfl)

/-- The second projection of an encoding of pairs, from its linear-time machine. -/
theorem snd {β₁ β₂ : Type u} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {enc : β₁ × β₂ ↪ List Bool} [h : PairEncoding enc₁ enc₂ enc] :
    ComputableInPolyTime (fun p : β₁ × β₂ => p.2) enc enc₂ :=
  let ⟨c, _, _, _, _, htm⟩ := h.snd
  of_computesTidily (T := fun n => c * (n + 1)) (by fun_prop) htm (fun _ => le_rfl)
    (fun _ => le_rfl)

end Turing.MultiTapeTM.PlainDirect
