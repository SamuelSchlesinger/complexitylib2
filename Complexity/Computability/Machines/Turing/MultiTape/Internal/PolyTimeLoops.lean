/-
Copyright (c) 2026 Erik Demaine, Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (direct-calculus integration checkpoint)

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PlainDirect.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option

/-!
# Direct plain folds with reachable-prefix bounds

Derived from the machine-level plain fold of the credited #869 prototype. The accumulator is
bounded only on reachable prefixes; no bound on arbitrary unreachable states is assumed.
The temporary prototype import is replaced by the canonical direct core at integration.
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Cslib

private theorem outputLengthLe {k : ℕ} {State : Type} (tm : MultiTapeTM k Bool State)
    {input output : List Bool} {t s : ℕ}
    (h : tm.ComputesInTimeAndSpace input output t s) : output.length ≤ t := by
  obtain ⟨⟨u, hu, rfl⟩, ht, -⟩ := h
  have ht := runsInTime_iff_halted.mp ht
  have heq : tm.runFrom (tm.initCfg input) u = tm.runFrom (tm.initCfg input) t := by
    rcases le_total u t with hut | htu
    · exact (runFrom_eq_of_halt tm _ hut hu).symm
    · exact runFrom_eq_of_halt tm _ htu ht
  rw [heq]
  simpa using tm.length_output_runFrom_le (tm.initCfg input) t

private theorem encodedLengthBound {α β : Type*} {input : α ↪ List Bool}
    {output : β ↪ List Bool} {f : α → β} (h : ComputableInPolyTime f input output) :
    ∃ c d : ℕ, ∀ a, (output (f a)).length ≤ c * ((input a).length + 1) ^ d := by
  obtain ⟨t, s, ht, _, k, State, _, tm, htm⟩ := h
  obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.mp ht
  exact ⟨c, d, fun a => (outputLengthLe tm (htm a)).trans (hcd _)⟩

private theorem foldlCapture {π β α : Type} (par : π) (step : π → β → α → β)
    (list : List α) (init : β) :
    list.foldl (fun state value => (state.1, step state.1 state.2 value)) (par, init) =
      (par, list.foldl (step par) init) := by
  induction list generalizing init with
  | nil => rfl
  | cons a list ih =>
    simp only [List.foldl_cons]
    exact ih (step par init a)

namespace ComputableInPolyTime

/-- A polynomial bound on the encoded accumulators of reachable prefixes suffices for a
uniform polynomial-time fold. The list and callback encodings are preserved. -/
theorem foldl' {γ α β : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {encL : List α ↪ List Bool}
    [ListEncoding encA encL] [hS : SizedListEncoding encA encL]
    {list : γ → List α} {init : γ → β} {step : β → α → β}
    (hlist : ComputableInPolyTime list encIn encL)
    (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun p : β × α => step p.1 p.2)
      (encPair encB encA) encB)
    {B : γ → ℕ}
    (hB : ∃ c d : ℕ, ∀ x, B x ≤ c * ((encIn x).length + 1) ^ d)
    (hstates : ∀ x, ∀ i ≤ (list x).length,
      (encB (((list x).take i).foldl step (init x))).length ≤ B x) :
    ComputableInPolyTime (fun x => (list x).foldl step (init x)) encIn encB := by
  obtain ⟨cL, dL, hL⟩ := encodedLengthBound hlist
  obtain ⟨cB, dB, hB⟩ := hB
  let A := fun n : ℕ => cL * (n + 1) ^ dL
  let D := fun n : ℕ => cB * (n + 1) ^ dB
  let P := fun n => 3 * A n + 3 * D n + 3
  have hP : PolynomiallyBounded P := by dsimp [P, A, D]; fun_prop
  apply PlainDirect.foldl (encA := encA) (encB := encB) (encL := encL)
    (list := list) (init := init) (step := step) (encBA := encPair encB encA)
    (encS := encPair encL encB) (encO := encOption (encPair encL encB))
    hlist hinit hstep hP
  · intro x
    exact (hS.length_le _).trans ((hL x).trans (by dsimp [P, A, D]; omega))
  · intro x i hi
    have hs := (hstates x i hi.le).trans (hB x)
    have ha := (hS.length_elem_le (list x) _ (List.getElem_mem hi)).trans (hL x)
    simp only [length_encPair]
    dsimp [P, A, D]
    omega
  · intro x i hi
    have hs := (hstates x i hi).trans (hB x)
    have hl := (hS.length_drop_le (list x) i).trans (hL x)
    simp only [length_encPair]
    dsimp [P, A, D]
    omega

/-- A captured parameter is computed uniformly, retained through every step, and bounded
separately from the accumulator. Only reachable prefix states need the supplied bound. -/
theorem foldlWith {γ α β π : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {encL : List α ↪ List Bool} {encP : π ↪ List Bool}
    [ListEncoding encA encL] [SizedListEncoding encA encL]
    {par : γ → π} {list : γ → List α} {init : γ → β} {step : π → β → α → β}
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn encL)
    (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun p : (π × β) × α => step p.1.1 p.1.2 p.2)
      (encPair (encPair encP encB) encA) encB)
    {B : γ → ℕ}
    (hB : ∃ c d : ℕ, ∀ x, B x ≤ c * ((encIn x).length + 1) ^ d)
    (hstates : ∀ x, ∀ i ≤ (list x).length,
      (encB (((list x).take i).foldl (step (par x)) (init x))).length ≤ B x) :
    ComputableInPolyTime (fun x => (list x).foldl (step (par x)) (init x)) encIn encB := by
  have houter : ComputableInPolyTime (fun q : (π × β) × α => q.1)
      (encPair (encPair encP encB) encA) (encPair encP encB) :=
    PlainDirect.fst (enc₁ := encPair encP encB) (enc₂ := encA)
  have hfirst : ComputableInPolyTime (fun p : π × β => p.1) (encPair encP encB) encP :=
    PlainDirect.fst (enc₁ := encP) (enc₂ := encB)
  have hstart : ComputableInPolyTime (fun x => (par x, init x)) encIn (encPair encP encB) :=
    PlainDirect.pair (enc₁ := encP) (enc₂ := encB) hpar hinit
  have hjoint : ComputableInPolyTime
      (fun q : (π × β) × α => (q.1.1, step q.1.1 q.1.2 q.2))
      (encPair (encPair encP encB) encA) (encPair encP encB) :=
    PlainDirect.pair (enc₁ := encP) (enc₂ := encB)
      (PlainDirect.comp hfirst houter) hstep
  obtain ⟨cP, dP, hP⟩ := encodedLengthBound hpar
  obtain ⟨cB, dB, hB⟩ := hB
  let C := fun x => 2 * (encP (par x)).length + 1 + B x
  let P := fun n : ℕ => 2 * (cP * (n + 1) ^ dP) + 1 + cB * (n + 1) ^ dB
  have hp : PolynomiallyBounded P := by dsimp [P]; fun_prop
  obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.mp hp
  have hC : ∀ x, C x ≤ c * ((encIn x).length + 1) ^ d := by
    intro x
    apply le_trans (b := P (encIn x).length) _ (hcd _)
    dsimp [C, P]
    have := hP x
    have := hB x
    omega
  have hfold := foldl' (encA := encA) (encB := encPair encP encB)
    (list := list) (init := fun x => (par x, init x))
    (step := fun state value => (state.1, step state.1 state.2 value))
    hlist hstart hjoint (B := C) ⟨c, d, hC⟩ (by
      intro x i hi
      simp only [foldlCapture, length_encPair]
      dsimp [C]
      exact Nat.add_le_add_left (hstates x i hi) _)
  have hsecond : ComputableInPolyTime (fun p : π × β => p.2) (encPair encP encB) encB :=
    PlainDirect.snd (enc₁ := encP) (enc₂ := encB)
  simpa only [foldlCapture] using PlainDirect.comp hsecond hfold

end ComputableInPolyTime
end Turing.MultiTapeTM
