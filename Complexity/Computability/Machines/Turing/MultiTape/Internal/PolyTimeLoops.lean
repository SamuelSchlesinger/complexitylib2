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

end ComputableInPolyTime
end Turing.MultiTapeTM
