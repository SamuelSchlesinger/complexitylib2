/-
Copyright (c) 2026 Erik Demaine, Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops

/-!
# Direct plain list primitives

Finite-state word transducers implement unary successor and append a framed element to a list.
Their machine clocks are linear and use no work tapes. The proofs do not invoke a tidy
computability calculus.
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Cslib

private theorem ofTransducer {Q : Type} [Finite Q] (τ : Transducer Bool Q)
    {α β : Type*} {input : α ↪ List Bool} {output : β ↪ List Bool} {f : α → β}
    (hf : ∀ a, output (f a) = τ.run τ.q₀ (input a)) :
    ComputableInPolyTime f input output := by
  refine ⟨fun n => 2 * n + 3, fun _ => 0, by fun_prop, by fun_prop,
    0, _, inferInstance, τ.toTM, fun a => ?_⟩
  rw [hf a]
  exact τ.computesInTimeAndSpace_toTM (input a)

private def unarySuccTransducer : Transducer Bool Bool where
  q₀ := true
  step q bit := (false, if q then [true, bit] else [bit])
  final q := if q then [true] else []
  length_step_le q bit := by cases q <;> simp
  length_final_le q := by cases q <;> simp

private theorem unarySuccRun (word : List Bool) :
    unarySuccTransducer.run true word = true :: word ∧
      unarySuccTransducer.run false word = word := by
  induction word with
  | nil => constructor <;> rfl
  | cons bit word ih =>
    constructor
    · change [true, bit] ++ unarySuccTransducer.run false word = true :: bit :: word
      rw [ih.2]
      rfl
    · change [bit] ++ unarySuccTransducer.run false word = bit :: word
      rw [ih.2]
      rfl

private def snocTransducer : Transducer Bool (Option Bool) where
  q₀ := none
  step
    | none, true => (some false, [])
    | none, false => (some true, [])
    | some false, bit => (none, [bit])
    | some true, bit => (some true, [true, bit])
  final _ := [false]
  length_step_le q bit := by
    cases q with
    | none => cases bit <;> simp
    | some q => cases q <;> simp
  length_final_le _ := by decide

private theorem snocRunTail (word : List Bool) :
    snocTransducer.run (some true) word = frame word := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
    change [true, bit] ++ snocTransducer.run (some true) word = true :: bit :: frame word
    rw [ih]
    rfl

private theorem snocRun (left right : List Bool) :
    snocTransducer.run none (frame left ++ right) = left ++ frame right := by
  induction left with
  | nil =>
    change snocTransducer.run (some true) right = frame right
    exact snocRunTail right
  | cons bit left ih =>
    change [bit] ++ snocTransducer.run none (frame left ++ right) =
      (bit :: left) ++ frame right
    rw [ih]
    rfl

namespace ComputableInPolyTime

/-- Unary successor is a direct finite-state transduction, including the empty word for zero. -/
@[fun_prop]
theorem unary_succ : ComputableInPolyTime (· + 1) encUnary encUnary := by
  apply ofTransducer unarySuccTransducer
  intro n
  change List.replicate (n + 1) true =
    unarySuccTransducer.run true (List.replicate n true)
  rw [(unarySuccRun _).1]
  simp only [List.replicate_succ]

/-- Append one element to a framed list, for an arbitrary fixed element encoding. -/
@[fun_prop]
theorem snoc {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : List α × α => p.1 ++ [p.2])
      (encPair (encList enc) enc) (encList enc) := by
  apply ofTransducer snocTransducer
  intro p
  change encList enc (p.1 ++ [p.2]) =
    snocTransducer.run none (frame (encList enc p.1) ++ enc p.2)
  rw [snocRun]
  change ((p.1 ++ [p.2]).flatMap (frame ∘ enc)) =
    p.1.flatMap (frame ∘ enc) ++ frame (enc p.2)
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    Function.comp_apply, List.append_nil]

end ComputableInPolyTime
end Turing.MultiTapeTM
