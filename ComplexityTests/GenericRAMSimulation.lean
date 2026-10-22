/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.GenericRAM.Simulation.Finite
public import Complexity.Computability.GenericRAM.Native.Nat
import Mathlib.Data.Fin.VecNotation

/-!
# Finite RAM simulation checks

A fixed store/load/branch/halt client runs at several configurations. Separate examples exercise
current and continuing labels, missing instructions, failed addresses, invalid moved values,
failed tests versus false tests, and the distinction between produced and moved values.
-/

@[expose] public section

namespace ComplexityTests.GenericRAMSimulation

open Cslib.GenericRAM
open BoundedNat

private def initial (a v default : ℕ) : FiniteState model 2 :=
  ⟨0, ![a, v], default, ∅⟩

private def client : Program model 2 :=
  [.op (.store 0 1), .op (.load 1 0), .branch (.test () ![0, 1]) 3, .halt 1]

-- No eager fault for invalid registers unrelated to an instruction.
example : FiniteState.step (M := model) 8 [.jump 1] (initial 99 99 99) =
    some (.inl { initial 99 99 99 with pc := 1 }) := rfl

-- The same fixed client accepts two configurations; its memory operations are real sparse writes.
example (k : ℕ) (hk : 4 ≤ k) :
    FiniteState.step (M := model) k client (initial 0 3 0) =
      some (.inl { (initial 0 3 0).write 0 3 with pc := 1 }) := by
  have h0 : 0 < k := by omega
  have h1 : 1 < k := by omega
  have h3 : 3 < k := by omega
  simp [FiniteState.step, FiniteState.dispatch, FiniteState.evalInstr, FiniteState.evalOp,
    FiniteState.resume, client, initial, model, h0, h1, h3]

private def stored : FiniteState model 2 := { (initial 0 3 0).write 0 3 with pc := 1 }
private def loaded : FiniteState model 2 := { (stored.set 1 0).set 1 3 with pc := 2 }
private def halting : FiniteState model 2 := { loaded with pc := 3 }

example : FiniteState.step (M := model) 4 client (stored.set 1 0) = some (.inl loaded) := rfl
example : FiniteState.step (M := model) 8 client (stored.set 1 0) = some (.inl loaded) := rfl
example : FiniteState.step (M := model) 4 client loaded = some (.inl halting) := rfl
example : FiniteState.step (M := model) 8 client halting = some (.inr 3) := rfl

-- A valid jump beyond the program faults on the next fetch, not on the jump.
example : FiniteState.step (M := model) 8 [.jump 5] (initial 0 0 0) =
    some (.inl { initial 0 0 0 with pc := 5 }) := rfl
example : FiniteState.step (M := model) 8 [.jump 5] { initial 0 0 0 with pc := 5 } = none := rfl
-- An invalid current or continuing label faults immediately.
example : FiniteState.step (M := model) 0 [.halt 0] (initial 0 0 0) = none := rfl
example : FiniteState.step (M := model) 4 [.jump 4] (initial 0 0 0) = none := rfl
example : FiniteState.step (M := model) 1 [.op (.copy 0 0)] (initial 0 0 0) = none := rfl
-- Halt does not validate a successor label.
example : FiniteState.step (M := model) 1 [.halt 0] (initial 0 0 0) = some (.inr 0) := rfl

-- Address extraction and loaded/source value validation are independent failure paths.
example : FiniteState.step (M := model) 4 [.op (.load 1 0)] (initial 4 0 0) = none := rfl
example : FiniteState.step (M := model) 4 [.op (.load 1 0)] (initial 0 0 4) = none := rfl
example : FiniteState.step (M := model) 4 [.op (.store 0 1)] (initial 4 0 0) = none := rfl
example : FiniteState.step (M := model) 4 [.op (.store 0 1)] (initial 0 4 0) = none := rfl
example : FiniteState.step (M := model) 4 [.op (.copy 0 1)] (initial 0 4 0) = none := rfl
example : FiniteState.step (M := model) 4 [.halt 1] (initial 0 4 0) = none := rfl
example : FiniteState.step (M := model) 4 [.op (.const 1 4)] (initial 0 0 0) = none := rfl
example : FiniteState.step (M := model) 4 [.op (.alu () 1 ![0, 1])] (initial 2 2 0) = none := rfl

-- False advances; a failed test faults. These cannot share a Boolean-only handler.
example : FiniteState.step (M := model) 4 [.branch (.test () ![0, 1]) 0] (initial 0 1 0) =
    some (.inl (initial 0 1 0)) := rfl
example : FiniteState.step (M := model) 4 [.branch (.test () ![0, 1]) 0] (initial 2 1 0) =
    some (.inl { initial 2 1 0 with pc := 1 }) := rfl
example : FiniteState.step (M := model) 4 [.branch (.test () ![0, 1]) 0]
    (initial 0 4 0) = none := rfl

-- A model may distinguish admissible produced values from legal moves.
/-- A model where produced values can be admissible although all moves fail. -/
abbrev rejectMoves : Model := { model with validMove := fun _ _ => false }
private def noMoves : FiniteState rejectMoves 1 := ⟨0, ![0], 0, ∅⟩
example : FiniteState.step (M := rejectMoves) 4 [.op (.const 0 2)] noMoves =
    some (.inl { noMoves.set 0 2 with pc := 1 }) := rfl
example : FiniteState.step (M := rejectMoves) 4 [.op (.copy 0 0)] noMoves = none := rfl

-- Empty register tuples are permitted when no instruction needs a register.
example : FiniteState.step (M := model) 4 ([.jump 0] : Program model 0) ⟨0, Fin.elim0, 0, ∅⟩ =
    some (.inl ⟨0, Fin.elim0, 0, ∅⟩) := rfl

-- Functional memory has redundant sparse representations; encodings must use the finite state.
example : (initial 0 0 0).denote = ((initial 0 0 0).write 7 0).denote := by
  rw [FiniteState.denote_write]
  ext a <;> simp [FiniteState.denote, initial, Data.write]

/-- The simulation covers every bounded-natural finite state, including invalid inputs. -/
theorem all_states (k : ℕ) (p : Program model 2) (s : FiniteState model 2) :
    FiniteState.denoteResult (FiniteState.step (M := model) k p s) = step k p s.denote :=
  FiniteState.denote_step k p s

/--
info: 'Cslib.GenericRAM.FiniteState.denote_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiniteState.denote_step

end ComplexityTests.GenericRAMSimulation
