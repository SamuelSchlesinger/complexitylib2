/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Space
import Complexity.Computability.Machines.Turing.MultiTape.Machine.Space

/-! Polynomial-space classes and finite views of space-bounded nondeterministic machines:
inhabitants, a branch running forever, a stuck branch, repeated output and empty inputs. -/

namespace ComplexityTests.Space

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-! ### Inhabitants -/

example : (∅ : Set (List Bool)) ∈ PSPACE encBits :=
  P_subset_PSPACE ⟨fun _ => false, ComputableTidilyInPolyTime.const false, fun _ => by simp⟩

example : (Set.univ : Set (List Bool)) ∈ NPSPACE encBits :=
  PSPACE_subset_NPSPACE (P_subset_PSPACE
    ⟨fun _ => true, ComputableTidilyInPolyTime.const true, fun _ => by simp⟩)

/-! ### A branch running forever -/

/-- Halt with output `[true]`. -/
private def acceptAction : Action 0 Bool Bool :=
  { inputTape := 0, workTapes := Fin.elim0, output := some true, state := none }

/-- Stay in the initial state, emitting nothing. -/
private def loopAction : Action 0 Bool Bool :=
  { inputTape := 0, workTapes := Fin.elim0, output := none, state := some false }

/-- From its only running state, either accept or loop forever. -/
private def loopOrAccept : MultiTapeNTM 0 Bool Bool where
  q₀ := false
  Tr q _ _ action := q = false ∧ (action = acceptAction ∨ action = loopAction)

/-- A computation path of one step accepts. -/
private theorem accepts_loopOrAccept (input : List Bool) : loopOrAccept.Accepts input := by
  have hstep : loopOrAccept.Step (loopOrAccept.initCfg input)
      (acceptAction.apply (loopOrAccept.initCfg input)) := ⟨acceptAction, ⟨rfl, .inl rfl⟩, rfl⟩
  refine ⟨⟨(RelSeries.singleton _ _).cons (loopOrAccept.initCfg input) hstep, rfl⟩, ?_, ?_⟩ <;>
    simp [acceptAction]

/-- No time bound is needed: the looping branch never halts, yet the problem is in `NPSPACE`. -/
example : (Set.univ : Set (List Bool)) ∈ NPSPACE encBits :=
  ⟨0, Bool, inferInstance, loopOrAccept, fun _ => 0, .const 0,
    fun a => ⟨MultiTapeNTM.runsInSpace_zero_tapes _ _ _, by simpa using accepts_loopOrAccept a⟩⟩

/-- The looping branch stays at the initial configuration. -/
private theorem step_loop (input : List Bool) :
    loopOrAccept.Step (loopOrAccept.initCfg input) (loopOrAccept.initCfg input) := by
  refine ⟨loopAction, ⟨rfl, .inr rfl⟩, ?_⟩
  apply Cfg.ext_zero_tapes <;> simp [loopAction, Action.apply, loopOrAccept]

/-- Run paths of every length stay at the initial configuration. -/
private theorem exists_loop_path (input : List Bool) (n : ℕ) :
    ∃ p : loopOrAccept.RunPath input, p.head = loopOrAccept.initCfg input ∧ p.length = n ∧
      p.last = loopOrAccept.initCfg input := by
  induction n with
  | zero => exact ⟨RelSeries.singleton _ _, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨p, hhead, hlen, hlast⟩ := ih
    have hstep : loopOrAccept.Step p.last (loopOrAccept.initCfg input) :=
      hlast ▸ step_loop input
    exact ⟨p.snoc _ hstep, by simpa using hhead, by simp [hlen], by simp⟩

/-- The looping branch has computation paths of every length that have not halted. -/
example (input : List Bool) (n : ℕ) : ∃ p : loopOrAccept.ComputationPath input,
    p.time = n ∧ ¬p.last.Halted := by
  obtain ⟨p, hhead, hlen, hlast⟩ := exists_loop_path input n
  refine ⟨⟨p, hhead⟩, hlen, ?_⟩
  change ¬(RelSeries.last p).Halted
  rw [hlast]
  simp [loopOrAccept]

/-! ### Views -/

/-- Repeated output is not acceptance: `[true, true]` is summarized as `[false]`. -/
example : outputClass [true, true] = [false] := rfl

example : outputClass [true] = [true] := rfl

example : outputClass [false] = [false] := rfl

/-- Acceptance of the looping machine is witnessed by a reachable halted view with output
`[true]`, on the empty input. -/
example : ∃ finite, Relation.ReflTransGen loopOrAccept.ViewStep (loopOrAccept.initView [])
    finite ∧ finite.state = none ∧ finite.output = [true] :=
  MultiTapeNTM.accepts_iff_reflTransGen_viewStep.mp (accepts_loopOrAccept [])

/-! ### Axioms -/

/--
info: 'Cslib.Complexity.PSPACE_subset_NPSPACE' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PSPACE_subset_NPSPACE

/--
info: 'Turing.MultiTapeNTM.accepts_iff_reflTransGen_viewStep' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeNTM.accepts_iff_reflTransGen_viewStep

/--
info: 'Turing.MultiTapeNTM.length_encFiniteCfg_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeNTM.length_encFiniteCfg_le

/--
info: 'Turing.MultiTapeNTM.RunPath.natAbs_lt_spaceUsedByTape' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeNTM.RunPath.natAbs_lt_spaceUsedByTape

end ComplexityTests.Space
