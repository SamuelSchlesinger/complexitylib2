/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Encodings.StepMachineComp
import Complexity.Computability.Complexity.Problems.CircuitValue.Writer

/-! A finite-state emitter has constant workspace and unbounded output, including empty input. -/

open Turing Turing.MultiTapeTM

namespace ComplexityTests.StepMachineResourceCertificate

/-- Copy the input in one rightward pass, and stop at its final blank. -/
def emitter : StepMachine Bool Bool Bool where
  init := false
  halt := id
  step _ a := match a with
    | none => (true, 0, [])
    | some b => (false, 1, [b])

theorem certificate : emitter.ResourceCertificate encBool (fun _ => 1) (fun _ => 1) where
  computable_halt := by
    simpa only [emitter, encBool_apply, List.length_singleton] using
      (ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool) id).inO_one
  computable_step := by
    apply ((ComputableInDegree.of_finite
      (encIn := encPair encBool (encOption encBool))
      (encMid := encPair encBool (encPair encMove encBits))
      (fun p : Bool × Option Bool => emitter.step p.1 p.2)).inO_one).mono 10
    all_goals
      intro p
      rcases p with ⟨_ | _, _ | _ | _⟩ <;>
        simp [encPair_apply, encOption, encBool_apply]

theorem prefix_run (word : List Bool) (i : ℕ) (hi : i ≤ word.length) :
    (emitter.run word i).state = false ∧ (emitter.run word i).pos.val = i + 1 ∧
      (emitter.run word i).out = word.take i := by
  induction i with
  | zero => simp [StepMachine.run, StepMachine.initCfg, emitter]
  | succ i ih =>
    obtain ⟨hs, hp, ho⟩ := ih (by omega)
    have hi' : i < word.length := by omega
    have hsym : inputSymbolAt word (emitter.run word i).pos = some word[i] := by
      simp [inputSymbolAt, hp, List.getElem?_eq_getElem hi']
    rw [emitter.run_succ_of_not_halt (by simpa [emitter] using hs)]
    simp only [StepMachine.stepAt]
    rw [hsym]
    change false = false ∧
      (moveInputPos (emitter.run word i).pos (1 : SignType)).val = i + 1 + 1 ∧
      (emitter.run word i).out ++ [word[i]] = word.take (i + 1)
    simp only [val_moveInputPos_pos, hp, ho]
    refine ⟨True.intro, by omega, ?_⟩
    exact (List.take_succ_eq_append_getElem hi').symm

theorem finish (word : List Bool) :
    (emitter.run word (word.length + 1)).state = true ∧
      (emitter.run word (word.length + 1)).out = word := by
  obtain ⟨hs, hp, ho⟩ := prefix_run word word.length le_rfl
  have hsym : inputSymbolAt word (emitter.run word word.length).pos = none := by
    simp [inputSymbolAt, hp]
  rw [emitter.run_succ_of_not_halt (by simpa [emitter] using hs)]
  simp only [StepMachine.stepAt]
  rw [hsym]
  change true = true ∧ (emitter.run word word.length).out ++ [] = word
  simp [ho]

theorem halts (word : List Bool) : emitter.HaltsAt word (word.length + 1) := by
  refine ⟨(finish word).1, fun i hi => ?_⟩
  simpa [emitter] using (prefix_run word i (by omega)).1

example : ComputableInBigO (id : List Bool → List Bool) encBits encBits
    List.length (fun _ => 1) := by
  have h := certificate.computableInBigO (encIn := encBits) (encOut := encBits)
    (id : List Bool → List Bool) (fun w => w.length + 1) halts
    (fun w => (finish w).2.symm)
    (tMax := fun _ => 1) (sMax := fun _ => 1) (by intros; exact ⟨le_rfl, le_rfl⟩)
  exact h.weaken (.of_le_linear 4 6 (by intro w; simp only [encBits_apply]; omega)) (.refl _)

-- Charging the entire emitted word to that same constant workspace would be false.
example : ¬ ComputableInO (id : List Bool → List Bool) encBits encBits
    List.length (fun _ => 1) := by
  rintro ⟨c, _, hlen⟩
  have h := hlen (List.replicate (2 * c + 1) false)
  simp only [id_eq, encBits_apply, List.length_replicate, Nat.one_add] at h
  omega

example (word : List Bool) : (emitter.comp emitter).Computes word word :=
  StepMachine.Computes.comp emitter emitter word
    ⟨_, halts word, (finish word).2⟩ ⟨_, halts word, (finish word).2⟩

example : (emitter.comp emitter).ResourceCertificate (StepMachine.encCompState encBool encBool)
    (StepMachine.compTime encBool encBool (fun _ => 1) (fun _ => 1) (fun _ => 1))
    (StepMachine.compSpace encBool encBool (fun _ => 1) (fun _ => 1)) :=
  certificate.comp certificate

-- A fixed halted initial state exercises the zero-round and zero-workspace initializer path.
example : ∃ t, ComputableInBigO (fun _ : List Bool => ([] : List Bool)) encBits encBits t
    (fun _ => 1) := by
  refine ⟨_, certificate.computableInBigO_of_init (encIn := encBits) (encOut := encBits)
    (constZero true) (fun _ => []) (fun _ => 0)
    (tMax := fun _ => 1) (sMax := fun _ => 1) ?_ ?_ ?_⟩
  · intro w
    simp [StepMachine.HaltsAt, StepMachine.run, StepMachine.initCfg, StepMachine.withInit,
      emitter]
  · intro w
    rfl
  · intros
    exact ⟨le_rfl, le_rfl⟩

/-- An actual writer schema with no chunks that copies its complete framed input. -/
def writer : Cslib.Complexity.CircuitValue.WriterSpec where
  countUnit := []
  countEnd := []
  numChunks _ := 0
  chunk _ _ := []
  trailer _ := []
  copyBit b := [b]

example (word : List Bool) :
    writer.machine.run (frame word) (writer.rounds word.length) = ⟨(3, word.length, 0), word⟩ := by
  simpa [writer, Cslib.Complexity.CircuitValue.WriterSpec.output] using writer.run_machine word

example : ComputableInLogSpace (id : List Bool → List Bool) (encFramed encBits) encBits := by
  have hin : (fun p => (Cslib.Complexity.CircuitValue.WriterSpec.encStepIn p).length) ≼
      fun p => Cslib.Complexity.CircuitValue.wBudget p.1 :=
    .of_le_linear 2 0 (by
      intro p
      simp only [Cslib.Complexity.CircuitValue.WriterSpec.encStepIn,
        Cslib.Complexity.CircuitValue.wBudget, length_encPair, encBool_apply,
        List.length_singleton]
      omega)
  apply writer.computableInLogSpace
  · intro w
    simp [writer, Cslib.Complexity.CircuitValue.WriterSpec.output, encBits]
  · exact ComputableInSpace.budget_const 0 hin
  · exact ComputableInSpace.budget_const [] hin
  · exact ComputableInSpace.budget_const [] hin
  · exact Cslib.PolynomiallyBounded.const 0

/--
info: 'Turing.StepMachine.ResourceCertificate.computableInBigO' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.StepMachine.ResourceCertificate.computableInBigO

/--
info: 'Turing.StepMachine.ResourceCertificate.comp' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.StepMachine.ResourceCertificate.comp

end ComplexityTests.StepMachineResourceCertificate
