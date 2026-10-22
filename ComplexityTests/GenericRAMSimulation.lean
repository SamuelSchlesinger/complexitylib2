/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.GenericRAM.Simulation.Turing
public import Complexity.Computability.GenericRAM.Native.Nat
import Mathlib.Data.Fin.VecNotation

/-!
# Finite RAM simulation and native step certificate checks

A fixed store/load/branch/halt client runs at several configurations. Separate examples exercise
current and continuing labels, missing instructions, failed addresses, invalid moved values,
failed tests versus false tests, the distinction between produced and moved values, uniform native
step execution across runtime configurations, and retention of nonpolynomial primitive and
sparse-memory resource bounds.
-/

@[expose] public section

namespace ComplexityTests.GenericRAMSimulation

open Cslib.GenericRAM Turing.MultiTapeTM
open BoundedNat

/-- Initial finite configuration with two registers and empty sparse store. -/
def initial (a v default : ℕ) : FiniteState model 2 :=
  ⟨0, ![a, v], default, ∅⟩

/-- Fixed four-instruction store/load/branch/halt client program. -/
def client : Program model 2 :=
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

/-- State reached after storing 3 at address 0. -/
def stored : FiniteState model 2 := { (initial 0 3 0).write 0 3 with pc := 1 }
/-- State reached after clearing register 1 and loading address 0 back into register 1. -/
def loaded : FiniteState model 2 := { (stored.set 1 0).set 1 3 with pc := 2 }
/-- State reached after taking the false branch to the halt instruction. -/
def halting : FiniteState model 2 := { loaded with pc := 3 }

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

/-- Concrete native step certificate for the four-instruction store/load/branch/halt client. -/
noncomputable def clientCertificate :
    NativeCertificate (fun q : ℕ × FiniteState model 2 => FiniteState.step q.1 client q.2)
      (FiniteState.inputEncoding encoding) (FiniteState.resultEncoding encoding) :=
  FiniteState.stepCertificate encoding nativePrimitives client

/-- One finite native machine implements the fixed client across all runtime configurations. -/
theorem client_step_inO :
    ComputableTidilyInO (fun q : ℕ × FiniteState model 2 => FiniteState.step q.1 client q.2)
      (FiniteState.inputEncoding encoding) (FiniteState.resultEncoding encoding)
      (FiniteState.stepTime encoding nativePrimitives client)
      (FiniteState.stepSpace encoding nativePrimitives client) :=
  FiniteState.step_inO encoding nativePrimitives client

/-- A single finite native machine handles distinct runtime configurations (`k = 4`, `k = 8`,
and invalid `k = 0`) without fixing the configuration in its transition table. -/
theorem uniform_machine_across_configs :
    ∃ (c k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State),
      (∀ q : ℕ × FiniteState model 2,
        tm.ComputesTidilyInTimeAndSpace
          (FiniteState.inputEncoding encoding q)
          (FiniteState.resultEncoding encoding (FiniteState.step q.1 client q.2))
          (c * (FiniteState.stepTime encoding nativePrimitives client q + 1))
          (c * (FiniteState.stepSpace encoding nativePrimitives client q + 1))) ∧
      FiniteState.step (M := model) 4 client (stored.set 1 0) = some (.inl loaded) ∧
      FiniteState.step (M := model) 8 client (stored.set 1 0) = some (.inl loaded) ∧
      FiniteState.step (M := model) 0 client (stored.set 1 0) = none := by
  obtain ⟨c, ⟨k, State, hfin, tm, htm⟩, _⟩ := client_step_inO
  exact ⟨c, k, State, hfin, tm, htm, rfl, rfl, rfl⟩

/-- Encoded finite-state length is bounded by control, register bound, default, and store size. -/
example (s : FiniteState model 2) {b : ℕ} (hb : ∀ i, (encNat (s.regs i)).length ≤ b) :
    (FiniteState.encoding encoding s).length ≤
      2 * (encNat s.pc).length + 2 * 2 * (2 * b + 1) +
        2 * (encNat s.default).length +
        (SparseMemory.entries s.memory).length *
          (4 * SparseMemory.maxKeyLength encNat s.memory +
            2 * SparseMemory.maxValueLength encNat s.memory + 3) + 3 :=
  FiniteState.length_encoding_le encoding s hb

/-- Primitive bundle whose constant certificate carries an exponential resource bound `2 ^ k`. -/
noncomputable def expPrimitives : model.NativePrimitives encoding where
  constant c :=
    ⟨fun k => (nativePrimitives.constant c).time k + 2 ^ k,
     fun k => (nativePrimitives.constant c).space k + 2 ^ k,
     (nativePrimitives.constant c).computes.mono_le
       (fun _ => Nat.le_add_right _ _) (fun _ => Nat.le_add_right _ _)⟩
  operation := nativePrimitives.operation
  test := nativePrimitives.test
  address := nativePrimitives.address
  validMove := nativePrimitives.validMove
  validPC := nativePrimitives.validPC

/-- `stepTime` and `stepSpace` retain nonpolynomial supplied primitive bounds rather than
selecting a polynomial bound. -/
theorem retained_exponential_primitive_bound (k : ℕ) (hk : 1 ≤ k) (s : FiniteState model 2)
    (hpc : s.pc = 0) :
    2 ^ k ≤ FiniteState.stepTime encoding expPrimitives [.op (.const 0 1)] (k, s) ∧
      2 ^ k ≤ FiniteState.stepSpace encoding expPrimitives [.op (.const 0 1)] (k, s) := by
  have hv : model.validPC k s.pc = true := by
    simp [model, hpc]
    omega
  have htc : 2 ^ k ≤ (expPrimitives.constant 1).time k := Nat.le_add_left _ _
  have hsc : 2 ^ k ≤ (expPrimitives.constant 1).space k := Nat.le_add_left _ _
  have hto : (expPrimitives.constant 1).time k ≤
      FiniteState.opTime encoding expPrimitives (.const 0 1) (k, s) :=
    FiniteState.le_opTime_const encoding expPrimitives 0 1 (k, s)
  have hso : (expPrimitives.constant 1).space k ≤
      FiniteState.opSpace encoding expPrimitives (.const 0 1) (k, s) :=
    FiniteState.le_opSpace_const encoding expPrimitives 0 1 (k, s)
  have hti := FiniteState.le_instrTime_op encoding expPrimitives 1 (.const 0 1) (k, s)
  have hsi := FiniteState.le_instrSpace_op encoding expPrimitives 1 (.const 0 1) (k, s)
  rw [FiniteState.stepTime_cons, FiniteState.stepSpace_cons, hv]
  simp only [hpc, ite_true]
  exact ⟨le_trans htc (le_trans hto (le_trans hti (by omega))),
    le_trans hsc (le_trans hso (le_trans hsi (by omega)))⟩

/-- Valid stores in `client` retain the parameterized sparse-memory write bound in `stepTime`. -/
theorem retained_sparse_write_bound (k : ℕ) (hk : 4 ≤ k) :
    SparseMemory.writeTime encNat encNat ((0, 3), ∅) ≤
      FiniteState.stepTime encoding nativePrimitives client (k, initial 0 3 0) := by
  have h0 : 0 < k := by omega
  have h3 : 3 < k := by omega
  have hv : model.validPC k (initial 0 3 0).pc = true := by
    simp [model, initial, h0]
  have ha : model.address k ((initial 0 3 0).regs 0) = some 0 := by
    simp [model, initial, h0]
  have hm : model.validMove k ((initial 0 3 0).regs 1) = true := by
    simp [model, initial, h3]
  have hto := FiniteState.le_opTime_store encoding nativePrimitives 0 1 (k, initial 0 3 0) 0 ha hm
  have hti := FiniteState.le_instrTime_op encoding nativePrimitives 1 (.store 0 1)
    (k, initial 0 3 0)
  rw [client, FiniteState.stepTime_cons, hv]
  have hpc : (initial 0 3 0).pc = 0 := rfl
  simp only [hpc, ite_true]
  exact le_trans hto (le_trans hti (by omega))

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInO.inl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInO.inl

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInO.inr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInO.inr

/--
info: 'Cslib.GenericRAM.FiniteState.denote_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiniteState.denote_step

/--
info: 'Cslib.GenericRAM.FiniteState.length_encoding_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiniteState.length_encoding_le

/--
info: 'Cslib.GenericRAM.FiniteState.stepCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiniteState.stepCertificate

/--
info: 'Cslib.GenericRAM.FiniteState.step_inO' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiniteState.step_inO

/--
info: 'ComplexityTests.GenericRAMSimulation.uniform_machine_across_configs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms uniform_machine_across_configs

/--
info: 'ComplexityTests.GenericRAMSimulation.retained_exponential_primitive_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms retained_exponential_primitive_bound

end ComplexityTests.GenericRAMSimulation
