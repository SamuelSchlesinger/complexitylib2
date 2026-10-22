/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.WordRAM.DynamicArray

/-!
# Doubling-array execution tests and axiom guards

Concrete symbolic executions trace the twelve-register doubling array across three capacity
doublings (`1 → 2 → 4 → 8`), checking exact register contents, live and historical memory
blocks, zeroed spare cells, frontier growth (`1 → 3 → 7 → 15`), and exact instruction counts
(`15` for initialization, `7` without growth, `34`, `49`, and `79` across the three doublings,
each attaining the exact `49`-instruction potential bound). An adaptive `Stateful` client also
interleaves appends with indexed reads.
-/

@[expose] public section

open Cslib Cslib.WordRAM
open Cslib.Algorithms.WordRAM

namespace DynamicArrayTest

/-- Initial blank state on 12 registers. -/
def blank : Data 12 := ⟨fun _ => 0, fun _ => 0⟩

theorem blank_bounded : blank.Bounded 8 :=
  ⟨fun _ => fits_zero 8, fun _ => fits_zero 8⟩

/-- Snapshot the persistent doubling-array registers `(ptr, len, cap, frontier)` and a list of
memory addresses, paired with the executed instruction count. -/
def snapshot (addrs : List ℕ) (yn : Data 12 × ℕ) : ℕ × (ℕ × ℕ × ℕ × ℕ) × List ℕ :=
  (yn.2,
   (yn.1.regs DynamicArray.ptr, yn.1.regs DynamicArray.len,
    yn.1.regs DynamicArray.cap, yn.1.regs DynamicArray.frontier),
   addrs.map yn.1.mem)

/-- Concrete state representing `vs` at `(ptrVal, capVal, frontierVal)`. -/
def mkState (ptrVal lenVal capVal frontierVal argVal : ℕ) (memList : List ℕ) : Data 12 where
  regs i :=
    if i = DynamicArray.ptr then ptrVal
    else if i = DynamicArray.len then lenVal
    else if i = DynamicArray.cap then capVal
    else if i = DynamicArray.frontier then frontierVal
    else if i = DynamicArray.arg then argVal
    else 0
  mem a := memList.getD a 0

/-- Concrete witness for the doubling-array representation invariant `Rep` after doubling `1 → 2`
on `[10, 20]`. -/
def repTwoState : Data 12 := mkState 1 2 2 3 0 [10, 10, 20]

theorem repTwo_rep : DynamicArray.Rep [10, 20] repTwoState where
  length_eq := rfl
  capacity_pos := by decide
  length_le := by decide
  capacity_le := by decide
  pointer_eq := rfl
  frontier_eq := rfl
  contents i := by fin_cases i <;> rfl

theorem repTwo_boundedRep : DynamicArray.BoundedRep 8 [10, 20] repTwoState :=
  ⟨⟨fun i => by fin_cases i <;> decide,
    fun a => by
      rcases a with _ | _ | _ | a <;> simp [repTwoState, mkState, Fits]⟩,
   repTwo_rep⟩

/-- `initProgram` allocates the 1-word block at address `0` (`ptr = 0, len = 0, cap = 1,
frontier = 1`) and zeroes cell `0` in `15` instructions. -/
example : (DynamicArray.initProgram.eval 8 4 blank).map (snapshot [0, 1]) =
    some (15, (0, 0, 1, 1), [0, 0]) := by decide

/-- First append (`10` into `[]` at `cap = 1`): no doubling, writes `mem 0 = 10` in `7`
instructions. -/
example : (DynamicArray.program.eval 8 4 (mkState 0 0 1 1 10 [0])).map (snapshot [0, 1]) =
    some (7, (0, 1, 1, 1), [10, 0]) := by decide

/-- Second append (`20` into `[10]` at `cap = 1`): triggers doubling `1 → 2`, allocates `[1, 3)`,
copies `10` to `mem 1`, writes `20` to `mem 2`, advances `frontier` to `3`, in `34` instructions
(`34 + potential [10, 20] - potential [10] = 34 + 30 - 15 = 49`). -/
example : (DynamicArray.program.eval 8 4 (mkState 0 1 1 1 20 [10])).map (snapshot [0, 1, 2, 3]) =
    some (34, (1, 2, 2, 3), [10, 10, 20, 0]) := by decide

/-- Third append (`30` into `[10, 20]` at `cap = 2`): triggers doubling `2 → 4`, allocates `[3, 7)`,
copies `[10, 20]` to `mem 3..4`, writes `30` to `mem 5`, leaves `mem 6 = 0`, advances `frontier`
to `7`, in `49` instructions (`49 + 30 - 30 = 49`). -/
example : (DynamicArray.program.eval 8 8 (mkState 1 2 2 3 30 [10, 10, 20])).map
    (snapshot [3, 4, 5, 6]) =
  some (49, (3, 3, 4, 7), [10, 20, 30, 0]) := by decide

/-- Fourth append (`40` into `[10, 20, 30]` at `cap = 4`): no doubling, writes `40` to `mem 6` in
`7` instructions. -/
example : (DynamicArray.program.eval 8 8
    (mkState 3 3 4 7 40 [10, 10, 20, 10, 20, 30, 0])).map (snapshot [3, 4, 5, 6]) =
  some (7, (3, 4, 4, 7), [10, 20, 30, 40]) := by decide

/-- Fifth append (`50` into `[10, 20, 30, 40]` at `cap = 4`): triggers doubling `4 → 8`, allocates
`[7, 15)`, copies `[10, 20, 30, 40]` to `mem 7..10`, writes `50` to `mem 11`, zeroes `mem 12..14`,
advances `frontier` to `15 < 4 * 5 = 20`, in `79` instructions (`79 + 30 - 60 = 49`). -/
example : (DynamicArray.program.eval 8 10
    (mkState 3 4 4 7 50 [10, 10, 20, 10, 20, 30, 40])).map
    (snapshot [7, 8, 9, 10, 11, 12, 13, 14]) =
  some (79, (7, 5, 8, 15), [10, 20, 30, 40, 50, 0, 0, 0]) := by decide

/-- Indexed read (`getProgram`) reads element `4` (`50`) from the `cap = 8` block at `ptr = 7` in
`2` instructions. -/
example : (DynamicArray.getProgram.eval 8 0
    (mkState 7 5 8 15 4 [10, 10, 20, 10, 20, 30, 40, 10, 20, 30, 40, 50, 0, 0, 0])).map
    (fun yn => (yn.2, yn.1.regs DynamicArray.temp)) =
  some (2, 50) := by decide

/-- Adaptive client: append `11` and `22`, read index `0`, then append the observed value plus
`33` and read index `2`. -/
def adaptiveClient : (DynamicArray.spec 8).Client (ℕ × ℕ) :=
  .liftBind (.append 11) fun _ =>
  .liftBind (.append 22) fun _ =>
  .liftBind (.get 0) fun (first : ℕ) =>
  .liftBind (.append (first + 33)) fun _ =>
  .liftBind (.get 2) fun (third : ℕ) => .pure (first, third)

example : (DynamicArray.spec 8).runClient [] adaptiveClient =
    ((11, 44), [11, 22, 44],
     [.append 11, .append 22, .get 0, .append 44, .get 2]) := rfl

theorem adaptiveClient_valid :
    (DynamicArray.spec 8).ValidHistory []
      ((DynamicArray.spec 8).runClient [] adaptiveClient).2.2 := by
  change (Fits 8 11 ∧ Fits 8 4) ∧ (Fits 8 22 ∧ Fits 8 12) ∧
    (0 < 2 ∧ Fits 8 0) ∧ (Fits 8 44 ∧ Fits 8 20) ∧ (2 < 3 ∧ Fits 8 2) ∧ True
  decide

/-- End-to-end adaptive execution from `initProgram` satisfies the linear instruction bound
`15 + 5 * 52 = 275` and space bound `frontier < 4 * 3 = 12`. -/
example : ∃ ready y traces, Exec 8 DynamicArray.initProgram blank ready 15 ∧
    Stateful.Executes ((DynamicArray.implementation 8).ExecOp 8) adaptiveClient ready
      (11, 44) y traces ∧
    DynamicArray.BoundedRep 8 [11, 22, 44] y ∧
    15 + Stateful.total DynamicProgram.OperationTrace.instructions traces +
      DynamicArray.potential [11, 22, 44] y ≤ 275 ∧
    y.regs DynamicArray.frontier < 12 := by
  obtain ⟨ready, y, traces, hi, he, hy, hb, hspace⟩ :=
    DynamicArray.run_initialized (by decide : Fits 8 1) adaptiveClient
      blank_bounded adaptiveClient_valid
  exact ⟨ready, y, traces, hi, he, hy, hb, hspace (by decide)⟩

/-- `run_appendAll` across five elements (`1 → 2 → 4 → 8` doublings) guarantees total charged
instructions `≤ 15 + 5 * 52 = 275` and `frontier < 20`. -/
example : ∃ ready y traces, Exec 8 DynamicArray.initProgram blank ready 15 ∧
    Stateful.Executes ((DynamicArray.implementation 8).ExecOp 8)
      (DynamicArray.appendAll [10, 20, 30, 40, 50]) ready () y traces ∧
    DynamicArray.BoundedRep 8 [10, 20, 30, 40, 50] y ∧
    15 + Stateful.total DynamicProgram.OperationTrace.instructions traces +
      DynamicArray.potential [10, 20, 30, 40, 50] y ≤ 275 ∧
    y.regs DynamicArray.frontier < 20 := by
  obtain ⟨ready, y, traces, hi, he, hy, hb, hspace⟩ :=
    DynamicArray.run_appendAll (w := 8) (vs := [10, 20, 30, 40, 50])
      (by decide : Fits 8 1) blank_bounded (by decide) (by decide)
  exact ⟨ready, y, traces, hi, he, hy, hb, hspace (by decide)⟩

-- Precondition rejections: out-of-range read index and word overflow.
example : ¬(DynamicArray.spec 8).valid [10, 20] (.get 2) := by decide
example : ¬(DynamicArray.spec 4).valid [10, 20] (.append 5) := by decide

/-- info: 'Cslib.Algorithms.WordRAM.DynamicArray.Rep.space' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DynamicArray.Rep.space

/-- info: 'Cslib.Algorithms.WordRAM.DynamicArray.grow_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DynamicArray.grow_exec

/-- info: 'Cslib.Algorithms.WordRAM.DynamicArray.append_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DynamicArray.append_exec

/-- info: 'Cslib.Algorithms.WordRAM.DynamicArray.get_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DynamicArray.get_exec

/-- info: 'Cslib.Algorithms.WordRAM.DynamicArray.init_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DynamicArray.init_exec

/-- info: 'Cslib.Algorithms.WordRAM.DynamicArray.amortized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DynamicArray.amortized

/-- info: 'Cslib.Algorithms.WordRAM.DynamicArray.run_initialized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DynamicArray.run_initialized

/-- info: 'Cslib.Algorithms.WordRAM.DynamicArray.run_appendAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DynamicArray.run_appendAll

end DynamicArrayTest
