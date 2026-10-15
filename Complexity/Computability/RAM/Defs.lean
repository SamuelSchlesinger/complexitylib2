/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Computability.URM.Basic
public import Cslib.Foundations.Relation.Defs

/-!
# Random-access machines

A *random-access machine* (RAM) is a register machine whose registers hold natural numbers of
unbounded size, whose instructions do arithmetic on whole registers, and which can address a
register through the contents of another (*indirect addressing*), so that a fixed program reaches
unboundedly many registers [Cook and Reckhow, Section 1][CookReckhow1973]. This file defines the
machine, its single steps and its runs. How long a run takes depends on how instructions are
charged, which is the subject of `Cslib.RAM.time` and its cost measures.

The model extends cslib's unlimited register machines (`Cslib.URM`): it uses the same register
contents `Cslib.URM.Regs` and their `read`/`write` API, a program is again a list of instructions,
a state is again a program counter with register contents, a run starts at instruction `0` with
the inputs in registers `0, 1, …` (`Cslib.RAM.State.init`), and a state is halted once its program
counter is past the end of the program. The instruction set is that of Cook and Reckhow
[Cook and Reckhow, Table I][CookReckhow1973] with three changes: registers hold natural numbers
rather than integers, so subtraction is truncated and the conditional jump tests for a nonzero
register; there are no input and output instructions, since the inputs sit in registers as for
URMs; and there is a multiplication instruction, which is what makes the unit cost measure unsound
(see `Cslib.RAM.logGap_squaring`).

## Design notes

* `Cslib.RAM.State` is a separate structure from `Cslib.URM.State`, with the same two fields,
  because its halting predicate refers to RAM programs.
* Besides the single-step relation `Cslib.RAM.Step`, which mirrors `Cslib.URM.Step`, there is a
  total step function `Cslib.RAM.step`, which leaves a halted state fixed, and the run
  `Cslib.RAM.run p n` is its `n`-th iterate. Costs are sums over runs, and a run as a function of
  its length is what makes those sums definitions rather than relations;
  `Cslib.RAM.steps_iff_exists_run` connects the two views.

## Main definitions

* `Cslib.RAM.Instr`: the instructions: constants, addition, truncated subtraction,
  multiplication, indirect load and store, and a conditional jump.
* `Cslib.RAM.Program`, `Cslib.RAM.State`: programs and machine states.
* `Cslib.RAM.Instr.exec`: the effect of one instruction on a state.
* `Cslib.RAM.step`, `Cslib.RAM.run`: the step function and the run for a given number of steps.
* `Cslib.RAM.Step`, `Cslib.RAM.Steps`: the single-step relation and its reflexive transitive
  closure.

## Main results

* `Cslib.RAM.Step.deterministic`: a state has at most one successor.
* `Cslib.RAM.isHalted_iff_normal`: a state is halted iff it has no successor.
* `Cslib.RAM.run_add`, `Cslib.RAM.run_eq_of_le`: runs compose, and are stationary once halted.
* `Cslib.RAM.steps_iff_exists_run`: the states reachable from `s` are the states `run p n s`.

## References

* [S. A. Cook and R. A. Reckhow, *Time bounded random access machines*][CookReckhow1973]
* [N. J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
-/

@[expose] public section

namespace Cslib.RAM

/-! ## Instructions, programs and states -/

/-- RAM instructions, written destination first as in Cook and Reckhow's `X_i ← X_j + X_k`
[Cook and Reckhow, Table I][CookReckhow1973]. The register named by a *direct* operand is part of
the instruction; the register named by an *indirect* operand is the contents of another
register. -/
inductive Instr : Type where
  /-- `const d v` sets register `d` to the constant `v`. -/
  | const (d v : ℕ)
  /-- `add d i j` sets register `d` to the sum of registers `i` and `j`. -/
  | add (d i j : ℕ)
  /-- `sub d i j` sets register `d` to the truncated difference of registers `i` and `j`. -/
  | sub (d i j : ℕ)
  /-- `mul d i j` sets register `d` to the product of registers `i` and `j`. -/
  | mul (d i j : ℕ)
  /-- `load d a` sets register `d` to the contents of the register whose index is in
  register `a` (an indirect read). -/
  | load (d a : ℕ)
  /-- `store a i` sets the register whose index is in register `a` to the contents of
  register `i` (an indirect write). -/
  | store (a i : ℕ)
  /-- `jpos i q` jumps to instruction `q` if register `i` is positive, and otherwise proceeds to
  the next instruction. -/
  | jpos (i q : ℕ)
deriving DecidableEq, Repr

/-- A RAM program is a list of instructions, indexed by the program counter. -/
abbrev Program := List Instr

/-- A RAM state: a program counter (`0`-indexed) and register contents. -/
@[ext]
structure State where
  /-- The program counter: the index of the next instruction. -/
  pc : ℕ
  /-- The register contents. -/
  regs : URM.Regs

namespace State

/-- The initial state on the given inputs: the program counter is `0`, and the inputs are in
registers `0, 1, …`, all other registers holding `0`. -/
def init (inputs : List ℕ) : State := ⟨0, URM.Regs.ofInputs inputs⟩

/-- A state is halted for a program once its program counter is past the end of the program. -/
def isHalted (s : State) (p : Program) : Prop := p.length ≤ s.pc

instance (s : State) (p : Program) : Decidable (s.isHalted p) :=
  inferInstanceAs (Decidable (p.length ≤ s.pc))

instance : Inhabited State := ⟨init []⟩

@[simp]
theorem isHalted_iff {s : State} {p : Program} : s.isHalted p ↔ p.length ≤ s.pc := Iff.rfl

@[simp]
theorem init_pc (inputs : List ℕ) : (init inputs).pc = 0 := rfl

@[simp]
theorem read_init_nil (n : ℕ) : (init []).regs.read n = 0 := rfl

end State

/-! ## Execution -/

namespace Instr

/-- The state reached by executing an instruction. -/
def exec : Instr → State → State
  | const d v, s => ⟨s.pc + 1, s.regs.write d v⟩
  | add d i j, s => ⟨s.pc + 1, s.regs.write d (s.regs.read i + s.regs.read j)⟩
  | sub d i j, s => ⟨s.pc + 1, s.regs.write d (s.regs.read i - s.regs.read j)⟩
  | mul d i j, s => ⟨s.pc + 1, s.regs.write d (s.regs.read i * s.regs.read j)⟩
  | load d a, s => ⟨s.pc + 1, s.regs.write d (s.regs.read (s.regs.read a))⟩
  | store a i, s => ⟨s.pc + 1, s.regs.write (s.regs.read a) (s.regs.read i)⟩
  | jpos i q, s => ⟨if 0 < s.regs.read i then q else s.pc + 1, s.regs⟩

end Instr

/-- One step of `p` from `s`: execute the current instruction, or stay put if `s` is halted. -/
def step (p : Program) (s : State) : State :=
  match p[s.pc]? with
  | some i => i.exec s
  | none => s

/-- The state after running `p` from `s` for `n` steps, staying put once halted. -/
def run (p : Program) (n : ℕ) : State → State := (step p)^[n]

/-- The single-step relation of a program, as for URMs (`Cslib.URM.Step`): a state that is not
halted steps to the result of executing its current instruction. -/
inductive Step (p : Program) : State → State → Prop where
  | exec {s : State} {i : Instr} (h : p[s.pc]? = some i) : Step p s (i.exec s)

/-- Multi-step execution: the reflexive transitive closure of `Step`. -/
abbrev Steps (p : Program) : State → State → Prop := Relation.ReflTransGen (Step p)

variable {p : Program} {s t u : State} {m n : ℕ}

/-! ### Steps -/

theorem step_of_getElem? {i : Instr} (h : p[s.pc]? = some i) : step p s = i.exec s := by
  simp only [step, h]

theorem step_of_isHalted (h : s.isHalted p) : step p s = s := by
  simp only [step, List.getElem?_eq_none (State.isHalted_iff.mp h)]

/-- A state that is not halted steps to `step p s`. -/
theorem step_step (h : ¬s.isHalted p) : Step p s (step p s) := by
  have hlt : s.pc < p.length := by simpa using h
  have hi : p[s.pc]? = some p[s.pc] := List.getElem?_eq_getElem hlt
  rw [step_of_getElem? hi]
  exact .exec hi

namespace Step

theorem step_eq (h : Step p s t) : step p s = t := by
  cases h with
  | exec hi => exact step_of_getElem? hi

theorem not_isHalted (h : Step p s t) : ¬s.isHalted p := by
  cases h with
  | exec hi =>
    intro hs
    simp [List.getElem?_eq_none (State.isHalted_iff.mp hs)] at hi

/-- The step relation is deterministic: each state has at most one successor. -/
theorem deterministic : Relator.RightUnique (Step p) :=
  fun _ _ _ h₁ h₂ => h₁.step_eq.symm.trans h₂.step_eq

end Step

theorem step_iff (h : ¬s.isHalted p) : Step p s t ↔ step p s = t :=
  ⟨Step.step_eq, fun ht => ht ▸ step_step h⟩

/-- A state is halted iff it is normal (has no successor) for the step relation. -/
theorem isHalted_iff_normal : s.isHalted p ↔ Relation.Normal (Step p) s :=
  ⟨fun h ⟨_, ht⟩ => ht.not_isHalted h, fun h => by_contra fun hs => h ⟨_, step_step hs⟩⟩

/-! ### Runs -/

@[simp]
theorem run_zero : run p 0 s = s := rfl

theorem run_succ : run p (n + 1) s = run p n (step p s) :=
  Function.iterate_succ_apply _ _ _

theorem run_succ' : run p (n + 1) s = step p (run p n s) :=
  Function.iterate_succ_apply' _ _ _

/-- Runs compose: running for `m + n` steps is running for `n` steps after `m`. -/
theorem run_add : run p (m + n) s = run p n (run p m s) := by
  rw [run, Nat.add_comm, Function.iterate_add_apply]
  rfl

/-- A halted state stays put. -/
theorem run_of_isHalted (h : s.isHalted p) : run p n s = s :=
  Function.iterate_fixed (step_of_isHalted h) n

/-- Once a run has halted, running longer changes nothing. -/
theorem run_eq_of_le (hmn : m ≤ n) (h : (run p m s).isHalted p) : run p n s = run p m s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [run_add, run_of_isHalted h]

theorem steps_run : Steps p s (run p n s) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    rw [run_succ']
    by_cases h : (run p n s).isHalted p
    · rwa [step_of_isHalted h]
    · exact ih.tail (step_step h)

/-- The states reachable from `s` are exactly the states of the run from `s`. -/
theorem steps_iff_exists_run : Steps p s t ↔ ∃ n, run p n s = t := by
  refine ⟨fun h => ?_, fun ⟨n, hn⟩ => hn ▸ steps_run⟩
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨n, rfl⟩ := ih
    exact ⟨n + 1, by rw [run_succ', hstep.step_eq]⟩

end Cslib.RAM

end
