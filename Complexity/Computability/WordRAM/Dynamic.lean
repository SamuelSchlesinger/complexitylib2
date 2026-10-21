/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Compile
public import Complexity.Foundations.Semantics.Stateful.Resource
public import Complexity.Computability.WordRAM.Trace

/-!
# Fixed-program implementations of dynamic data structures

An implementation has one structured program, one output register, and a register-only calling
convention. Each call replaces designated input registers with encoded words, preserving all
other registers and the entire memory. Argument encoding, external delivery, and result decoding
are not charged; all
instructions of the operation, including its final `halt`, are charged. Initialization is a
separate obligation expressed by the initial representation hypothesis. Argument encoding
depends on the requested operation, without access to the maintained machine data.

Certificates require bounded configurations and bounded arguments, and a successful exact
machine execution for every admissible operation. Determinism supplies correctness for every
execution. The generic history theorem then preserves all observations and adds actual costs.
The same single compiled program is used at every call; the interface does not generate code
from the requested operation.

## Main definitions

* `DynamicProgram`: fixed code, an input-register convention, and an output decoder.
* `DynamicProgram.ExecOp`: execution of a call, including the final halt charge.
* `DynamicCertificate`: representation, word bounds, and per-operation semantic machine proofs.

## Main results

* `DynamicProgram.ExecOp.executes`: calls execute the same flat program.
* `DynamicCertificate.realization`: machine certificates instantiate shared adaptive execution.
* `DynamicCertificate.instruction_bound`: separate native instruction-cost certificates.
-/

@[expose] public section

namespace Cslib.WordRAM

universe u v z

variable {r : ℕ} {D : Stateful.Spec.{u, v, z}}

/-- A single program serving all operations through a fixed register calling convention. -/
structure DynamicProgram (D : Stateful.Spec.{u, v, z}) (r : ℕ) where
  /-- The same code is executed for every operation. -/
  code : Code r
  /-- Register returned by the final halt instruction. -/
  output : Fin r
  /-- Registers overwritten by externally supplied operation arguments. -/
  input : Fin r → Bool
  /-- Encoded arguments, independent of the maintained machine state. -/
  encode : D.Op → Fin r → ℕ
  /-- Interpretation of the final register tuple as the operation's typed observation. -/
  decode : (o : D.Op) → (Fin r → ℕ) → Option (D.Result o)

namespace DynamicProgram

variable (P : DynamicProgram D r)

/-- Deliver operation arguments without changing maintained memory or non-input registers. -/
def prepare (o : D.Op) (x : Data r) : Data r where
  regs i := if P.input i then P.encode o i else x.regs i
  mem := x.mem

@[simp]
theorem prepare_mem (o : D.Op) (x : Data r) : (P.prepare o x).mem = x.mem := rfl

/-- Registers outside the calling convention retain their contents. -/
theorem prepare_regs_of_not_input {i : Fin r} (hi : P.input i = false) (o : D.Op) (x : Data r) :
    (P.prepare o x).regs i = x.regs i := by
  simp [prepare, hi]

/-- Argument delivery preserves bounded words when the arguments fit. -/
theorem prepare_bounded {w : ℕ} {o : D.Op} {x : Data r} (hx : x.Bounded w)
    (ho : ∀ i, P.input i = true → Fits w (P.encode o i)) : (P.prepare o x).Bounded w := by
  refine ⟨fun i => ?_, hx.2⟩
  change Fits w (if P.input i then P.encode o i else x.regs i)
  split
  · exact ho i (by assumption)
  · exact hx.1 i

/-- Native evidence for one call: instruction count including halt and the memory transcript. -/
structure OperationTrace where
  /-- Number of executed machine instructions, including the final halt. -/
  instructions : ℕ
  /-- All reads and writes, in execution order. -/
  probes : List Probe

/-- A bounded machine call with native execution evidence independent of any resource bound. -/
def ExecOp (w : ℕ) : Stateful.Execution D (Data r) OperationTrace := fun x o a y trace =>
  (P.prepare o x).Bounded w ∧ ∃ n, TraceExec w P.code (P.prepare o x) y n trace.probes ∧
    P.decode o y.regs = some a ∧ trace.instructions = n + 1

/-- Every call is an execution of one fixed flat machine program. The returned register tuple
is observed at the final state; the designated output register is also the halt value. -/
theorem ExecOp.executes {w : ℕ} {x y : Data r} {o : D.Op} {a : D.Result o}
    {trace : OperationTrace} (h : P.ExecOp w x o a y trace) :
    Executes w (P.code.program P.output) ⟨0, P.prepare o x⟩ (y.regs P.output)
      trace.instructions := by
  obtain ⟨_, n, he, _, ht⟩ := h
  rw [ht]
  exact he.exec.executes P.output

/-- A call preserves bounded words, including every word in the observed register tuple. -/
theorem ExecOp.bounded {w : ℕ} {x y : Data r} {o : D.Op} {a : D.Result o}
    {trace : OperationTrace} (h : P.ExecOp w x o a y trace) : y.Bounded w := by
  obtain ⟨hb, n, he, _, _⟩ := h
  exact he.exec.bounded hb

/-- Calls are deterministic in their final representation, observation, and instruction count. -/
theorem ExecOp.unique {w : ℕ} {x y y' : Data r} {o : D.Op} {a a' : D.Result o}
    {trace trace' : OperationTrace} (h : P.ExecOp w x o a y trace)
    (h' : P.ExecOp w x o a' y' trace') :
    y = y' ∧ a = a' ∧ trace.instructions = trace'.instructions := by
  obtain ⟨_, n, he, ha, ht⟩ := h
  obtain ⟨_, n', he', ha', ht'⟩ := h'
  obtain ⟨rfl, rfl⟩ := he.exec.unique he'.exec
  exact ⟨rfl, Option.some.inj (ha.symm.trans ha'), ht.trans ht'.symm⟩

/-- The write transcript supplies a frame rule for a call, including register-only delivery. -/
theorem ExecOp.frame {w : ℕ} {x y : Data r} {o : D.Op} {a : D.Result o}
    {trace : OperationTrace} (h : P.ExecOp w x o a y trace) {Q : HeapAssertion}
    (hQ : Q.holds x.mem) (hd : Disjoint Q.footprint (Probe.writes trace.probes)) :
    Q.holds y.mem := by
  obtain ⟨_, n, he, _, _⟩ := h
  exact he.frame hQ hd

end DynamicProgram

/-- Per-operation semantic proof obligations tied to fixed bounded-word code.
Performance claims are supplied separately, as `Stateful.Bound` certificates. -/
structure DynamicCertificate (P : DynamicProgram D r) (w : ℕ) where
  /-- Abstract state represented by the persistent machine data. -/
  rep : D.State → Data r → Prop
  /-- Represented configurations contain only machine words. -/
  bounded : ∀ {s x}, rep s x → x.Bounded w
  /-- Admissible arguments fit the machine's word size. -/
  arguments_fit : ∀ {s} (o), D.valid s o → ∀ i, P.input i = true → Fits w (P.encode o i)
  /-- A machine execution implements an admissible operation. -/
  execute : ∀ {s x} (o), rep s x → D.valid s o →
    ∃ y n, Exec w P.code (P.prepare o x) y n ∧
      P.decode o y.regs = some (D.step s o).2 ∧ rep (D.step s o).1 y

namespace DynamicCertificate

variable {P : DynamicProgram D r} {w : ℕ} (C : DynamicCertificate P w)

/-- Fixed-program certificates realize the common dynamic specification, without choosing a cost. -/
def realization : Stateful.Realization D (P.ExecOp w) where
  rep := C.rep
  total o hr hv := by
    obtain ⟨y, n, he, ha, _⟩ := C.execute o hr hv
    obtain ⟨ts, hts⟩ := he.exists_trace
    exact ⟨_, y, ⟨n + 1, ts⟩,
      P.prepare_bounded (C.bounded hr) (C.arguments_fit o hv), n, hts, ha, rfl⟩
  correct hr hv he := by
    obtain ⟨y, n, he', ha, hr'⟩ := C.execute _ hr hv
    obtain ⟨_, k, ht, ha', _⟩ := he
    obtain ⟨rfl, rfl⟩ := ht.exec.unique he'
    exact ⟨Option.some.inj (ha'.symm.trans ha), hr'⟩

/-- A separate per-operation instruction estimate supplies a reusable resource certificate. -/
theorem instruction_bound (charge : D.State → D.Op → ℕ)
    (hbound : ∀ {s x} (o) {y n}, C.rep s x → D.valid s o →
      Exec w P.code (P.prepare o x) y n → n + 1 ≤ charge s o) :
    Stateful.Bound C.realization DynamicProgram.OperationTrace.instructions charge := by
  intro s x o a y trace hr hv he
  obtain ⟨_, n, ht, _, hn⟩ := he
  rw [hn]
  exact hbound o hr hv ht.exec

/-- The same native evidence separately bounds memory probes by the instruction charge. -/
theorem probe_bound (charge : D.State → D.Op → ℕ)
    (B : Stateful.Bound C.realization DynamicProgram.OperationTrace.instructions charge) :
    Stateful.Bound C.realization (fun t => t.probes.length) charge := by
  intro s x o a y trace hr hv he
  have hb := B hr hv he
  obtain ⟨_, n, ht, _, hn⟩ := he
  exact ht.length_le.trans ((Nat.le_add_right n 1).trans (hn ▸ hb))

end DynamicCertificate

end Cslib.WordRAM
