/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate
public import Cslib.Computability.Circuit.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Function.DependsOn

/-!
# Circuit input support

This file computes the original inputs that can affect each wire and proves
that circuit evaluation depends only on those inputs. An input on which a function depends
essentially (`EssentialAt`) therefore reaches an output of every circuit computing it.

## Main definitions

* `Cslib.Circuits.EssentialAt`: coordinates whose change can change a function.
* `Cslib.Circuits.Program.wireSupport`, `Cslib.Circuits.Circuit.inputSupport`.

## Main results

* `Cslib.Circuits.Circuit.dependsOn_eval`: a circuit depends only on its input support.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {U V : Type*} {n m g : ℕ}

/-- Changing only coordinate `i` can change the value of `f`. -/
def EssentialAt (f : (Fin n → U) → V) (i : Fin n) : Prop :=
  ∃ x y, (∀ k, k ≠ i → x k = y k) ∧ f x ≠ f y

/-- Every essential coordinate belongs to any support of the function. -/
theorem EssentialAt.mem_support {f : (Fin n → U) → V} {support : Finset (Fin n)} {i : Fin n}
    (h : EssentialAt f i) (hf : DependsOn f (support : Set (Fin n))) : i ∈ support := by
  obtain ⟨x, y, hxy, hne⟩ := h
  by_contra hi
  exact hne (hf fun k hk => hxy k fun e => hi (e ▸ hk))

/-- A coordinate is essential exactly when the function does not depend only on the others. -/
theorem essentialAt_iff_not_dependsOn {f : (Fin n → U) → V} {i : Fin n} :
    EssentialAt f i ↔ ¬DependsOn f {i}ᶜ := by
  simp only [EssentialAt, DependsOn, Set.mem_compl_iff, Set.mem_singleton_iff, not_forall,
    exists_prop]


/-- The original inputs supporting a line, given the support of each wire. -/
def Line.inputSupport
    (line : Line σ n g)
    (wireSupport : Wire n g → Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.biUnion fun k => wireSupport (line.wires k)


/-- Membership in a line's input support comes from one of its arguments. -/
@[simp] theorem Line.mem_inputSupport
    {line : Line σ n g}
    {wireSupport : Wire n g → Finset (Fin n)}
    {input : Fin n} :
    input ∈ line.inputSupport wireSupport ↔
      ∃ argument, input ∈ wireSupport (line.wires argument) := by
  simp [Line.inputSupport]


/-- The input support of every gate in a program. -/
def Program.gateSupport : ∀ {g : ℕ}, Program σ n g → Fin g → Finset (Fin n)
  | _, .empty => Fin.elim0
  | _, .gate program line =>
      let prior := program.gateSupport
      let wireSupport := Wire.elim (fun k => {k}) prior
      Fin.lastCases (line.inputSupport wireSupport) prior


/-- The input support of every input or gate wire in a program. -/
def Program.wireSupport
    (program : Program σ n g) : Wire n g → Finset (Fin n) :=
  Wire.elim (fun k => {k}) program.gateSupport


/-- An input wire is supported only by that input. -/
@[simp] theorem Program.wireSupport_input
    (program : Program σ n g)
    (input : Fin n) :
    program.wireSupport (Wire.input input) = {input} := rfl


/-- A gate-output wire has the support of that gate. -/
@[simp] theorem Program.wireSupport_gate
    (program : Program σ n g)
    (gate : Fin g) :
    program.wireSupport (Wire.gate gate) =
      program.gateSupport gate := rfl


/-- Adding a gate preserves the support of every earlier wire. -/
@[simp] theorem Program.wireSupport_gate_castSucc
    (program : Program σ n g)
    (line : Line σ n g)
    (wire : Wire n g) :
    (program.gate line).wireSupport wire.castSucc = program.wireSupport wire := by
  cases wire with
  | input i => rfl
  | gate j => simp [Program.wireSupport, Program.gateSupport]


/-- The new gate is supported by precisely the inputs supporting the new line. -/
@[simp] theorem Program.gateSupport_gate_last
    (program : Program σ n g)
    (line : Line σ n g) :
    (program.gate line).gateSupport (Fin.last g) =
      line.inputSupport program.wireSupport := by
  simp only [Program.wireSupport, Program.gateSupport, Fin.lastCases_last]


/-- The new wire is supported by precisely the inputs supporting the new line. -/
theorem Program.wireSupport_gate_last
    (program : Program σ n g)
    (line : Line σ n g) :
    (program.gate line).wireSupport (Wire.gate (Fin.last g)) =
      line.inputSupport program.wireSupport := by
  simp only [Program.wireSupport, Program.gateSupport, Wire.elim_gate, Fin.lastCases_last]


/-- The input support of every designated output wire in a circuit. -/
def Circuit.outputSupport
    (c : Circuit σ n m) : Fin m → Finset (Fin n) :=
  c.program.wireSupport ∘ c.outputs


/-- The union of the input supports of a circuit's outputs. -/
def Circuit.inputSupport (c : Circuit σ n m) : Finset (Fin n) :=
  Finset.univ.biUnion c.outputSupport


/-- An input supports a circuit exactly when it supports a designated output wire. -/
@[simp] theorem Circuit.mem_inputSupport
    {c : Circuit σ n m}
    {input : Fin n} :
    input ∈ c.inputSupport ↔
      ∃ output, input ∈ c.program.wireSupport (c.outputs output) := by
  simp [Circuit.inputSupport, Circuit.outputSupport]


/-- Program gates agree whenever their supporting inputs agree. -/
theorem Program.eval_congr
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (left right : Fin n → U)
    (k : Fin g)
    (agree : ∀ i ∈ program.gateSupport k, left i = right i) :
    program.eval interpretation left k = program.eval interpretation right k := by
  induction program with
  | empty => exact Fin.elim0 k
  | @gate g program line ih =>
      revert agree
      refine Fin.lastCases ?_ (fun j => ?_) k
      · intro agree
        simp only [Program.eval, Fin.lastCases_last]
        unfold Line.eval
        congr 1
        funext argument
        simp only [Function.comp_apply]
        let wireSupport : Wire n g → Finset (Fin n) :=
          Wire.elim (fun k => {k}) program.gateSupport
        have agreeOnLine :
            ∀ i ∈ line.inputSupport wireSupport, left i = right i := by
          simpa [Program.gateSupport] using agree
        have wireValueEqual (wire : Wire n g) :
            (∀ i ∈ wireSupport wire, left i = right i) →
            (Wire.elim left (program.eval interpretation left) wire : U) =
              (Wire.elim right (program.eval interpretation right) wire : U) := by
          cases wire with
          | input i =>
              intro h
              simpa using h i (by simp [wireSupport])
          | gate j =>
              intro h
              simpa using ih j (fun i hi =>
                h i (by simpa [wireSupport] using hi))
        exact wireValueEqual (line.wires argument) fun i hi =>
          agreeOnLine i (Line.mem_inputSupport.mpr ⟨argument, hi⟩)
      · intro agree
        simp only [Program.eval, Fin.lastCases_castSucc]
        apply ih j
        simpa [Program.gateSupport] using agree


/-- Program traces agree on any wire whose supporting inputs agree. -/
theorem Program.trace_congr
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (left right : Fin n → U)
    (wire : Wire n g)
    (agree : ∀ i ∈ program.wireSupport wire, left i = right i) :
    program.trace interpretation left wire =
      program.trace interpretation right wire := by
  unfold Program.trace
  revert agree
  cases wire with
  | input input =>
    intro agree
    simpa using agree input (by simp [Program.wireSupport])
  | gate gate =>
    intro agree
    simp only [Wire.elim_gate]
    apply program.eval_congr interpretation left right gate
    intro input present
    exact agree input (by simpa [Program.wireSupport] using present)


/-- Circuit evaluation depends only on the circuit's structural input support. -/
theorem Circuit.dependsOn_eval
    (c : Circuit σ n m)
    (interpretation : Interpretation σ U) :
    DependsOn (c.eval interpretation) (c.inputSupport : Set (Fin n)) := by
  intro left right agree
  funext output
  apply c.program.trace_congr interpretation left right (c.outputs output)
  intro input present
  exact agree input (Circuit.mem_inputSupport.mpr ⟨output, present⟩)


/-- A computed function depends only on the circuit's structural input support. -/
theorem Circuit.Computes.dependsOn
    {c : Circuit σ n m}
    {interpretation : Interpretation σ U}
    {target : (Fin n → U) → Fin m → U}
    (computes : c.Computes interpretation target) :
    DependsOn target (c.inputSupport : Set (Fin n)) := by
  intro left right agree
  rw [← computes left, ← computes right]
  exact c.dependsOn_eval interpretation agree


end Cslib.Circuits
