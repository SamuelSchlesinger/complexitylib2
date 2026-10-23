/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
import Mathlib.Data.List.GetD

/-!
# Boolean circuits scheduled in layers

Each node reads only the preceding layer. Constants allow evaluation with no input wires;
copies carry values across layers; NAND nodes may read a wire twice. The last layer supplies
all outputs, and the empty program preserves all inputs. Wire indices have binary encodings.

The number of scheduled layers counts copies and empty layers too. It is not identified here
with the depth of a De Morgan circuit. A conversion from ordinary circuits, with its size and
depth guarantees, is separate work.

## Main definitions

* `Cslib.Circuits.Boolean.Layered.Node`: constants, copies and NANDs.
* `Cslib.Circuits.Boolean.Layered.eval`: evaluation of a list of layers.
* `Cslib.Circuits.Boolean.Layered.WellFormed`: all references read the preceding layer.
* `Cslib.Circuits.Boolean.Layered.encNode`: two tag bits and binary wire indices.

## References

The consecutive-layer presentation, including inserted copy gates, is used in
[C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2][Gentry2009].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Layered

open Turing.MultiTapeTM

/-- A node whose inputs are positions in the preceding layer. -/
inductive Node where
  | const (value : Bool)
  | copy (wire : ℕ)
  | nand (first second : ℕ)
  deriving DecidableEq

/-- The two tag bits distinguish the four operations; unused wire positions are zero. -/
def Node.code : Node → (Bool × Bool) × ℕ × ℕ
  | .const b => ((false, b), 0, 0)
  | .copy i => ((true, false), i, 0)
  | .nand i j => ((true, true), i, j)

theorem Node.code_injective : Function.Injective Node.code := by
  intro a b h
  cases a <;> cases b <;> simp_all [Node.code]

/-- Encode nodes with two operation bits and binary wire indices, including invalid indices. -/
def encNode : Node ↪ List Bool :=
  ⟨fun node => encPair (encPair encBool encBool) (encPair encNat encNat) node.code,
    (encPair (encPair encBool encBool) (encPair encNat encNat)).injective.comp
      Node.code_injective⟩

/-- A node is valid when each of its references exists in the preceding layer. -/
def Node.Valid (width : ℕ) : Node → Prop
  | .const _ => True
  | .copy i => i < width
  | .nand i j => i < width ∧ j < width

/-- Evaluate one node. Invalid references read `false`; correctness of a client interpreter
may require `Node.Valid` rather than preserving this fallback. -/
def Node.eval (inputs : List Bool) : Node → Bool
  | .const b => b
  | .copy i => inputs.getD i false
  | .nand i j => !(inputs.getD i false && inputs.getD j false)

/-- Evaluate a layer, preserving its order and repeated references. -/
def evalLayer (inputs : List Bool) (layer : List Node) : List Bool :=
  layer.map (Node.eval inputs)

@[simp] theorem length_evalLayer (inputs : List Bool) (layer : List Node) :
    (evalLayer inputs layer).length = layer.length := List.length_map _

/-- Execute the layers in order. No layers means identity, including on an empty input. -/
def eval (inputs : List Bool) : List (List Node) → List Bool
  | [] => inputs
  | layer :: layers => eval (evalLayer inputs layer) layers

@[simp] theorem eval_nil (inputs : List Bool) : eval inputs [] = inputs := rfl

@[simp] theorem eval_cons (inputs : List Bool) (layer : List Node) (layers : List (List Node)) :
    eval inputs (layer :: layers) = eval (evalLayer inputs layer) layers := rfl

theorem eval_append (inputs : List Bool) (first second : List (List Node)) :
    eval inputs (first ++ second) = eval (eval inputs first) second := by
  induction first generalizing inputs with
  | nil => rfl
  | cons layer layers ih => exact ih (evalLayer inputs layer)

/-- Extending a prefix executes precisely its next scheduled layer. -/
theorem eval_take_succ (inputs : List Bool) (layers : List (List Node)) {i : ℕ}
    (hi : i < layers.length) :
    eval inputs (layers.take (i + 1)) =
      evalLayer (eval inputs (layers.take i)) (layers.getD i []) := by
  rw [List.take_succ_eq_append_getElem hi, eval_append, eval_cons, eval_nil,
    List.getD_eq_getElem _ _ hi]

/-- All references are in range in the immediately preceding layer. -/
def WellFormed (inputCount : ℕ) : List (List Node) → Prop
  | [] => True
  | layer :: layers => (∀ node ∈ layer, node.Valid inputCount) ∧ WellFormed layer.length layers

@[simp] theorem wellFormed_nil (inputCount : ℕ) : WellFormed inputCount [] := trivial

@[simp] theorem wellFormed_cons (inputCount : ℕ) (layer : List Node)
    (layers : List (List Node)) :
    WellFormed inputCount (layer :: layers) ↔
      (∀ node ∈ layer, node.Valid inputCount) ∧ WellFormed layer.length layers := Iff.rfl

/-- Each scheduled layer reads valid wires of the evaluated prefix. -/
theorem WellFormed.valid_getD {inputs : List Bool} {layers : List (List Node)}
    (h : WellFormed inputs.length layers) {i : ℕ} (hi : i < layers.length) :
    ∀ node ∈ layers.getD i [], node.Valid (eval inputs (layers.take i)).length := by
  induction layers generalizing inputs i with
  | nil => simp at hi
  | cons layer layers ih =>
    cases i with
    | zero => simpa only [List.getD_cons_zero, List.take_zero, eval_nil] using h.1
    | succ i =>
      have htail : WellFormed (evalLayer inputs layer).length layers := by
        simpa only [length_evalLayer] using h.2
      simpa only [List.getD_cons_succ, List.take_succ_cons, eval_cons] using
        ih htail (Nat.lt_of_succ_lt_succ hi)

end Cslib.Circuits.Boolean.Layered
