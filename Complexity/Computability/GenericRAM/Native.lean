/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Defs
public import Complexity.Computability.Machines.Turing.MultiTape.Halting.Computable
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option

/-!
# Native certificates for RAM primitives

A `NativeCertificate` records arbitrary input-dependent time and space bounds, including the
encoded output size, for an actual finite native multi-tape machine. `Model.NativePrimitives`
collects these certificates for the scalar obligations of a RAM model. Configuration and all
operands are encoded runtime inputs; a single machine handles all of them for each fixed symbol.
Constants may depend on the symbol, and hence on a fixed finite source program. Symbols themselves
are not encoded inputs: this is not a uniform interpreter for arbitrary programs.

The semantic `Model` remains independent of finite encodings. In particular, this interface does
not require an exact real RAM to admit a bit representation. It also supplies neither a memory
representation nor a whole-machine simulation. Loads/stores still require charged lookup/update;
control, initialization and output require their own certificates. Deriving an input-only bound
from a configuration-and-input bound additionally requires charged, computable configuration
selection and an input-fit guarantee, rather than instance-dependent width advice.

## Main definitions

* `NativeCertificate`: native implementation with arbitrary resource bounds.
* `Model.Encoding`: selectable encodings of values, addresses and configuration.
* `Model.checkedConstant`, `Model.checkedOp`: include the result admissibility check.
* `Model.NativePrimitives`: scalar obligations, including move and control-label validation.

## Main results

* `NativeCertificate.nonempty_iff_isComputable`: arbitrary-bound certificates exist exactly for
  native computable functions.
* `NativeCertificate.isComputable`: forget the resource bounds.
* `NativeCertificate.polyTime`: obtain polynomial time under separate polynomial bounds.
* `NativeCertificate.comp`: compose certificates with input-dependent resource accounting.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.GenericRAM

open Turing.MultiTapeTM

/-- An actual native implementation, with bounds also charging its encoded output length. -/
structure NativeCertificate {α β : Type} (f : α → β)
    (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) where
  /-- Input-dependent time bound, up to a constant factor and additive constant. -/
  time : α → ℕ
  /-- Input-dependent work space and encoded output bound, up to constants. -/
  space : α → ℕ
  /-- One finite machine implements the function on every encoded input. -/
  computes : ComputableTidilyInO f encIn encOut time space

namespace NativeCertificate

variable {α β γ : Type} {f : α → β} {g : β → γ}
  {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}

/-- Forgetting resource bounds retains native computability. -/
theorem isComputable (c : NativeCertificate f encIn encMid) :
    IsComputable f encIn encMid := c.computes.isComputable

/-- Polynomiality is a separate property of both bounds in the encoded input length. -/
def IsPolynomial (c : NativeCertificate f encIn encMid) : Prop :=
  PolyBounded (fun a => (encIn a).length) c.time ∧
    PolyBounded (fun a => (encIn a).length) c.space

/-- Derive the existing native polynomial-time predicate, for use by its compositional calculus. -/
theorem polyTime (c : NativeCertificate f encIn encMid) (h : c.IsPolynomial) :
    ComputableTidilyInPolyTime f encIn encMid :=
  c.computes.computableTidilyInPolyTime h.1 h.2

/-- Compose implementations, charging the second bound at the first result. -/
def comp (d : NativeCertificate g encMid encOut) (c : NativeCertificate f encIn encMid) :
    NativeCertificate (g ∘ f) encIn encOut where
  time a := c.time a + d.time (f a)
  space a := c.space a + d.space (f a)
  computes := d.computes.comp c.computes

/-- Composing polynomial certificates preserves polynomiality in the original input encoding. -/
theorem comp_isPolynomial (d : NativeCertificate g encMid encOut)
    (c : NativeCertificate f encIn encMid) (hd : d.IsPolynomial) (hc : c.IsPolynomial) :
    (d.comp c).IsPolynomial :=
  ⟨hc.1.add (hd.1.comp (c.polyTime hc).polyBounded_length),
    hc.2.add (hd.2.comp (c.polyTime hc).polyBounded_length)⟩

/-- Package exact native bounds, including the running time in the space allowance to charge
encoded output length. No polynomial hypothesis is needed. -/
def ofTimeAndSpace {t s : α → ℕ}
    (h : ComputableTidilyInTimeAndSpace f encIn encMid t s) :
    NativeCertificate f encIn encMid where
  time := t
  space a := s a + t a
  computes := .of_bounds h 1 (fun _ => by simp)
    (fun _ => by simp; omega) (fun a => by
      have := h.length_le a
      simp only [one_mul]
      omega)

/-- Arbitrary-bound certificates impose exactly native computability, not an efficiency
assumption. Polynomial resource bounds remain a separate property. -/
theorem nonempty_iff_isComputable :
    Nonempty (NativeCertificate f encIn encMid) ↔ IsComputable f encIn encMid := by
  refine ⟨fun ⟨c⟩ => c.isComputable, fun h => ?_⟩
  obtain ⟨t, s, h⟩ := h.exists_computableTidilyInTimeAndSpace
  exact ⟨ofTimeAndSpace h⟩

/-- Every native polynomial-time proof supplies a certificate with polynomial bounds. The space
bound includes the running time so that it also bounds the emitted output. -/
theorem exists_polynomial (h : ComputableTidilyInPolyTime f encIn encMid) :
    ∃ c : NativeCertificate f encIn encMid, c.IsPolynomial := by
  obtain ⟨t, s, ht, hs, hf⟩ := h
  exact ⟨ofTimeAndSpace hf, ht, hs.add ht⟩

/-- Select resource bounds from an existing polynomial-time implementation proof. -/
noncomputable def ofPolyTime (h : ComputableTidilyInPolyTime f encIn encMid) :
    NativeCertificate f encIn encMid := (exists_polynomial h).choose

/-- Bounds selected by `ofPolyTime` are polynomial in the encoded input length. -/
theorem ofPolyTime_isPolynomial (h : ComputableTidilyInPolyTime f encIn encMid) :
    (ofPolyTime h).IsPolynomial := (exists_polynomial h).choose_spec

end NativeCertificate

namespace Model

/-- Finite bit representations are separate from the semantic model. Configuration encoding is
chosen explicitly; in particular, unary and binary widths have different resource costs. -/
structure Encoding (M : Model.{0, 0, 0, 0}) where
  /-- Encoding of register and memory values. -/
  value : M.Value ↪ List Bool
  /-- Encoding of memory addresses. -/
  address : M.Address ↪ List Bool
  /-- Encoding of runtime model parameters, including any word width. -/
  config : M.Config ↪ List Bool

variable {M : Model.{0, 0, 0, 0}}

/-- A fixed literal's result, including the admissibility check performed by `Data.put`. -/
def checkedConstant (M : Model) (c : M.Const) (k : M.Config) : Option M.Value :=
  (M.constant k c).bind fun v => if M.admissible k v then some v else none

/-- A fixed operation's result, including the admissibility check performed by `Data.put`.
A native implementation can reject overflow without materializing the unchecked result. -/
def checkedOp (M : Model) (op : M.operations.Op)
    (p : M.Config × (Fin (M.operations.Arity op) → M.Value)) : Option M.Value :=
  (M.evalOp p.1 op p.2).bind fun v => if M.admissible p.1 v then some v else none

/-- A constant instruction stores exactly the checked literal result, preserving faults. -/
theorem eval_const_eq_map_checkedConstant {r : ℕ} (k : M.Config) (x : Data M r)
    (d : Fin r) (c : M.Const) :
    (Op.const d c).eval k x = (M.checkedConstant c k).map (x.set d) := by
  cases h : M.constant k c with
  | none => simp [Op.eval, checkedConstant, h]
  | some v =>
    simp only [Op.eval, checkedConstant, h, Option.bind_some, Data.put]
    split <;> rfl

/-- An ALU instruction stores exactly the checked operation result, preserving faults. -/
theorem eval_alu_eq_map_checkedOp {r : ℕ} (k : M.Config) (x : Data M r)
    (op : M.operations.Op) (d : Fin r) (args : Fin (M.operations.Arity op) → Fin r) :
    (Op.alu op d args).eval k x = (M.checkedOp op (k, x.regs ∘ args)).map (x.set d) := by
  cases h : M.evalOp k op (x.regs ∘ args) with
  | none => simp [Op.eval, checkedOp, h]
  | some v =>
    simp only [Op.eval, checkedOp, h, Option.bind_some, Data.put]
    split <;> rfl

/-- Scalar certificates needed by a fixed-program RAM simulation. Memory lookup/update and
finite-program dispatch are additional obligations. There is no uniform symbol dispatcher here. -/
structure NativePrimitives (M : Model.{0, 0, 0, 0}) (enc : Encoding M) where
  /-- Literal symbols are fixed; configuration varies over every encoded input. -/
  constant : ∀ c, NativeCertificate (M.checkedConstant c) enc.config (encOption enc.value)
  /-- Operation symbols are fixed; configuration and all operands are runtime inputs. -/
  operation : ∀ op, NativeCertificate (M.checkedOp op)
    (encPair enc.config (encPi enc.value)) (encOption enc.value)
  /-- Tests preserve the distinction between fault, false and true. -/
  test : ∀ t, NativeCertificate (fun p => M.evalTest p.1 t p.2)
    (encPair enc.config (encPi enc.value)) (encOption encBool)
  /-- Address extraction can fault independently of move validation. -/
  address : NativeCertificate (fun p => M.address p.1 p.2)
    (encPair enc.config enc.value) (encOption enc.address)
  /-- Copy/load/store/halt validate existing values through this predicate. -/
  validMove : NativeCertificate (fun p => M.validMove p.1 p.2)
    (encPair enc.config enc.value) encBool
  /-- Current and continuing control labels both require validation. -/
  validPC : NativeCertificate (fun p => M.validPC p.1 p.2)
    (encPair enc.config encNat) encBool

end Model
end Cslib.GenericRAM
