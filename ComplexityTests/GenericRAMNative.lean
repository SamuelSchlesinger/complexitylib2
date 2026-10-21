/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.GenericRAM.Native.Nat
public import Complexity.Computability.WordRAM.Native
import Complexity.Tactic.PolyTime
import Mathlib.Data.Fin.VecNotation

/-!
# Native RAM primitive certificates

Complete bundle nonvacuity, native computability without efficiency assumptions, polynomial
composition and automation, and distinct fault paths in checked scalar/instruction semantics.
-/

@[expose] public section

namespace ComplexityTests.GenericRAMNative

open Cslib.GenericRAM Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
open BoundedNat

-- The bundle exists for an infinite runtime input domain, with every field polynomial.
/-- The complete scalar bundle has a concrete native implementation. -/
theorem nativePrimitives_nonempty : Nonempty (model.NativePrimitives encoding) := ⟨nativePrimitives⟩
example (c : ℕ) : (nativePrimitives.constant c).IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial (constant_polyTime c)
example (op : model.operations.Op) : (nativePrimitives.operation op).IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial (operation_polyTime op)
example (t : model.tests.Op) : (nativePrimitives.test t).IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial (test_polyTime t)
example : nativePrimitives.address.IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial address_polyTime
example : nativePrimitives.validMove.IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial validMove_polyTime
example : nativePrimitives.validPC.IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial validPC_polyTime

-- Pure native computability suffices for arbitrary-bound certification.
example {α β : Type} (f : α → β) (ei : α ↪ List Bool) (eo : β ↪ List Bool)
    (h : IsComputable f ei eo) : Nonempty (NativeCertificate f ei eo) :=
  NativeCertificate.nonempty_iff_isComputable.mpr h

-- Recover actual native machine existence, not a RAM implementation axiom.
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State),
    ∀ p, tm.Computes (encPair encNat encNat p) (encOption encNat (model.address p.1 p.2)) :=
  isComputable_iff.mp nativePrimitives.address.isComputable

-- Composition exposes the intermediate-dependent bounds and remains polynomial.
private noncomputable def present : NativeCertificate
    (fun x : Option ℕ => x.isSome) (encOption encNat) encBool :=
  .ofPolyTime (optionIsSome (of_eq fun _ => rfl))

private noncomputable def addressAccepted := present.comp nativePrimitives.address

example (p : ℕ × ℕ) : addressAccepted.time p =
    nativePrimitives.address.time p + present.time (model.address p.1 p.2) := rfl
example : addressAccepted.IsPolynomial :=
  present.comp_isPolynomial nativePrimitives.address
    (NativeCertificate.ofPolyTime_isPolynomial (optionIsSome (of_eq fun _ => rfl)))
    (NativeCertificate.ofPolyTime_isPolynomial address_polyTime)
example : IsComputable (fun p => (model.address p.1 p.2).isSome)
    (encPair encNat encNat) encBool := addressAccepted.isComputable

-- Named certificates are reused without unfolding their implementations.
example : ComputableTidilyInPolyTime (model.checkedOp ())
    (encPair encNat (encPi encNat)) (encOption encNat) := by polytime
example : ComputableTidilyInPolyTime
    (fun k => (model.checkedConstant 7 k).getD 0) encNat encNat := by polytime
example : ComputableTidilyInPolyTime
    (Cslib.WordRAM.Basis.standard.genericModel.checkedOp (.bin .add))
    (encPair encUnary (encPi encNat)) (encOption encNat) := by polytime

-- Literals, results, tests, addresses, moves and labels have live rejection paths.
example : model.checkedConstant 3 4 = some 3 := by decide
example : model.checkedConstant 4 4 = none := by decide
example : model.checkedConstant 0 0 = none := by decide
example : model.checkedOp () (8, ![3, 4]) = some 7 := by decide
example : model.checkedOp () (7, ![3, 4]) = none := by decide
example : model.evalTest 8 () ![3, 4] = some true := by decide
example : model.evalTest 8 () ![4, 3] = some false := by decide
example : model.evalTest 8 () ![8, 3] = none := by decide
example : model.evalTest 8 () ![3, 8] = none := by decide
example : model.address 4 3 = some 3 := by decide
example : model.address 4 4 = none := by decide
example : model.validMove 4 3 = true ∧ model.validMove 4 4 = false := by decide
example : model.validPC 4 3 = true ∧ model.validPC 4 4 = false := by decide

private def data (a v : ℕ) : Data model 2 := ⟨![a, v], fun _ => v⟩

-- Loads reject either failed address extraction or invalid loaded values.
example : (Op.load 1 0).eval (M := model) 4 (data 4 0) = none := rfl
example : (Op.load 1 0).eval (M := model) 4 (data 0 4) = none := rfl
-- Stores and copies validate their source; halt checks its output.
example : (Op.store 0 1).eval (M := model) 4 (data 0 4) = none := rfl
example : (Op.copy 0 1).eval (M := model) 4 (data 0 4) = none := rfl
example : Cslib.GenericRAM.step (M := model) 4 [.halt 1]
    (⟨0, data 0 4⟩ : State model 2) = .fault := rfl
-- Validate current PC and jump destination, and fault rather than take a false branch.
example : Cslib.GenericRAM.step (M := model) 0 [.halt 0]
    (⟨0, data 0 0⟩ : State model 2) = .fault := rfl
example : Cslib.GenericRAM.step (M := model) 4 [.jump 4]
    (⟨0, data 0 0⟩ : State model 2) = .fault := rfl
example : Cslib.GenericRAM.step (M := model) 4 [.branch (.test () ![0, 1]) 0]
    (⟨0, data 0 4⟩ : State model 2) = .fault := rfl
example : run (M := model) 4 [.branch (.test () ![0, 1]) 0, .halt 1] 2
    (⟨0, data 2 1⟩ : State model 2) = some (1, 2) := rfl

-- Constants and ALU checks are connected to the existing instruction semantics.
example (k : ℕ) (x : Data model 2) :
    (Op.alu () 0 ![0, 1]).eval k x =
      (model.checkedOp () (k, x.regs ∘ ![0, 1])).map (x.set 0) :=
  Model.eval_alu_eq_map_checkedOp ..

-- WordRAM uses an exclusive bound 2^w, so width zero still admits zero.
private abbrev word := Cslib.WordRAM.Basis.standard.genericModel
example : word.checkedOp (.bin .add) (0, ![0, 0]) = some 0 := by decide
example : word.checkedOp (.bin .add) (0, ![0, 1]) = none := by decide
example : word.checkedOp (.bin .add) (2, ![1, 2]) = some 3 := by decide
example : word.checkedOp (.bin .add) (2, ![2, 2]) = none := by decide
example : word.checkedOp (.bin .add) (3, ![2, 2]) = some 4 := by decide
example : Cslib.WordRAM.checkedAddCertificate.IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial Cslib.WordRAM.checkedAdd_polyTime

/--
info: 'Cslib.GenericRAM.NativeCertificate.nonempty_iff_isComputable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeCertificate.nonempty_iff_isComputable
/--
info: 'Cslib.GenericRAM.NativeCertificate.comp_isPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeCertificate.comp_isPolynomial
/--
info: 'Cslib.GenericRAM.BoundedNat.nativePrimitives' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BoundedNat.nativePrimitives
/--
info: 'Cslib.WordRAM.checkedAdd_polyTime' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.checkedAdd_polyTime

end ComplexityTests.GenericRAMNative
