/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Multiparty.ObliviousTransfer

/-!
# Tests: Completeness of Oblivious Transfer

Concrete 2-party and 3-party circuit functionalities (including 2-party AND, 2-party XOR, and
3-party AND against a dishonest majority `C = {0, 2}`), a non-vacuous `PolyTimeFunctionality`
instance, tests of non-fairness and abort, and axiom checks for the headline theorems.
-/

namespace ComplexityTests.Crypto.ObliviousTransfer

open Cslib Cslib.Circuits Cslib.Crypto Cslib.Crypto.Multiparty Cslib.Probability Turing.MultiTapeTM
open scoped Cslib.Probability.PMF

/-- Explicit 1-gate De Morgan circuit on 2 inputs and 2 outputs computing the 2-party AND
functionality `(x₀, x₁) ↦ (x₀ && x₁, x₀ && x₁)`. -/
private def twoPartyAndCircuit : Circuit Boolean.signature (2 * 1) (2 * 1) :=
  let p0 : Program Boolean.signature 2 0 := .empty
  let l0 : Line Boolean.signature 2 0 := ⟨.and, ![.input 0, .input 1]⟩
  ⟨p0.gate l0, fun _ => .gate 0⟩

example (inputs : Fin 2 → BitString 1) (p : Fin 2) (b : Fin 1) :
    circuitFunctionality twoPartyAndCircuit inputs p b = (inputs 0 0 && inputs 1 0) := by
  revert inputs p b
  decide

/-- Explicit 2-gate De Morgan circuit on 3 inputs and 3 outputs computing the 3-party AND
functionality `(x₀, x₁, x₂) ↦ (x₀ && x₁ && x₂, ...)`. -/
private def threePartyAndCircuit : Circuit Boolean.signature (3 * 1) (3 * 1) :=
  let p0 : Program Boolean.signature 3 0 := .empty
  let l0 : Line Boolean.signature 3 0 := ⟨.and, ![.input 0, .input 1]⟩
  let p1 : Program Boolean.signature 3 1 := p0.gate l0
  let l1 : Line Boolean.signature 3 1 := ⟨.and, ![.gate 0, .input 2]⟩
  ⟨p1.gate l1, fun _ => .gate 1⟩

example (inputs : Fin 3 → BitString 1) (p : Fin 3) (b : Fin 1) :
    circuitFunctionality threePartyAndCircuit inputs p b =
      ((inputs 0 0 && inputs 1 0) && inputs 2 0) := by
  revert inputs p b
  decide

/-- Real/ideal simulation holds against a dishonest majority `C = {0, 2}` (2 of 3 parties
corrupted) in the 3-party AND protocol. -/
example (A : MaliciousOTAdversary 3 1 1 threePartyAndCircuit.size (List Bool))
    (inputs : Fin 3 → BitString 1) :
    realOTHybridExecution threePartyAndCircuit ({0, 2} : Finset (Fin 3)) A inputs =
      idealExecutionWithAbort (circuitFunctionality threePartyAndCircuit)
        ({0, 2} : Finset (Fin 3))
        (kilianSimulator ({0, 2} : Finset (Fin 3)) threePartyAndCircuit A) inputs :=
  realOTHybridExecution_eq_idealExecutionWithAbort threePartyAndCircuit {0, 2} A inputs

/-- Non-vacuous `PolyTimeFunctionality` instance for the 2-party XOR functionality family. -/
private def twoPartyXorPolyTime : PolyTimeFunctionality 2 where
  inWidth := fun _ => 1
  outWidth := fun _ => 1
  circuit := fun _ => twoPartyXorCircuit
  poly_inWidth := PolynomiallyBounded.const 1
  poly_outWidth := PolynomiallyBounded.const 1
  poly_size := PolynomiallyBounded.const twoPartyXorCircuit.size

example : ComputationallySecureWithAbort twoPartyXorPolyTime :=
  ot_complete_computationallySecureWithAbort twoPartyXorPolyTime

example : PolynomiallyBounded (fun n => otCallBudget 2 (twoPartyXorPolyTime.circuit n)) :=
  twoPartyXorPolyTime.polynomiallyBounded_otCallBudget

/-- On abort, honest party `1` is not guaranteed output delivery in 2-party AND. -/
example (inputs : Fin 2 → BitString 1) :
    ¬ GuaranteedOutputDelivery ({0} : Finset (Fin 2))
      (realOTHybridExecution twoPartyAndCircuit ({0} : Finset (Fin 2))
        (abortingAdversary 2 1 1 twoPartyAndCircuit.size) inputs) :=
  not_guaranteedOutputDelivery_of_abort twoPartyAndCircuit {0} ⟨1, by decide⟩ inputs

/-- Rushing unfair adversary in 2-party XOR learns party 1's input while party 1 gets `none`. -/
example (inputs : Fin 2 → BitString 1) :
    realOTHybridExecution twoPartyXorCircuit ({0} : Finset (Fin 2)) unfairXorAdversary inputs =
      PMF.pure (fun _ => none, inputs 1 0) :=
  unfair_twoPartyXor_execution inputs

/-! ### Axioms of the headline theorems -/

/--
info: 'Cslib.Crypto.Multiparty.otAndShare_uniform' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Multiparty.otAndShare_uniform

/--
info: 'Cslib.Crypto.Multiparty.parity_shareAnd' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Multiparty.parity_shareAnd

/--
info: 'Cslib.Crypto.Multiparty.parity_evalCircuitOT' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Multiparty.parity_evalCircuitOT

/--
info: 'Cslib.Crypto.Multiparty.realOTHybridExecution_eq_idealExecutionWithAbort' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Multiparty.realOTHybridExecution_eq_idealExecutionWithAbort

/--
info: 'Cslib.Crypto.Multiparty.dist_realOTHybridExecution_idealExecutionWithAbort' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Multiparty.dist_realOTHybridExecution_idealExecutionWithAbort

/--
info: 'Cslib.Crypto.Multiparty.ot_complete_statisticallySecureWithAbort' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Multiparty.ot_complete_statisticallySecureWithAbort

/--
info: 'Cslib.Crypto.Multiparty.ot_complete_computationallySecureWithAbort' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Multiparty.ot_complete_computationallySecureWithAbort

/--
info: 'Cslib.Crypto.Multiparty.PolyTimeFunctionality.polynomiallyBounded_otCallBudget' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Multiparty.PolyTimeFunctionality.polynomiallyBounded_otCallBudget

/--
info: 'Cslib.Crypto.Multiparty.PolyTimeFunctionality.circuitFunctionality_apply_eq_evalOutput'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Multiparty.PolyTimeFunctionality.circuitFunctionality_apply_eq_evalOutput

/--
info: 'Cslib.Crypto.Multiparty.not_guaranteedOutputDelivery_of_abort' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Multiparty.not_guaranteedOutputDelivery_of_abort

/--
info: 'Cslib.Crypto.Multiparty.unfair_twoPartyXor_execution' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Multiparty.unfair_twoPartyXor_execution

/--
info: 'Cslib.Crypto.Multiparty.cleve_unfair_fallback' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Multiparty.cleve_unfair_fallback

end ComplexityTests.Crypto.ObliviousTransfer
