/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Iteration.AffineController

/-!
# Tests for autonomous controllers and affine-payload iteration bounds

Exercises `controlledMap_iterate`, `controlledBits_iterate`, `controlled_circuit`,
`affineHash_circuit`, `affineHash_affineMapSeed`, `affine_payload_circuit`,
`affine_controller_power` (for zero-width and positive-width controllers and payloads),
`affine_controller_polynomial`, and `affine_controller_variable_time`, together with `#print axioms`
guards for the headline theorems.
-/

namespace ComplexityTests.AffineController

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Iteration
open Cslib.BitString.LinearHash

/-! ### Autonomous controllers and composite payloads -/

-- Iterating a controlled map on `Bool × Bool` where controller flips and payload XORs controller.
example : (controlledMap Bool.not (fun u v => u ^^ v))^[3] (false, true) = (true, false) := by
  rw [controlledMap_iterate]
  decide

-- Flat Boolean encoding of controller followed by payload agrees on appended vectors.
example (u : BitString 1) (v : BitString 2) :
    controlledBits id (fun _ w => w) (Fin.append u v) = Fin.append u v := by
  simp

-- Iterating `controlledBits` equals `controlledBits` of the iterated controller and composite
-- payload.
example (T : ℕ) (x : BitString (1 + 2)) :
    (controlledBits (q := 1) (p := 2) id (fun _ v => v))^[T] x =
      controlledBits (id^[T]) (controlledPayload id (fun _ v => v) T) x :=
  controlledBits_iterate id (fun _ v => v) T x

-- Selecting trivial identity payload circuits for a 1-bit autonomous controller.
example (g : BitString 1 → BitString 1) :
    ∃ c : Circuit signature (1 + 2) (1 + 2),
      c.Computes interpretation (controlledBits g (fun _ v => v)) ∧
      c.size ≤ 2 + 2 ^ 1 * (0 + 6 * 1 + 4 * 2 + 1) :=
  controlled_circuit g (fun _ v => v) 0 fun _ =>
    ⟨Circuit.id signature 2, fun _ => rfl, by simp⟩

/-! ### Affine hashes and affine payloads -/

-- Every 2×2 affine hash has a De Morgan circuit of size at most `2 * (5 * 3 + 1) = 32`.
example (seed : (Fin 2 → BitString 2) × BitString 2) :
    ∃ c : Circuit signature 2 2,
      c.Computes interpretation (affineHash seed) ∧ c.size ≤ 32 := by
  simpa using affineHash_circuit seed

-- Evaluating `affineHash` on `affineMapSeed` of an affine translation recovers the translation.
example (b v : BitString 2) :
    affineHash (affineMapSeed (AffineMap.const Bool (BitString 2) b +
      AffineMap.id Bool (BitString 2))) v = b + v :=
  affineHash_affineMapSeed _ v

-- Identity affine payload on 2 bits has a circuit of size at most `2 * (5 * 3 + 1) = 32`.
example : ∃ c : Circuit signature 2 2,
    c.Computes interpretation (AffineMap.id Bool (BitString 2)) ∧ c.size ≤ 32 := by
  simpa using affine_payload_circuit (AffineMap.id Bool (BitString 2))

/-! ### Affine-controller iteration bounds -/

-- Zero-width controller (`q = 0`) and 2-bit affine payload: fixed power within budget 43.
example (a : BitString 0 → (BitString 2 →ᵃ[Bool] BitString 2)) (T : ℕ) :
    ∃ c : Circuit signature (0 + 2) (0 + 2),
      c.Computes interpretation ((controlledBits id (fun u => a u))^[T]) ∧
      c.size ≤ 43 := by
  simpa [affineControllerBudget] using affine_controller_power id a T

-- Positive-width controller (`q = 1`), zero-width affine payload (`p = 0`), and `T = 0`.
example (g : BitString 1 → BitString 1)
    (a : BitString 1 → (BitString 0 →ᵃ[Bool] BitString 0)) :
    ∃ c : Circuit signature (1 + 0) (1 + 0),
      c.Computes interpretation ((controlledBits g (fun u => a u))^[0]) ∧
      c.size ≤ 16 := by
  simpa [affineControllerBudget] using affine_controller_power g a 0

-- Positive-width controller (`q = 1`) and 1-bit affine payload: fixed power within budget.
example (g : BitString 1 → BitString 1)
    (a : BitString 1 → (BitString 1 →ᵃ[Bool] BitString 1)) (T : ℕ) :
    ∃ c : Circuit signature (1 + 1) (1 + 1),
      c.Computes interpretation ((controlledBits g (fun u => a u))^[T]) ∧
      c.size ≤ affineControllerBudget 1 1 :=
  affine_controller_power g a T

-- Polynomial controller bound with `2 ^ 1 ≤ 1 * (1 + 2 + 1) ^ 1`.
example (g : BitString 1 → BitString 1)
    (a : BitString 1 → (BitString 2 →ᵃ[Bool] BitString 2)) (T : ℕ) :
    ∃ c : Circuit signature (1 + 2) (1 + 2),
      c.Computes interpretation ((controlledBits g (fun u => a u))^[T]) ∧
      c.size ≤ 32 * 1 * (1 + 2 + 1) ^ (1 + 2) :=
  affine_controller_polynomial g a 1 1 (by decide) T

-- Input-time iteration of an affine-payload controlled map with `m = 0` and `m = 3` time bits.
example (g : BitString 1 → BitString 1)
    (a : BitString 1 → (BitString 2 →ᵃ[Bool] BitString 2)) :
    ∃ c : Circuit signature ((1 + 2) + 0) (1 + 2),
      c.Computes interpretation (inputTimeIterate (controlledBits g (fun u => a u)) 0) ∧
      c.size ≤ 0 := by
  simpa using affine_controller_variable_time g a 0

example (g : BitString 1 → BitString 1)
    (a : BitString 1 → (BitString 2 →ᵃ[Bool] BitString 2)) :
    ∃ c : Circuit signature ((1 + 2) + 3) (1 + 2),
      c.Computes interpretation (inputTimeIterate (controlledBits g (fun u => a u)) 3) ∧
      c.size ≤ 3 * (affineControllerBudget 1 2 + 4 * (1 + 2)) :=
  affine_controller_variable_time g a 3

/-! ### Axiom guards -/

/--
info: 'Cslib.Circuits.Boolean.Iteration.controlledMap_iterate' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms controlledMap_iterate

/--
info: 'Cslib.Circuits.Boolean.Iteration.controlledPayload_mem' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms controlledPayload_mem

/--
info: 'Cslib.Circuits.Boolean.Iteration.controlledBits_iterate' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms controlledBits_iterate

/--
info: 'Cslib.Circuits.Boolean.Iteration.controlled_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms controlled_circuit

/--
info: 'Cslib.Circuits.Boolean.Iteration.controlled_family_power' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms controlled_family_power

/--
info: 'Cslib.Circuits.Boolean.Iteration.controlled_family_variable_time' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms controlled_family_variable_time

/--
info: 'Cslib.Circuits.Boolean.Iteration.affineHash_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms affineHash_circuit

/--
info: 'Cslib.Circuits.Boolean.Iteration.affineHash_affineMapSeed' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms affineHash_affineMapSeed

/--
info: 'Cslib.Circuits.Boolean.Iteration.affine_payload_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms affine_payload_circuit

/--
info: 'Cslib.Circuits.Boolean.Iteration.affine_controller_power' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms affine_controller_power

/--
info: 'Cslib.Circuits.Boolean.Iteration.affineControllerBudget_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms affineControllerBudget_le

/--
info: 'Cslib.Circuits.Boolean.Iteration.affine_controller_polynomial' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms affine_controller_polynomial

/--
info: 'Cslib.Circuits.Boolean.Iteration.affine_controller_variable_time' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms affine_controller_variable_time

end ComplexityTests.AffineController
