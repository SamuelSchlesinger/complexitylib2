/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Iteration.CircuitCounting
import Complexity.Computability.Circuit.Boolean.Iteration.CounterBatch
import Complexity.Computability.Circuit.Boolean.Iteration.ModulusCounter
import Complexity.Computability.Circuit.Boolean.Iteration.Optimization
import Complexity.Computability.Circuit.Boolean.Iteration.Permutation
import Complexity.Computability.Circuit.Boolean.Iteration.PrimeCycles

/-!
# Fixed-power circuit clients

Exercise the word circuits on a two-bit adder and table selection, the residue correction on a
concrete repeat, record collisions, and the fixed-power theorems on a bit-flip circuit, on
zero-width states, on an empty and a singleton invariant set, through an encoding of a type in
a higher universe, and for permutation inversion and periodicity.
-/

namespace ComplexityTests.Iteration

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Iteration

/-! ### Words -/

-- A two-bit ripple-carry adder on the first two and last two inputs, from the shared carries.
example : ∃ c : Circuit signature 4 2,
    c.Computes interpretation (fun x i =>
      (word (fun j : Fin 2 => x ⟨j, by omega⟩) +
        word (fun j : Fin 2 => x ⟨j + 2, by omega⟩)).getLsbD i.val) ∧ c.size ≤ 25 :=
  (Synthesis.word_add (s := inputs 4) (fun x => word fun j : Fin 2 => x ⟨j, by omega⟩)
    (fun x => word fun j : Fin 2 => x ⟨j + 2, by omega⟩)
    (fun i => ⟨⟨i, by omega⟩, funext fun x =>
      (getLsbD_word (fun j : Fin 2 => x ⟨j, by omega⟩) i).symm⟩)
    (fun i => ⟨⟨i + 2, by omega⟩, funext fun x =>
      (getLsbD_word (fun j : Fin 2 => x ⟨j + 2, by omega⟩) i).symm⟩)).exists_circuit_outputs

-- Table selection is exact in range and all-false out of range.
example : selectBits (BitVec.ofNat 2 1) ![![true, false], ![false, true]] = ![false, true] := by
  decide

example : selectBits (BitVec.ofNat 2 3) ![![true, false], ![false, true]] = ![false, false] := by
  decide

-- Positions beyond the index range are never selected, so oversized tables do not alias.
example : selectBits (BitVec.ofNat 1 0) ![![true, false], ![false, false], ![false, true]] =
    ![true, false] := by
  decide

/-! ### Residues and records -/

-- An orbit repeating between times 2 and 5: time 10 is the time 4 in `[2, 5)`.
example : (repeatWordIndex 10 5 (BitVec.ofNat 3 2) (BitVec.ofNat 3 5)).toNat = 4 := by decide

-- Equal states collide unless a record is padding or both are identical.
example : Record.collision (Record.query (n := 1) (w := 2) ![true] 0)
    (Record.stored ![true] ![false]) = true := by decide

example : Record.collision (Record.query (n := 1) (w := 2) ![true] 0)
    (Record.query ![true] 0) = false := by decide

example : Record.collision (Record.pad (n := 1) (w := 2)) Record.pad = false := by decide

/-! ### Fixed powers -/

/-- The one-bit negation circuit. -/
private def flip : Circuit signature 1 1 :=
  ⟨.gate .empty ⟨.not, fun _ => .input 0⟩, fun _ => .gate 0⟩

private theorem eval_flip (x : BitString 1) : flip.eval interpretation x = fun _ => !x 0 := by
  funext i
  fin_cases i
  rfl

-- Every power of the flip has a circuit within the bound at `L = 1`.
example (T : ℕ) : ∃ out : Circuit signature 1 1,
    out.Computes interpretation (flip.eval interpretation)^[T] ∧
      out.size ≤ 40000 * powerBudget 1 1 2 1 := by
  simpa [flip] using fixed_power 1 flip T 1 one_pos (by decide)

-- Zero-width states: `L = 1 = 2 ^ 0` is the only parameter.
example (c : Circuit signature 0 0) (T : ℕ) : ∃ out : Circuit signature 0 0,
    out.Computes interpretation (c.eval interpretation)^[T] ∧
      out.size ≤ 40000 * (c.size + 3) := by
  simpa [powerBudget] using fixed_power 0 c T 1 one_pos le_rfl

-- The empty invariant set needs no checkpoint storage.
example (c : Circuit signature 2 2) (T : ℕ) : ∃ out : Circuit signature 2 2,
    out.ComputesOn interpretation ↑(∅ : Finset (BitString 2)) (c.eval interpretation)^[T] ∧
      out.size ≤ 40000 * powerBudget 2 c.size 0 1 :=
  fixed_power_on 2 c ∅ T 1 (by simp) one_pos (by decide)

-- A singleton invariant set: a fixed point stores at most one checkpoint.
example (c : Circuit signature 2 2) (h : c.eval interpretation ![false, false] = ![false, false])
    (T : ℕ) : ∃ out : Circuit signature 2 2,
      out.ComputesOn interpretation ↑({![false, false]} : Finset (BitString 2))
        (c.eval interpretation)^[T] ∧ out.size ≤ 40000 * powerBudget 2 c.size 1 1 :=
  fixed_power_on 2 c {![false, false]} T 1 (by simpa using h) one_pos (by decide)

/-! ### Encodings, permutations and periodicity -/

-- States in a higher universe, encoded by one bit.
example (T : ℕ) : ∃ out : Circuit signature 1 1,
    (∀ x ∈ (Finset.univ : Finset (ULift.{1} Bool)),
      out.eval interpretation (fun _ => x.down) = fun _ => (id^[T] x).down) ∧
    out.size ≤ 40000 * powerBudget 1 0 2 1 := by
  simpa using fixed_power_encoded (n := 1) id Finset.univ
    (fun (x : ULift.{1} Bool) (_ : Fin 1) => x.down)
    (fun _ _ _ _ h => ULift.ext (congrFun h 0)) (Circuit.id signature 1)
    (fun _ _ => Finset.mem_univ _) (fun _ _ => rfl) T 1 one_pos (by decide)

/-- Negation as a permutation of one-bit states. -/
private def flipPerm : Equiv.Perm (BitString 1) where
  toFun x := fun _ => !x 0
  invFun x := fun _ => !x 0
  left_inv x := funext fun i => by fin_cases i; simp
  right_inv x := funext fun i => by fin_cases i; simp

-- The flip's inverse, through the factorial exponent.
example : ∃ out : Circuit signature 1 1,
    out.Computes interpretation flipPerm.symm ∧ out.size ≤ 40000 * powerBudget 1 1 2 1 := by
  simpa [flip] using permutation_inverse flip flipPerm (fun x => eval_flip x) 1 one_pos (by decide)

-- Every state is periodic for the flip.
example : ∃ out : Circuit signature 1 1,
    (∀ x, out.eval interpretation x 0 = true ↔
      x ∈ Function.periodicPts (flip.eval interpretation)) ∧
    out.size ≤ 40000 * powerBudget 1 1 2 1 + 7 := by
  simpa [flip] using periodicPts_circuit flip 1 one_pos (by decide)

-- The half-exponential closed form.
example (c : Circuit signature 3 3) (T : ℕ) : ∃ out : Circuit signature 3 3,
    out.Computes interpretation (c.eval interpretation)^[T] ∧
      out.size ≤ 120000 * (c.size + 64) * 4 := by
  simpa using fixed_power_half_exponent c T

/-! ### Hard-power counting, modular counters and prime-cycle permutations -/

-- Linear-size circuit for the 2-bit modular-counter step.
example : ∃ c : Circuit signature (2 + 2) (2 + 2),
    c.Computes interpretation (counterStep 2) ∧ c.size ≤ 50 * 2 + 20 :=
  counterStep_circuit 2

-- Exponential lower bound for some power of the 64-bit modular counter.
example : ∃ c : Circuit signature (64 + 64) (64 + 64),
    c.size ≤ 50 * (64 + 1) ∧ Function.Bijective (c.eval interpretation) ∧
    ∃ T < ModulusCounter.period 64,
      ∀ out : Circuit signature (64 + 64) (64 + 64),
        out.Computes interpretation (c.eval interpretation)^[T] →
          2 ^ 64 / (1024 * (64 + 1)) < out.size :=
  counter_power_lower_bound 64 (by decide)

-- Almost all counter powers at width k = 64 are hard.
example : (easyCounterPowers 64 (lowerBudget 64)).card * 2 ^ (2 ^ (64 - 1)) ≤
    ModulusCounter.period 64 :=
  almost_all_counter_powers_hard 64 (by decide)

-- Least common multiple below 5 is strictly less than 4 ^ 5.
example : lcmBelow 5 < 4 ^ 5 :=
  lcmBelow_lt_four_pow 5 (by decide)

/-- Non-vacuous concrete `PrimeCycleData` instance from the hash-class construction. -/
noncomputable def samplePrimeCycleData : PrimeCycleData 1 3 :=
  PrimeCycleData.ofHash 1 1 (fun _ => 0) (fun _ => by decide)

example : Function.Bijective samplePrimeCycleData.step :=
  samplePrimeCycleData.step_bijective

-- Batched modular-counter power for r = 2 blocks of width 2 * 2 = 4.
example (T : ℕ) :
    ∃ out : Circuit signature (2 * (2 + 2)) (2 * (2 + 2)),
      out.Computes interpretation (counterBatchPower T) ∧
        out.size ≤ 40000 * (2 + 1) ^ 3 * (2 ^ 2 + 2) :=
  batched_counter_power T 2 (by decide)

-- Empty batch (r = 0) and zero-width (k = 0) boundary cases of batched_counter_power.
example (T k : ℕ) :
    ∃ out : Circuit signature (0 * (k + k)) (0 * (k + k)),
      out.Computes interpretation (counterBatchPower (r := 0) (k := k) T) ∧
        out.size ≤ 40000 * (k + 1) ^ 3 * (2 ^ k + 0) :=
  batched_counter_power T 0 (Nat.zero_le _)

example (T : ℕ) :
    ∃ out : Circuit signature (1 * (0 + 0)) (1 * (0 + 0)),
      out.Computes interpretation (counterBatchPower (r := 1) (k := 0) T) ∧
        out.size ≤ 40000 * (0 + 1) ^ 3 * (2 ^ 0 + 1) :=
  batched_counter_power T 1 (by decide)

/-- Two-block `2 * (2 + 2)`-bit state with active block 0 `(modulus = 3, residue = 2)` and
inactive zero-modulus block 1 `(modulus = 0, residue = 1)`. -/
def sampleTwoBlockState : BitString (2 * (2 + 2)) :=
  fun i =>
    if (finProdFinEquiv.symm i).1 = 0 then
      ModulusCounter.pack (3 : BitVec 2) (2 : BitVec 2) (finProdFinEquiv.symm i).2
    else
      ModulusCounter.pack (0 : BitVec 2) (1 : BitVec 2) (finProdFinEquiv.symm i).2

-- Block 0 advances from residue 2 by T = 2 modulo 3 to residue 1, while block 1 (modulus 0)
-- stays fixed at residue 1.
example :
    counterBlock (counterBatchPower (r := 2) (k := 2) 2 sampleTwoBlockState) 0 =
      ModulusCounter.pack (3 : BitVec 2) (1 : BitVec 2) ∧
    counterBlock (counterBatchPower (r := 2) (k := 2) 2 sampleTwoBlockState) 1 =
      ModulusCounter.pack (0 : BitVec 2) (1 : BitVec 2) := by
  constructor <;> funext b <;> revert b <;> decide

-- Concrete nonidentity proof for `ModulusCounter.power (k := 2) 1` and instantiation of the
-- `r ≤ c.size` bound (`counterBatch_size_ge_of_ne_id` and `counterBatch_lower_bounds`).
theorem power_one_two_ne_id : ModulusCounter.power (k := 2) 1 ≠ id := by
  intro h
  have hbit := congrFun (congrFun h (ModulusCounter.pack (2 : BitVec 2) (0 : BitVec 2)))
    (Fin.natAdd 2 ⟨0, by decide⟩)
  revert hbit
  decide

example (c : Circuit signature (2 * (2 + 2)) (2 * (2 + 2)))
    (hc : c.Computes interpretation (counterBatchPower (r := 2) (k := 2) 1)) :
    2 ≤ c.size :=
  counterBatch_size_ge_of_ne_id 1 power_one_two_ne_id c hc

example (c : Circuit signature (2 * (2 + 2)) (2 * (2 + 2)))
    (hc : c.Computes interpretation (counterBatchPower (r := 2) (k := 2) 1)) :
    (∃ out : Circuit signature (2 + 2) (2 + 2),
      out.Computes interpretation (ModulusCounter.power 1) ∧ out.size ≤ c.size) ∧
    2 ≤ c.size := by
  obtain ⟨hsingle, hbatch⟩ := counterBatch_lower_bounds 1 (by decide : 0 < 2) c hc
  exact ⟨hsingle, hbatch power_one_two_ne_id⟩

-- Combined upper and lower bounds for batched hard counter powers at k = 64.
example :
    ∃ T < ModulusCounter.period 64, ∀ r, 0 < r → r ≤ 2 ^ (64 + 64) →
      (∃ out : Circuit signature (r * (64 + 64)) (r * (64 + 64)),
        out.Computes interpretation (counterBatchPower T) ∧
          out.size ≤ 40000 * (64 + 1) ^ 3 * (2 ^ 64 + r)) ∧
      ∀ c : Circuit signature (r * (64 + 64)) (r * (64 + 64)),
        c.Computes interpretation (counterBatchPower T) →
          lowerBudget 64 < c.size ∧ r ≤ c.size :=
  batched_hard_counter_power 64 (by decide)

/-! ### Axioms -/

/--
info: 'Cslib.Circuits.Boolean.Iteration.fixed_power_on' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fixed_power_on

/--
info: 'Cslib.Circuits.Boolean.Iteration.fixed_power' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fixed_power

/--
info: 'Cslib.Circuits.Boolean.Iteration.fixed_power_encoded' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fixed_power_encoded

/--
info: 'Cslib.Circuits.Boolean.Iteration.fixed_power_image' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fixed_power_image

/--
info: 'Cslib.Circuits.Boolean.Iteration.permutation_inverse' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms permutation_inverse

/--
info: 'Cslib.Circuits.Boolean.Iteration.permutation_inverse_encoded' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms permutation_inverse_encoded

/--
info: 'Cslib.Circuits.Boolean.Iteration.periodicPts_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms periodicPts_circuit

/--
info: 'Cslib.Circuits.Boolean.Iteration.fixed_power_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fixed_power_optimized

/--
info: 'Cslib.Circuits.Boolean.Iteration.fixed_power_half_exponent' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fixed_power_half_exponent

/--
info: 'Cslib.Circuits.Boolean.Iteration.fixed_power_polynomial' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fixed_power_polynomial

/--
info: 'Cslib.Circuits.Synthesis.word_add' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Synthesis.word_add

/--
info: 'Cslib.Circuits.Synthesis.word_sub' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Synthesis.word_sub

/--
info: 'Cslib.Circuits.Boolean.Iteration.exists_hard_power' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_hard_power

/--
info: 'Cslib.Circuits.Boolean.Iteration.counterStep_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms counterStep_circuit

/--
info: 'Cslib.Circuits.Boolean.Iteration.counter_power_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms counter_power_lower_bound

/--
info: 'Cslib.Circuits.Boolean.Iteration.almost_all_counter_powers_hard' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms almost_all_counter_powers_hard

/--
info: 'Cslib.Circuits.Boolean.Iteration.counter_powers_compute_remainders' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms counter_powers_compute_remainders

/--
info: 'Cslib.Circuits.Boolean.Iteration.variable_time_counter_iff_remainder' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms variable_time_counter_iff_remainder

/--
info: 'Cslib.Circuits.Boolean.Iteration.ModulusCounter.hard_power_exponent_capacity' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ModulusCounter.hard_power_exponent_capacity

/--
info: 'Cslib.Circuits.Boolean.Iteration.lcmBelow_lt_four_pow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms lcmBelow_lt_four_pow

/--
info: 'Cslib.Circuits.Boolean.Iteration.PrimeCycleData.period' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PrimeCycleData.period

/--
info: 'Cslib.Circuits.Boolean.Iteration.PrimeCycleData.exists_hard_power' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PrimeCycleData.exists_hard_power

/--
info: 'Cslib.Circuits.Boolean.Iteration.PrimeCycleData.step_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PrimeCycleData.step_circuit

/--
info: 'Cslib.Circuits.Boolean.Iteration.PrimeCycleData.power_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PrimeCycleData.power_circuit

/--
info: 'Cslib.Circuits.Boolean.Iteration.PrimeCycles.near_landau_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PrimeCycles.near_landau_lower_bound

/--
info: 'Cslib.Circuits.Boolean.Iteration.counterRemainder_of_power' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms counterRemainder_of_power

/--
info: 'Cslib.Circuits.Boolean.Iteration.counterPower_of_remainder' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms counterPower_of_remainder

/--
info: 'Cslib.Circuits.Boolean.Iteration.batched_counter_power' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms batched_counter_power

/--
info: 'Cslib.Circuits.Boolean.Iteration.counterPower_of_batched' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms counterPower_of_batched

/--
info: 'Cslib.Circuits.Boolean.Iteration.counterBatch_size_ge_of_ne_id' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms counterBatch_size_ge_of_ne_id

/--
info: 'Cslib.Circuits.Boolean.Iteration.counterBatch_lower_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms counterBatch_lower_bounds

/--
info: 'Cslib.Circuits.Boolean.Iteration.batched_hard_counter_power' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms batched_hard_counter_power

end ComplexityTests.Iteration
