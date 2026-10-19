/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Iteration.Batch

/-!
# Input-time and batched iteration clients

Input times are evaluated on a two-bit counter, including zero time bits; the shared lookup on
present, absent and duplicated keys; the finishing step without a flagged time; the
checkpoint-free power on the identity; and the input-time and batched theorems on the bit-flip
circuit, including an empty batch and the balanced bounds.
-/

namespace ComplexityTests.Iteration.Batch

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Iteration

/-- The one-bit negation circuit. -/
private def flip : Circuit signature 1 1 :=
  ⟨.gate .empty ⟨.not, fun _ => .input 0⟩, fun _ => .gate 0⟩

/-! ### Input times and batches -/

/-- Two-bit increment modulo four, least significant bit first. -/
private def inc (x : BitString 2) : BitString 2 := ![!x 0, x 1 ^^ x 0]

-- Time bits `true, true` (least significant first) encode `3`: `00` becomes `11`.
example : inputTimeIterate inc 2 ![false, false, true, true] = ![true, true] := by decide

-- Time bits `false, true` encode `2`: `01` becomes `11`.
example : inputTimeIterate inc 2 ![true, false, false, true] = ![true, true] := by decide

-- Without time bits the state is returned.
example (y : BitString (2 + 0)) : inputTimeIterate inc 0 y = fun i => y (Fin.castAdd 0 i) :=
  inputTimeIterate_zero inc y

-- Every input time of the flip, with the fixed-power circuits at `L = 1`.
example (m : ℕ) : ∃ out : Circuit signature (1 + m) 1,
    out.Computes interpretation (inputTimeIterate (flip.eval interpretation) m) ∧
      out.size ≤ m * (40000 * powerBudget 1 1 2 1 + 4) := by
  simpa [flip] using variable_time flip m 1 one_pos (by decide)

-- The shared lookup returns the stored value, all-false for an absent key, and the OR of the
-- values stored under a repeated key.
example : lookupOr ![![true, false], ![false, true]] ![![true], ![false]] ![true, false] =
    ![true] := by decide

example : lookupOr ![![true, false], ![false, true]] ![![true], ![false]] ![true, true] =
    ![false] := by decide

example : lookupOr ![![true, false], ![true, false]] ![![true, false], ![false, true]]
    ![true, false] = ![true, true] := by decide

-- Without a flagged time the finished state is the fallback.
example : finishHit (w := 2) inc 1 ![false, false] ![![true, true], ![true, false]]
    ![false, true] = ![false, true] := by decide

-- The identity repeats immediately, so the checkpoint-free power applies at `L = 2`.
example (T : ℕ) (hT : 4 ≤ T) : ∃ out : Circuit signature 1 1,
    (∀ x, out.eval interpretation x = x) ∧ out.size ≤ 40000 * powerBudget 1 0 0 2 := by
  have hid : (Circuit.id signature 1).eval interpretation = id := rfl
  obtain ⟨out, hout, hs⟩ := exists_repeat_power (Circuit.id signature 1) T 2 two_pos (by decide)
    hT
  refine ⟨out, fun x => ?_, by simpa using hs⟩
  rw [hout x ⟨0, 1, by decide, by decide, by simp [hid]⟩, hid, Function.iterate_id]
  rfl

-- Two independent flips share one dictionary.
example (T : ℕ) : ∃ out : Circuit signature (2 * 1) (2 * 1),
    out.Computes interpretation (blockMap (flip.eval interpretation)^[T] 2) ∧
      out.size ≤ 100000 * batchBudget 1 1 2 2 1 := by
  simpa [flip] using batched_fixed_power flip 2 T 1 (by decide) one_pos (by decide)

-- The empty batch is allowed.
example (c : Circuit signature 2 2) (T : ℕ) : ∃ out : Circuit signature (0 * 2) (0 * 2),
    out.Computes interpretation (blockMap (c.eval interpretation)^[T] 0) ∧
      out.size ≤ 100000 * batchBudget 2 c.size 4 0 1 :=
  batched_fixed_power c 0 T 1 (by decide) one_pos (by decide)

-- A single trajectory recovers the fixed-power tradeoff.
example (n s M L : ℕ) : batchBudget n s M 1 L = powerBudget n s M L := batchBudget_one n s M L

-- Two flips, each with its own time.
example (m : ℕ) : ∃ out : Circuit signature (2 * (1 + m)) (2 * 1),
    out.Computes interpretation (blockMap (inputTimeIterate (flip.eval interpretation) m) 2) ∧
      out.size ≤ m * (100000 * batchBudget 1 1 2 2 1 + 4 * (2 * 1)) := by
  simpa [flip] using batched_variable_time flip 2 m 1 (by decide) one_pos (by decide)

-- The balanced batched bounds.
example (c : Circuit signature 3 3) (T : ℕ) : ∃ out : Circuit signature (2 * 3) (2 * 3),
    out.Computes interpretation (blockMap (c.eval interpretation)^[T] 2) ∧
      (out.size : ℝ) ≤ 300000 * optimizedBatchBudget 3 c.size 8 2 :=
  batched_fixed_power_optimized c 2 T two_pos (by decide)

/-! ### Axioms -/

/--
info: 'Cslib.Circuits.Boolean.Iteration.variable_time' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms variable_time

/--
info: 'Cslib.Circuits.Boolean.Iteration.variable_time_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms variable_time_optimized

/--
info: 'Cslib.Circuits.Boolean.Iteration.binary_powering' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms binary_powering

/--
info: 'Cslib.Circuits.Boolean.Iteration.synthesis_lookupOr' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms synthesis_lookupOr

/--
info: 'Cslib.Circuits.Boolean.Iteration.exists_repeat_power' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_repeat_power

/--
info: 'Cslib.Circuits.Boolean.Iteration.batched_fixed_power' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms batched_fixed_power

/--
info: 'Cslib.Circuits.Boolean.Iteration.batched_fixed_power_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms batched_fixed_power_optimized

/--
info: 'Cslib.Circuits.Boolean.Iteration.batched_variable_time' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms batched_variable_time

/--
info: 'Cslib.Circuits.Boolean.Iteration.batched_variable_time_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms batched_variable_time_optimized

end ComplexityTests.Iteration.Batch
