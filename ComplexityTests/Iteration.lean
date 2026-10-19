/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Iteration.Optimization
import Complexity.Computability.Circuit.Boolean.Iteration.Permutation

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
    (fun i => ⟨⟨i, by omega⟩, by funext x; simp⟩)
    (fun i => ⟨⟨i + 2, by omega⟩, by funext x; simp⟩)).exists_circuit_outputs

-- Table selection is exact in range and all-false out of range.
example : selectBits (BitVec.ofNat 2 1) ![![true, false], ![false, true]] = ![false, true] := by
  decide

example : selectBits (BitVec.ofNat 2 3) ![![true, false], ![false, true]] = ![false, false] := by
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

end ComplexityTests.Iteration
