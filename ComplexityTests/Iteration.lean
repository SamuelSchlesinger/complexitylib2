/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Iteration.InPlace
import Complexity.Computability.Circuit.Boolean.Iteration.Optimization
import Complexity.Computability.Circuit.Boolean.Iteration.Permutation
import Complexity.Computability.Circuit.Boolean.Iteration.SequentialSquaring
import Complexity.Computability.Circuit.Boolean.Iteration.UniversalMap

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

/-! ### Universal step map, in-place machines, and sequential squaring -/

-- Zero-gate (`G = 0`) round of the universal map on the identity circuit.
example (x : BitString 1) :
    (Universal.step interpretation)^[0 + 1]
      (Universal.start (Universal.describe 0 (Circuit.id signature 1) .not) x) =
    Universal.start (Universal.describe 0 (Circuit.id signature 1) .not)
      ((Circuit.id signature 1).eval interpretation x) :=
  Universal.step_round interpretation (Circuit.id signature 1) .not le_rfl x

-- One round of `1 + 1` steps of the universal map simulates `flip`.
example (x : BitString 1) :
    (Universal.step interpretation)^[1 + 1]
      (Universal.start (Universal.describe 1 flip .not) x) =
    Universal.start (Universal.describe 1 flip .not) (flip.eval interpretation x) :=
  Universal.step_round interpretation flip .not le_rfl x

-- Padded (`G = 3 > flip.size`) round of the universal map simulates `flip`.
example (x : BitString 1) :
    (Universal.step interpretation)^[3 + 1]
      (Universal.start (Universal.describe 3 flip .not) x) =
    Universal.start (Universal.describe 3 flip .not) (flip.eval interpretation x) :=
  Universal.step_round interpretation flip .not (by decide) x

-- Concrete instantiation of `Universal.universal_power_circuit` for `T = 1` on `flip`.
example : ∃ d : Circuit signature 1 1,
    d.Computes interpretation (flip.eval interpretation)^[1] ∧ d.size ≤ flip.size + 2 :=
  Universal.universal_power_circuit flip .not le_rfl (fun s => s.x) Sum.inl id (fun _ => rfl)
    (fun _ => rfl) 1 flip (fun x =>
      (congrArg Universal.Config.x
        (Universal.step_iterate interpretation flip .not le_rfl 1 x)).symm)

/-- A 1-head halting in-place machine on `Bool` tape with one absorbing state `Unit`. -/
private def idleMachine : InPlace.Machine Unit Bool 1 where
  δ q r _ _ := (q, r, fun _ => .stay)
  start := ()
  halting _ := True
  embed := id

private theorem idleMachine_absorbing : idleMachine.HaltingAbsorbing :=
  fun _ _ _ _ _ => rfl

example : (InPlace.reach idleMachine 2).card ≤ 8 := by
  simpa using InPlace.reach_card_le_configs idleMachine (n := 2)

example (z : InPlace.Config Unit Bool 2 1) :
    idleMachine.step^[Fintype.card (InPlace.Config Unit Bool 2 1)] z = z :=
  ((InPlace.iterate_card_halting idleMachine idleMachine_absorbing z).2 0 trivial)

private theorem injOn_config_one {h : ℕ} (M : InPlace.Machine Unit Bool h) :
    Set.InjOn (fun z : InPlace.Config Unit Bool 1 h => z.1) (InPlace.reach M 1) := by
  intro z₁ _ z₂ _ h1
  exact Prod.ext h1 (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))

-- Concrete instantiation of `InPlace.inplace_halting` on `idleMachine`.
example : ∃ (out : Circuit signature 1 1) (final : BitString 1 → InPlace.Config Unit Bool 1 1),
    (∀ x, out.eval interpretation x = (final x).1 ∧
      (idleMachine.halting (final x).2.2 ↔
        ∃ t, idleMachine.halting (idleMachine.step^[t] (idleMachine.init x)).2.2) ∧
      ∀ t, idleMachine.halting (idleMachine.step^[t] (idleMachine.init x)).2.2 →
        final x = idleMachine.step^[t] (idleMachine.init x)) ∧
    (out.size : ℝ) ≤ (Circuit.id signature 1).size + 120000 * optimizedBudget 1 0 2 := by
  simpa using InPlace.inplace_halting idleMachine idleMachine_absorbing (fun z => z.1)
    (injOn_config_one idleMachine) (Circuit.id signature 1)
    (fun z _ => by rw [InPlace.Machine.step_of_halting idleMachine_absorbing z trivial]; rfl)
    (Circuit.id signature 1) (fun _ => rfl)

/-- A 2-head 1-cell machine where head 0 writes `false` and moves `.left`, while head 1 writes
`!r 1` and moves `.right`. On a 1-cell tape both moves clamp to `0`, and head 1's write wins. -/
private def collideMachine : InPlace.Machine Unit Bool 2 where
  δ q r _ _ := (q, ![false, !r 1], ![.left, .right])
  start := ()
  halting _ := False
  embed := id

private theorem collideMachine_step (z : InPlace.Config Unit Bool 1 2) :
    collideMachine.step z = (fun _ => !z.1 0, fun _ => 0, ()) := by
  refine Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))
  funext i
  fin_cases i
  have hp0 : z.2.1 0 = 0 := Subsingleton.elim _ _
  have hp1 : z.2.1 1 = 0 := Subsingleton.elim _ _
  simp [collideMachine, InPlace.Machine.step, InPlace.writeHeads, Fin.foldl_succ_last,
    Fin.foldl_zero, hp1]

private theorem collideMachine_round (x : BitString 1) :
    collideMachine.step^[1] (collideMachine.init x) =
      collideMachine.init (flip.eval interpretation x) := by
  rw [Function.iterate_one, collideMachine_step]
  simp [InPlace.Machine.init, collideMachine, eval_flip]

-- Concrete instantiation of `InPlace.inplace_configs_optimized` and `InPlace.round_bounds_of_hard`
-- on the 2-head colliding/clamping machine `collideMachine`.
example (T : ℕ) : ∃ out : Circuit signature 1 1,
    (∀ x, out.eval interpretation x = (collideMachine.step^[T] (collideMachine.init x)).1) ∧
    (out.size : ℝ) ≤ (Circuit.id signature 1).size + 120000 * optimizedBudget 1 flip.size 2 := by
  simpa using InPlace.inplace_configs_optimized collideMachine (fun z => z.1)
    (injOn_config_one collideMachine) flip
    (fun z _ => by rw [collideMachine_step, eval_flip])
    (Circuit.id signature 1) (fun _ => rfl) T

example (q : ℕ)
    (hhard : ∀ d : Circuit signature 1 1,
      d.Computes interpretation (flip.eval interpretation)^[1] → q < d.size) :
    (∀ out : Circuit signature 1 1,
      (∀ x, out.eval interpretation x = (collideMachine.step^[1 * 1] (collideMachine.init x)).1) →
      q < out.size) ∧
    ∀ T', ∃ out : Circuit signature 1 1,
      (∀ x, out.eval interpretation x = (collideMachine.step^[T'] (collideMachine.init x)).1) ∧
      (out.size : ℝ) ≤ (Circuit.id signature 1).size + 120000 * optimizedBudget 1 flip.size 2 := by
  simpa using InPlace.round_bounds_of_hard collideMachine 1 1 q one_pos (flip.eval interpretation)
    collideMachine_round (fun z => z.1) (injOn_config_one collideMachine) id (fun _ => rfl) hhard
    flip (fun z _ => by rw [collideMachine_step, eval_flip]) (Circuit.id signature 1) (fun _ => rfl)

-- Sequential squaring modulo `M = 1`, at `T = 0`, and on a non-unit residue modulo `M = 15`.
example (T : ℕ) (x : ZMod 1) :
    (fun y : ZMod 1 => y ^ 2)^[T] x = x ^ SequentialSquaring.reducedExponent 1 T :=
  SequentialSquaring.iterate_square_reduced squarefree_one T x

private theorem squarefree_15 : Squarefree (15 : ℕ) := by
  rintro (_ | _ | _ | _ | d) ⟨k, hk⟩
  · omega
  · exact isUnit_one
  · omega
  · omega
  · rcases k with _ | k
    · omega
    · nlinarith

-- `3 : ZMod 15` is a non-unit, yet satisfies `pow_carmichael_succ` and `iterate_square_reduced`
-- (including at `T = 0`).
example : ¬ IsUnit (3 : ZMod 15) := by
  rintro ⟨u, hu⟩
  have h := congrArg (fun z : ZMod 15 => (5 : ZMod 15) * z) hu
  have h0 : (5 : ZMod 15) * 3 = 0 := by decide
  have h5 : (5 : ZMod 15) ≠ 0 := by decide
  have hu0 : (5 : ZMod 15) * (u : ZMod 15) = 0 := h.trans h0
  have := (Units.mul_left_eq_zero u).mp hu0
  exact h5 this

example : (3 : ZMod 15) ^ (SequentialSquaring.carmichael 15 + 1) = (3 : ZMod 15) :=
  SequentialSquaring.pow_carmichael_succ squarefree_15 3

example : (fun y : ZMod 15 => y ^ 2)^[0] (3 : ZMod 15) =
    (3 : ZMod 15) ^ SequentialSquaring.reducedExponent 15 0 :=
  SequentialSquaring.iterate_square_reduced squarefree_15 0 3

example (T : ℕ) (x : ZMod 15) :
    (fun y : ZMod 15 => y ^ 2)^[T] x = x ^ SequentialSquaring.reducedExponent 15 T :=
  SequentialSquaring.iterate_square_reduced squarefree_15 T x

-- Non-squarefree boundary (`M = 4`): `x ^ (λ(4) + 1) = x` fails at the nilpotent residue `2`.
example : ¬ Squarefree (4 : ℕ) := by
  intro h
  have h2 := Nat.isUnit_iff.mp (h 2 ⟨1, by ring⟩)
  omega

example : (2 : ZMod 4) ^ (SequentialSquaring.carmichael 4 + 1) ≠ (2 : ZMod 4) := by
  obtain ⟨k, hk⟩ : ∃ k, SequentialSquaring.carmichael 4 + 1 = k + 2 :=
    ⟨SequentialSquaring.carmichael 4 - 1, by
      have := SequentialSquaring.carmichael_pos 4
      omega⟩
  rw [hk, pow_add, show (2 : ZMod 4) ^ 2 = 0 by decide, mul_zero]
  decide

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
info: 'Cslib.Circuits.Boolean.Iteration.simulation_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms simulation_circuit

/--
info: 'Cslib.Circuits.Boolean.Iteration.prodMap_power_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prodMap_power_circuit

/--
info: 'Cslib.Circuits.Boolean.Iteration.smul_zpow_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms smul_zpow_circuit

/--
info: 'Cslib.Circuits.Boolean.Iteration.smul_iterate_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms smul_iterate_circuit

/--
info: 'Cslib.Circuits.Boolean.Iteration.smul_inverse_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms smul_inverse_circuit

/--
info: 'Cslib.Circuits.Boolean.Iteration.Universal.step_round' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Universal.step_round

/--
info: 'Cslib.Circuits.Boolean.Iteration.Universal.step_iterate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Universal.step_iterate

/--
info: 'Cslib.Circuits.Boolean.Iteration.Universal.universal_power_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Universal.universal_power_circuit

/--
info: 'Cslib.Circuits.Boolean.Iteration.InPlace.reach_card_le_configs' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms InPlace.reach_card_le_configs

/--
info: 'Cslib.Circuits.Boolean.Iteration.InPlace.reach_card_le_time' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms InPlace.reach_card_le_time

/--
info: 'Cslib.Circuits.Boolean.Iteration.InPlace.reach_card_le_round' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms InPlace.reach_card_le_round

/--
info: 'Cslib.Circuits.Boolean.Iteration.InPlace.iterate_card_halting' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms InPlace.iterate_card_halting

/--
info: 'Cslib.Circuits.Boolean.Iteration.InPlace.inplace_fixed_power_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms InPlace.inplace_fixed_power_optimized

/--
info: 'Cslib.Circuits.Boolean.Iteration.InPlace.inplace_configs_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms InPlace.inplace_configs_optimized

/--
info: 'Cslib.Circuits.Boolean.Iteration.InPlace.inplace_time_optimized' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms InPlace.inplace_time_optimized

/--
info: 'Cslib.Circuits.Boolean.Iteration.InPlace.inplace_halting' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms InPlace.inplace_halting

/--
info: 'Cslib.Circuits.Boolean.Iteration.InPlace.round_lower_bound_of_hard' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms InPlace.round_lower_bound_of_hard

/--
info: 'Cslib.Circuits.Boolean.Iteration.InPlace.round_bounds_of_hard' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms InPlace.round_bounds_of_hard

/--
info: 'Cslib.Circuits.Boolean.Iteration.SequentialSquaring.pow_carmichael_succ' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SequentialSquaring.pow_carmichael_succ

/--
info: 'Cslib.Circuits.Boolean.Iteration.SequentialSquaring.pow_eq_pow_of_modEq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SequentialSquaring.pow_eq_pow_of_modEq

/--
info: 'Cslib.Circuits.Boolean.Iteration.SequentialSquaring.iterate_square_reduced' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SequentialSquaring.iterate_square_reduced

/--
info: 'Cslib.Circuits.Boolean.Iteration.SequentialSquaring.crypto_table_entries' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SequentialSquaring.crypto_table_entries

end ComplexityTests.Iteration
