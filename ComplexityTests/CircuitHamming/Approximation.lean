/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Approximation.Hamming
import Complexity.Computability.Circuit.Pointwise
import Cslib.Computability.Circuit.Boolean.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Two local approximation schemes for De Morgan circuits on two inputs: approximation by the
first projection, where every gate may err on every sample, and exact evaluation on truth tables,
where no gate errs. The first gives the lower-bound principle for the exclusive or in its counting,
Hamming and weighted forms; the second makes the decoded output equal to the target. -/

namespace ComplexityTests.CircuitHamming.Approximation

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Approximation Finset

/-! ### Approximation by a projection -/

/-- Approximation by the projections on two inputs: an approximate value names an input, every
gate is approximated by the first input, and every gate may err on all four samples. -/
def projScheme : Scheme interpretation (fun _ _ => (0 : Fin 2))
    (fun (i : Fin 2) (s : BitString 2) => s i) (fun s => s) id where
  relation := Eq
  relation_trans := Eq.trans
  map_relation _ _ _ h := congrArg _ (funext h)
  errorCost _ := 4
  exceptions _ _ := univ
  input_correct _ _ := rfl
  gate_correct _ _ s hs := absurd (mem_univ s) hs
  exceptions_card_le _ _ := by simp

instance : DecidableRel projScheme.relation := fun u v => inferInstanceAs (Decidable (u = v))

/-- The exclusive or is at Hamming distance two from both projections. -/
theorem le_hammingDist_xor (a : Fin 2) :
    2 ≤ hammingDist (fun s : BitString 2 => s 0 ^^ s 1) fun s => s a := by
  fin_cases a <;> decide

/-- **The lower-bound principle in Hamming terms**: the exclusive or is two samples away from
every projection and each gate errs on at most four, so it needs at least `2 / 4` gates, that is,
at least one. -/
example : 2 ≤ 4 * complexity interpretation (single fun x : BitString 2 => x 0 ^^ x 1) :=
  projScheme.le_mul_complexity_of_le_hammingDist id _ (fun _ => le_rfl) le_hammingDist_xor

/-- The same bound from the failures of the approximate values. -/
example : 2 ≤ 4 * complexity interpretation (single fun x : BitString 2 => x 0 ^^ x 1) := by
  refine projScheme.le_mul_complexity univ _ (fun _ => le_rfl) fun a => ?_
  fin_cases a <;> decide

/-- The weighted bound for the uniform distribution: the exclusive or fails with probability one
half on every projection, while each gate errs with probability at most one. -/
example :
    (1 / 2 : ℝ) ≤ 1 * complexity interpretation (single fun x : BitString 2 => x 0 ^^ x 1) := by
  refine projScheme.le_mul_complexity_of_le_sum_failures (μ := fun _ => 1 / 4)
    (fun _ => by norm_num) univ _ (fun _ _ => ?_) fun a => ?_
  · simp only [projScheme, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul]
    norm_num
  · have h : 2 ≤ #(projScheme.failures univ a fun s : BitString 2 => s 0 ^^ s 1) := by
      fin_cases a <;> decide
    rw [sum_const, nsmul_eq_mul]
    have h' : (2 : ℝ) ≤ #(projScheme.failures univ a fun s : BitString 2 => s 0 ^^ s 1) := by
      exact_mod_cast h
    linarith

/-- A one-gate circuit for the conjunction. -/
private def andCircuit : Circuit signature 2 1 :=
  ⟨.gate .empty ⟨.and, fun a => .input a⟩, fun _ => .gate 0⟩

/-- The decoded output of the conjunction circuit is within the total local error, four, of the
conjunction. -/
example : hammingDist (fun s : BitString 2 => s 0 && s 1)
    (fun s => s (andCircuit.eval (fun _ _ => (0 : Fin 2)) id 0)) ≤ 4 :=
  (projScheme.hammingDist_le_sum_errorCost id andCircuit fun _ => rfl).trans_eq rfl

/-! ### Exact evaluation on truth tables -/

/-- Exact evaluation on truth tables: the pointwise lift approximates exactly, with no
exceptions. -/
def exactScheme : Scheme interpretation (interpretation.pointwise (BitString 2))
    (fun (a : BitString 2 → Bool) s => a s) (fun s => s) (fun j x => x j) where
  relation := Eq
  relation_trans := Eq.trans
  map_relation _ _ _ h := congrArg _ (funext h)
  errorCost _ := 0
  exceptions _ _ := ∅
  input_correct _ _ := rfl
  gate_correct _ _ _ _ := rfl
  exceptions_card_le _ _ := le_rfl

/-- With no local errors, the decoded output of a circuit is the function it computes. -/
example : hammingDist (fun s : BitString 2 => s 0 && s 1)
    (andCircuit.eval (interpretation.pointwise (BitString 2)) (fun j x => x j) 0) = 0 :=
  Nat.le_zero.1 <| (exactScheme.hammingDist_le_sum_errorCost id andCircuit fun _ => rfl).trans_eq
    (by simp [exactScheme, andCircuit])

/-! ### Axioms -/

/--
info: 'Cslib.Circuits.Approximation.Scheme.hammingDist_le_sum_errorCost' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.hammingDist_le_sum_errorCost

/--
info: 'Cslib.Circuits.Approximation.Scheme.le_mul_complexity' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.le_mul_complexity

/--
info: 'Cslib.Circuits.Approximation.Scheme.le_mul_complexity_of_le_hammingDist' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.le_mul_complexity_of_le_hammingDist

/--
info: 'Cslib.Circuits.Approximation.Scheme.sum_failures_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.sum_failures_le

/--
info: 'Cslib.Circuits.Approximation.Scheme.le_mul_complexity_of_le_sum_failures' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.le_mul_complexity_of_le_sum_failures

end ComplexityTests.CircuitHamming.Approximation
