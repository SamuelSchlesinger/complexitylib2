/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Iteration.SparseTime
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# Sparse-counter variable-time clients

Exercise carry overflow, empty state/time widths, a full counter cycle, and an edited
counter with two cycles. A concrete interval chart checks satisfiability of the chart
contract; coordinate transfer uses actual identity circuits.
-/

namespace ComplexityTests.Iteration.SparseTime

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Iteration
open Cslib.FunctionalGraph

attribute [local instance] counterChartWordOrder

-- 6 + 6 overflows three bits, but the widened modular adder gives 12 mod 7 = 5.
example : addResidue (7 : BitVec 3) 6 6 = 5 := by decide
example : addResidue (7 : BitVec 3) 0 0 = 0 := by decide
example : addResidue (0 : BitVec 0) 0 0 = 0 := by decide

-- The zero-time-width circuit returns the input state.
example (f : Equiv.Perm (BitVec 2)) : ∃ out : Circuit signature (2 + 0) 2,
    out.Computes interpretation (fun z i => z (Fin.castAdd 0 i)) ∧
    out.size ≤ 5000 * ((disagreement f (fun x => x + 1)).card + 1) := by
  obtain ⟨out, hout, hs⟩ := sparse_counter_variable_time f 0
  refine ⟨out, ?_, by simpa using hs⟩
  intro z
  have ht : (word (fun j : Fin 0 => z (Fin.natAdd 2 j))).toNat = 0 := by
    have := (word (fun j : Fin 0 => z (Fin.natAdd 2 j))).isLt
    simpa using this
  simpa only [ht, Function.iterate_zero_apply, getLsbD_word] using hout z

example (m : ℕ) : ∃ out : Circuit signature (0 + m) 0,
    out.Computes interpretation (fun _ => Fin.elim0) ∧ out.size ≤ 3000 * (m + 1) := by
  obtain ⟨out, hout, hs⟩ := sparse_counter_variable_time (Equiv.refl (BitVec 0)) m
  have he : disagreement (Equiv.refl (BitVec 0)) (fun x => x + 1) = ∅ := by
    ext x
    simp [mem_disagreement]
  refine ⟨out, fun _ => funext fun i => Fin.elim0 i, ?_⟩
  rw [he] at hs
  simpa using hs

-- Full-cycle wraparound with a time wider than the state.
example : (streamRemainder (4 : BitVec 4)
    (fun i : Fin 6 => (63 : BitVec 6).getLsbD i.val)).toNat = 3 := by decide

example (m : ℕ) : ∃ out : Circuit signature (2 + m) 2,
    out.Computes interpretation (fun z i =>
      (((fun x : BitVec 2 => x + 1)^[(word fun j => z (Fin.natAdd 2 j)).toNat])
        (word fun j => z (Fin.castAdd m j))).getLsbD i.val) ∧
    out.size ≤ 5000 * (m + 1) := by
  have h := sparse_counter_variable_time (Equiv.addRight (1 : BitVec 2)) m
  have he : disagreement (Equiv.addRight (1 : BitVec 2)) (fun x => x + 1) = ∅ := by
    ext x
    simp [mem_disagreement]
  rw [he] at h
  simpa using h

-- Cycles (0,1) and (2,3); exactly the edges at 1 and 3 differ from the counter.
private def twoCycles : Equiv.Perm (BitVec 2) :=
  (Equiv.swap 1 3).trans (Equiv.addRight 1)

private theorem twoCycles_disagreement :
    disagreement twoCycles (fun x => x + 1) = {1, 3} := by
  ext x
  simp only [mem_disagreement, Finset.mem_insert, Finset.mem_singleton]
  revert x
  decide

private def twoIntervalChart : CounterIntervalChart twoCycles 2 where
  start j := 2 * j.val
  stop j := 2 * j.val + 2
  start_lt_stop := by intro j; lia
  stop_le := by intro j; have := j.isLt; lia
  covers := by decide
  path := by
    intro j d hd
    have hd' : d < 2 := by lia
    interval_cases d <;> fin_cases j <;> decide

-- The chart's two intervals genuinely satisfy encoding and decoding on every state.
example (x : BitVec 2) : twoIntervalChart.encode x = wordCycleLabel twoCycles x :=
  twoIntervalChart.encode_spec twoCycles.injective x

example (x : BitVec 2) :
    twoIntervalChart.decode (canonicalCycle twoCycles x)
      (BitVec.ofNat (chartWidth 2) (phase twoCycles x)) = fun i => x.getLsbD i.val :=
  twoIntervalChart.decode_spec twoCycles.injective x

example (m : ℕ) : ∃ out : Circuit signature (2 + m) 2,
    out.Computes interpretation (fun z i =>
      ((twoCycles : BitVec 2 → BitVec 2)^[(word fun j => z (Fin.natAdd 2 j)).toNat]
        (word fun j => z (Fin.castAdd m j))).getLsbD i.val) ∧
    out.size ≤ 5000 * (m + 3) := by
  have h := sparse_counter_variable_time twoCycles m
  rw [twoCycles_disagreement] at h
  simpa [Nat.add_comm, Nat.add_left_comm] using h

example (m : ℕ) : ∃ out : Circuit signature (2 + m) 2,
    out.Computes interpretation (fun z i =>
      ((twoCycles : BitVec 2 → BitVec 2)^[(word fun j => z (Fin.natAdd 2 j)).toNat]
        (word fun j => z (Fin.castAdd m j))).getLsbD i.val) ∧
    out.size ≤ 5000 * (m + 3) := by
  have hid : (Circuit.id signature 2).Computes interpretation
      (fun x i => ((Equiv.refl (BitVec 2)) (word x)).getLsbD i.val) := by
    intro x
    funext i
    exact (getLsbD_word x i).symm
  have h := sparse_coordinate_variable_time twoCycles (Equiv.addRight 1) (Equiv.refl _)
    (fun _ => rfl) (Circuit.id signature 2) (Circuit.id signature 2) hid hid m
  have he : disagreement twoCycles (Equiv.addRight (1 : BitVec 2)) = {1, 3} :=
    twoCycles_disagreement
  rw [he] at h
  simpa [Nat.add_comm, Nat.add_left_comm] using h

/--
info: 'Cslib.Circuits.Boolean.Iteration.toNat_addResidue' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Iteration.toNat_addResidue

/--
info: 'Cslib.Circuits.Boolean.Iteration.exists_counterIntervalChart' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Iteration.exists_counterIntervalChart

/--
info: 'Cslib.Circuits.Boolean.Iteration.sparse_counter_variable_time' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Iteration.sparse_counter_variable_time

/--
info: 'Cslib.Circuits.Boolean.Iteration.sparse_counter_labels' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Iteration.sparse_counter_labels

/--
info: 'Cslib.Circuits.Boolean.Iteration.sparse_coordinate_variable_time' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Iteration.sparse_coordinate_variable_time

end ComplexityTests.Iteration.SparseTime
