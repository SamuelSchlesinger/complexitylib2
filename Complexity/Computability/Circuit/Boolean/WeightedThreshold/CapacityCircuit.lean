/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedThreshold
public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Capacity
import Mathlib.Algebra.BigOperators.Fin

/-!
# Scalar-block capacity of native weighted threshold programs

A native program gives a block decomposition by revealing its gate values in topological order.
The history is its existing gate evaluation, masked to the gates already processed. Each gate
with a nonzero effective coefficient on an original input has capacity cost four. Every other
gate has cost one, even when its output changes with earlier gate values. Repeated argument
wires are counted through their aggregated coefficients, so cancelling input weights do not
create an input-reading block.

The resulting capacity bound applies to any fixed Boolean readout of the gate values. The
single-output circuit corollary requires that its output wire selects a gate: an original-input
wire is not part of this readout. No separate evaluator or runtime algorithm is introduced.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.blockDecomposition`: a native program as scalar blocks.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.cost_blockDecomposition`: exact cost `4 ^ |inputGates|`.
* `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_mul_four_pow_inputGates`: the C1 bound.

## References

* [S. Schlesinger, *Algebraic circuit formalization*, Threshold (C1) and its internal lemmas]
  [Schlesinger2026Algebraic]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset

variable {n g : ℕ}

private theorem changesAtMost_threshold {H : Type*} (out : Bool → H) (c : ℝ) :
    ChangesAtMost (fun t => out (decide (c ≤ t))) 1 := by
  intro z hz S hS
  have hcut (i) (hi : i ∈ S) : z i < c ∧ c ≤ z (i + 1) := by
    have hn : ¬ c ≤ z i := by
      intro hc
      exact hS i hi (by simp [hc, hc.trans (hz (Nat.le_succ i))])
    have hp : c ≤ z (i + 1) := by
      by_contra hn'
      exact hS i hi (by simp [hn, hn'])
    exact ⟨lt_of_not_ge hn, hp⟩
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact (not_lt_of_ge ((hcut i hi).2.trans (hz h))) (hcut j hj).1
  · exact (not_lt_of_ge ((hcut j hj).2.trans (hz h))) (hcut i hi).1

private theorem masked_eval_succ (p : Program signature n g) (gate : Fin g) (x : Fin n → Bool) :
    (fun j : Fin g => if j.val < gate.val + 1 then p.eval interpretation x j else false) =
      Function.update (fun j => if j.val < gate.val then p.eval interpretation x j else false)
        gate (decide ((p.lines gate).op.threshold ≤
          (∑ i, inputWeight p gate i * (x i).toNat) +
          ∑ j, gateWeight p gate j *
            (if j.val < gate.val then p.eval interpretation x j else false).toNat)) := by
  have heval := eval_gate_eq p x gate
  have hsum : (∑ j, gateWeight p gate j * (p.eval interpretation x j).toNat) =
      ∑ j, gateWeight p gate j *
        (if j.val < gate.val then p.eval interpretation x j else false).toNat := by
    apply sum_congr rfl
    intro j _
    by_cases hj : j < gate
    · simp [hj]
    · simp [hj, gateWeight_eq_zero_of_le p gate j (le_of_not_gt hj)]
  rw [hsum] at heval
  funext j
  by_cases hj : j = gate
  · subst j
    simpa using heval
  · rw [Function.update_of_ne hj]
    have hv : j.val ≠ gate.val := fun h => hj (Fin.ext h)
    have heq : (j.val < gate.val + 1) ↔ j.val < gate.val := by omega
    simp only [heq]

private theorem masked_eval_step (p : Program signature n g) (gate : Fin g) :
    (BlockKind.oneDim (if gate ∈ inputGates p then 1 else 0)).Step
      (fun x j => if j.val < gate.val then p.eval interpretation x j else false)
      (fun x j => if j.val < gate.val + 1 then p.eval interpretation x j else false) := by
  classical
  by_cases hgate : gate ∈ inputGates p
  · simp only [hgate, ite_true, BlockKind.Step]
    refine ⟨inputWeight p gate,
      fun z t => Function.update z gate (decide ((p.lines gate).op.threshold ≤
        t + ∑ j, gateWeight p gate j * (z j).toNat)), ?_, ?_⟩
    · intro z
      exact (changesAtMost_threshold (Function.update z gate) _).comp_monotone
        (monotone_id.add_const _)
    · exact masked_eval_succ p gate
  · simp only [hgate, ite_false, BlockKind.Step]
    refine ⟨fun _ => 0,
      fun z _ => Function.update z gate (decide ((p.lines gate).op.threshold ≤
        ∑ j, gateWeight p gate j * (z j).toNat)), ?_, ?_⟩
    · intro z
      exact ChangesAtMost.const _
    · intro x
      simpa only [inputWeight_eq_zero_of_not_mem p hgate, zero_mul, sum_const_zero,
        zero_add] using masked_eval_succ p gate x

/-- Revealing the existing gate evaluation one gate at a time gives a scalar block decomposition.
The output may be any fixed Boolean readout of the gate values. -/
noncomputable def blockDecomposition (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) :
    BlockDecomposition (fun x => readout (p.eval interpretation x)) (Fin g → Bool) where
  length := g
  kind := fun i => .oneDim (if h : i < g then if ⟨i, h⟩ ∈ inputGates p then 1 else 0 else 0)
  history := fun i x j => if j.val < i then p.eval interpretation x j else false
  output := readout
  history_zero := by simp
  step := fun i hi => by simpa only [dite_eq_left hi] using masked_eval_step p ⟨i, hi⟩
  output_history := fun x => by simp

/-- Every effective input-reading gate costs four, and every other gate costs one. -/
theorem cost_blockDecomposition (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) :
    (blockDecomposition p readout).cost = 4 ^ (inputGates p).card := by
  classical
  simp only [BlockDecomposition.cost, blockDecomposition]
  rw [← Fin.prod_univ_eq_prod_range]
  simp only [dite_eq_left, Fin.isLt]
  have hcost (j : Fin g) :
      (BlockKind.oneDim (if j ∈ inputGates p then 1 else 0)).cost =
        if j ∈ inputGates p then 4 else 1 := by
    by_cases h : j ∈ inputGates p <;> simp [h, BlockKind.cost]
  simp only [hcost]
  rw [Finset.prod_ite_mem_eq]
  simp

/-- **C1 capacity bound.** Any Boolean readout of a weighted program's gate values computing a
function whose two fibers are `K`-rectangle-free satisfies this input-reading-gate bound. -/
theorem two_pow_lt_mul_four_pow_inputGates (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction n} {K : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 4 * K ^ 2 * 4 ^ (inputGates p).card := by
  have h := (blockDecomposition p readout).two_pow_lt_mul_cost
    (fun b => by simpa only [hreadout] using hf b)
  simpa only [cost_blockDecomposition] using h

/-- The C1 bound for a single-output circuit whose output selects a gate. -/
theorem circuit_two_pow_lt_mul_four_pow_inputGates (c : Circuit signature n 1)
    (houtput : ∃ gate, c.outputs 0 = .gate gate) {f : Cslib.BooleanFunction n} {K : ℕ}
    (hcomputes : ∀ x, c.eval interpretation x 0 = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 4 * K ^ 2 * 4 ^ (inputGates c.program).card := by
  obtain ⟨gate, hgate⟩ := houtput
  apply two_pow_lt_mul_four_pow_inputGates c.program (fun z => z gate) ?_ hf
  intro x
  simpa only [Circuit.eval, Function.comp_apply, hgate, Program.trace, Wire.elim_gate]
    using hcomputes x

end Cslib.Circuits.Boolean.WeightedThreshold
