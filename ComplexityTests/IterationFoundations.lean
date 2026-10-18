/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Iteration
import Complexity.Foundations.Combinatorics.FunctionalGraph.Checkpoints
import Complexity.Foundations.Combinatorics.FunctionalGraph.Cycle
import Complexity.Foundations.Combinatorics.FunctionalGraph.Powers

/-!
# Iteration foundation clients

Exercise the orbit structure on concrete maps (an identity, a constant map, the empty type),
checkpoint packing on a finite invariant subset of an infinite type and its `L > 0` boundary,
and circuit iteration and retained orbits over a non-Boolean signature, including zero steps.
-/

namespace ComplexityTests.IterationFoundations

open Cslib Cslib.Circuits Cslib.FunctionalGraph Function

/-! ### Orbit structure -/

-- The identity map: every state is periodic of period one, with one distinct power.
example (x : Fin 3) : transientDepth id x = 0 ∧ cycleLength id x = 1 := by
  have hx : x ∈ periodicPts (id : Fin 3 → Fin 3) := mk_mem_periodicPts one_pos rfl
  refine ⟨(transientDepth_eq_zero_iff _ x).mpr hx, ?_⟩
  simp [cycleLength, (transientDepth_eq_zero_iff _ x).mpr hx]

-- The constant map onto `0` on `Fin 2`: state `1` has transient depth one.
private def toZero : Fin 2 → Fin 2 := fun _ => 0

private theorem toZero_iterate_succ (k : ℕ) (x : Fin 2) : toZero^[k + 1] x = 0 := by
  rw [iterate_succ_apply']; rfl

example : transientDepth toZero 1 = 1 := by
  have h0 : toZero^[1] 1 ∈ periodicPts toZero := mk_mem_periodicPts one_pos rfl
  have h1 : (1 : Fin 2) ∉ periodicPts toZero := by
    rintro ⟨p, hp, hper⟩
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    have := hper.eq
    rw [toZero_iterate_succ] at this
    exact absurd this (by decide)
  have hle := (iterate_mem_periodicPts_iff toZero 1 1).mp h0
  have hpos : transientDepth toZero 1 ≠ 0 := fun h => h1 ((transientDepth_eq_zero_iff _ _).mp h)
  omega

-- On an empty type the only power is the empty function: `μ + λ = 0 + 1`.
example (f : Empty → Empty) : Nat.card (Set.range fun T : ℕ => f^[T]) = 1 := by
  rw [card_range_iterate]
  simp [maxTransientDepth, cyclePeriod]

-- Two powers agree exactly as `iterate_eq_iterate_iff` says; distinct small powers differ.
example (f : Fin 4 → Fin 4) (i j : Fin (maxTransientDepth f + cyclePeriod f)) (h : i ≠ j) :
    f^[i.val] ≠ f^[j.val] := fun he => h (iterate_injective_below f he)

-- A repeat bounds the transient plus the cycle.
example (f : Fin 5 → Fin 5) (x : Fin 5) (h : f^[2] x = f^[4] x) :
    transientDepth f x + cycleLength f x ≤ 4 :=
  transientDepth_add_cycleLength_le_of_iterate_eq f x (by decide) h

-- The canonical cycle of a fixed point is the point itself.
example : canonicalCycle (id : Fin 3 → Fin 3) 2 ∈ cycleSet id 2 := canonicalCycle_mem _ _

/-! ### Checkpoints -/

-- Halving on `ℕ` maps `{0, …, 7}` into itself; the ambient type is infinite.
example : ∃ H : Finset ℕ, H ⊆ Finset.range 8 ∧ H.card * 2 ≤ (Finset.range 8).card ∧
    ∀ x ∈ Finset.range 8, Repeats (· / 2) x 2 ∨ ∃ d < 2 * 2, (· / 2)^[d] x ∈ H :=
  exists_checkpoints _ (Finset.range 8)
    (fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)) (by decide)

-- The hypothesis `0 < L` is necessary: with `L = 0` no state satisfies the conclusion.
example (f : ℕ → ℕ) (H : Finset ℕ) (x : ℕ) :
    ¬(Repeats f x 0 ∨ ∃ d < 2 * 0, f^[d] x ∈ H) := by
  rintro (⟨i, j, _, hj, _⟩ | ⟨d, hd, _⟩) <;> omega

-- On a finite type: at most `card α / L` checkpoints.
example (f : Fin 6 → Fin 6) : ∃ H : Finset (Fin 6), H.card ≤ 3 ∧
    ∀ x, Repeats f x 2 ∨ ∃ d < 2 * 2, f^[d] x ∈ H := by
  simpa using exists_checkpoints_finite f (L := 2) (by decide)

/-! ### Circuit iteration over a non-Boolean signature -/

/-- One unary operation, interpreted as the successor on `ℕ`. -/
private abbrev succSignature : Signature where
  Op := Unit
  Arity _ := 1

private def succInterpretation : Interpretation succSignature ℕ := fun _ x => x 0 + 1

/-- One successor gate on the single wire. -/
private def succCircuit : Circuit succSignature 1 1 :=
  ⟨.gate .empty ⟨(), fun _ => .input 0⟩, fun _ => .gate 0⟩

example : (succCircuit.iterate 3).eval succInterpretation ![4] = ![7] := by
  rw [Circuit.eval_iterate]
  decide

-- Exact arbitrary weighted cost and size, including zero steps.
example : (succCircuit.iterate 5).program.cost (fun _ => 7) = 35 := by
  rw [Circuit.cost_program_iterate]; rfl

example : (succCircuit.iterate 0).size = 0 ∧ (succCircuit.iterate 4).size = 4 := by
  simp [succCircuit]

-- Retaining the orbit prefix costs one copy per transition, and nothing for zero steps.
example (t : ℕ) : Synthesis succInterpretation (inputs 1)
    (Synthesis.stages (fun j => Set.range fun i (x : Fin 1 → ℕ) =>
      (succCircuit.eval succInterpretation)^[j] x i) t) (t * succCircuit.size) :=
  Synthesis.orbit (s := inputs 1) succCircuit (fun x => x) (fun i => Set.mem_range_self i) t

/-! ### Axioms -/

/--
info: 'Cslib.FunctionalGraph.exists_checkpoints' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_checkpoints

/--
info: 'Cslib.FunctionalGraph.card_range_iterate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms card_range_iterate

/--
info: 'Cslib.FunctionalGraph.orbit_prefix_injective' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms orbit_prefix_injective

/--
info: 'Cslib.FunctionalGraph.exists_iterate_eq_iff_canonicalCycle_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_iterate_eq_iff_canonicalCycle_eq

/--
info: 'Cslib.Circuits.Circuit.cost_program_iterate' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Circuit.cost_program_iterate

/--
info: 'Cslib.Circuits.Synthesis.orbit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Synthesis.orbit

end ComplexityTests.IterationFoundations
