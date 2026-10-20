/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ElementDistinctness
public import Complexity.Computability.WordRAM.RAM

/-!
# Element distinctness on a logarithmic-cost RAM

The bounded-universe direct-addressing algorithm
[Cormen et al., Section 11.1][CLRS2009] uses only the additive-memory fragment of the word RAM.
Compiling its fixed twelve-register program with `Cslib.WordRAM.ToRAM.paddedProgram` gives a
natural-number RAM decider with logarithmic cost `O((n + 1) (log(n + 1) + 1))`.

This first statement uses the explicitly supplied padded, length-bearing input convention.
It charges every executed instruction, including compiler initialization and output, but does
not yet certify construction of that input layout. The entries must be below the input length;
unrestricted element distinctness is outside the statement. The target is the library's
natural-number adaptation of [Cook and Reckhow][CookReckhow1973], not a Turing-machine theorem.
The source word RAM adapts [MIT–ULB CompGeom Group][Tromino2025].

## Main definitions

* `Cslib.Algorithms.WordRAM.ElementDistinctness.paddedRamProgram`: the fixed compiled decider.

## Main results

* `Cslib.Algorithms.WordRAM.ElementDistinctness.program_isAdditive`: the concrete source
  program belongs to the compiler's supported fragment.
* `Cslib.Algorithms.WordRAM.ElementDistinctness.haltsWithResultInTime_nodup_padded`: the
  compiled decider answers within `2448 (n + 1) (Nat.log 2 (n + 1) + 1)` logarithmic cost.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
* [S. A. Cook and R. A. Reckhow, *Time bounded random access machines*][CookReckhow1973]
* [MIT–ULB CompGeom Group, *Undecidability of tiling with a tromino*][Tromino2025]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ElementDistinctness

open Cslib.WordRAM

/-- Every instruction of the compiled source decider is in the additive-memory fragment. -/
theorem program_isAdditive : (decider.program Reg.ans).IsAdditive := by decide

/-- The fixed twelve-register source decider compiled to the natural-number RAM. Its input
convention is `ToRAM.paddedInput 12`, whose supplied zero prefix has length seventeen. -/
def paddedRamProgram : RAM.Program := ToRAM.paddedProgram (decider.program Reg.ans)

/-- Bounded-universe element distinctness has logarithmic RAM cost
`2448 (n + 1) (log₂(n + 1) + 1)` from the supplied padded-input convention. The constant is
not optimized. All source and compiler instructions are charged, but constructing the
initial padded list is not included. -/
theorem haltsWithResultInTime_nodup_padded (a : Input) :
    RAM.HaltsWithResultInTime RAM.logCost paddedRamProgram (ToRAM.paddedInput 12 a.1)
      (if a.1.Nodup then 1 else 0)
      (2448 * (a.1.length + 1) * (Nat.log 2 (a.1.length + 1) + 1)) := by
  let w := logWidth 2 a.1.length
  have hfit : InputFits w a.1 := inputFits a le_rfl
  obtain ⟨v, t, he, ht, hv, hnodup⟩ := decidesInTime_nodup a w le_rfl hfit
  have hvalue : v = if a.1.Nodup then 1 else 0 := by
    change v = 1 ↔ a.1.Nodup at hnodup
    by_cases ha : a.1.Nodup
    · simp [ha, hnodup.mpr ha]
    · simp only [ite_eq_right ha]
      have : v ≠ 1 := fun h => ha (hnodup.mp h)
      lia
  have h := ToRAM.haltsWithResultInTime_padded program_isAdditive hfit he
  rw [hvalue] at h
  refine h.mono ?_
  change 48 * (t + 1) * (w + 1) ≤ _
  have ht' : t + 1 ≤ 17 * (a.1.length + 1) := by lia
  have hw : w + 1 ≤ 3 * (Nat.log 2 (a.1.length + 1) + 1) := by
    have := Nat.log_mono_right (b := 2) (Nat.le_succ a.1.length)
    dsimp [w, logWidth]
    lia
  calc
    _ ≤ 48 * (17 * (a.1.length + 1)) * (3 * (Nat.log 2 (a.1.length + 1) + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 48 ht') hw
    _ = _ := by ring

end Cslib.Algorithms.WordRAM.ElementDistinctness

end
