/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.InductiveCounting.Machine
import Mathlib.Tactic.Linarith

/-!
# Every-prefix logarithmic storage of the complement query machine

The input scan stores a binary position at most the input length. After bootstrap, every
controller register is bounded, including on dishonest branches. Its graph has a fixed
polynomial number of vertices and guessing needs only the binary length of that number.
These statements bound every prefix, rather than only successful computation paths.

## Main results

* `Turing.InductiveCounting.registerBound_le_polynomial`: polynomial bounds for all registers.
* `Turing.InductiveCounting.length_run_le`: logarithmic storage on every choice prefix.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
-/

@[expose] public section

namespace Turing.InductiveCounting

open MultiTapeTM MultiTapeNTM.ConfigurationGraph

private theorem size_le_self (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self

private theorem two_pow_size_le (n : ℕ) : 2 ^ n.size ≤ 2 * (n + 1) := by
  by_cases h : n.size = 0
  · simp only [h, pow_zero]
    omega
  · have hp : 2 ^ (n.size - 1) ≤ n := Nat.lt_size.mp (by omega)
    rw [show n.size = n.size - 1 + 1 by omega, pow_succ]
    omega

/-- The graph bound is a fixed power, independently of the input. -/
def graphExponent (k D : ℕ) : ℕ := D * Fintype.card (Register k)

/-- Polynomial bounds hold for the entire register range checked by the controller. -/
theorem registerBound_le_polynomial {k : ℕ} (D n : ℕ) :
    Cslib.InductiveCounting.registerBound
      (vertexBound (k := k) D n) (guessWidth (k := k) D n) ≤
      (8 * 2 ^ graphExponent k D) * (n + 1) ^ graphExponent k D := by
  let N := vertexBound (k := k) D n
  let E := graphExponent k D
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (ne_of_gt (by
    change 0 < vertexBound (k := k) D n
    rw [vertexBound_eq_pow]
    exact pow_pos (by omega) _))
  have hsize := size_le_self N
  have hpow := two_pow_size_le N
  have hregister : Cslib.InductiveCounting.registerBound N N.size ≤ 8 * N := by
    unfold Cslib.InductiveCounting.registerBound
    omega
  have hpoly : N ≤ 2 ^ E * (n + 1) ^ E := by
    change vertexBound (k := k) D n ≤ _
    rw [vertexBound_eq_pow]
    change (n + 2) ^ E ≤ _
    calc
      (n + 2) ^ E ≤ (2 * (n + 1)) ^ E := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ E * (n + 1) ^ E := mul_pow ..
  change Cslib.InductiveCounting.registerBound N N.size ≤ (8 * 2 ^ E) * (n + 1) ^ E
  calc
    _ ≤ 8 * N := hregister
    _ ≤ 8 * (2 ^ E * (n + 1) ^ E) := Nat.mul_le_mul_left 8 hpoly
    _ = _ := (Nat.mul_assoc ..).symm

variable {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (D : ℕ)

/-- The invariant covers every abstract prefix, including a prefix in the bootstrap scan. -/
def RuntimeInvariant (input : List Bool) (s : Runtime) : Prop :=
  match s.counting with
  | none => s.length ≤ input.length
  | some c => s.length = input.length ∧ Cslib.InductiveCounting.Bounded
      (vertexBound (k := k) D input.length) (guessWidth (k := k) D input.length) c

/-- Every choice prefix satisfies the short-state invariant. -/
theorem runtimeInvariant_run (input : List Bool) (choices : List Bool) :
    RuntimeInvariant (k := k) D input ((queryMachine ntm D).run input choices) := by
  by_cases hshort : choices.length ≤ input.length
  · have hr : (queryMachine ntm D).run input choices = ⟨choices.length, none⟩ := by
      simpa only [NondeterministicQueryMachine.run, queryMachine, Nat.zero_add] using
        replay_scan ntm D input choices (j := 0) (by omega)
    rw [hr]
    exact hshort
  · rw [run_after_bootstrap ntm D input choices (by omega)]
    exact ⟨rfl, Cslib.InductiveCounting.bounded_replay Cslib.InductiveCounting.bounded_initial _⟩

/-- A constant depending only on the fixed machine's graph parameters. -/
def storageConstant (k D : ℕ) : ℕ :=
  40 * (Nat.size (8 * 2 ^ graphExponent k D) + 2 * graphExponent k D + 2) + 4

/-- Every state allowed by the prefix invariant has logarithmic encoded size. -/
theorem length_runtime_le {input : List Bool} {s : Runtime}
    (h : RuntimeInvariant (k := k) D input s) :
    (encRuntime s).length ≤ storageConstant k D * (Nat.log2 input.length + 1) := by
  cases s with
  | mk n counting =>
    cases counting with
    | none =>
      have hn := length_encNat_le_log2 h
      change (encPair encNat (encOption encState) (n, none)).length ≤ _
      simp only [length_encPair, encOption_none, List.length_nil]
      unfold storageConstant
      nlinarith [Nat.zero_le (Nat.log2 input.length)]
    | some c =>
      obtain ⟨rfl, hc⟩ := h
      have hn := length_encNat_le_log2 (Nat.le_refl input.length)
      have hs := length_encState_le_of_registerBound_le hc
        (registerBound_le_polynomial (k := k) D input.length)
      change (encPair encNat (encOption encState) (input.length, some c)).length ≤ _
      simp only [length_encPair, encOption_some, List.length_cons]
      unfold storageConstant
      nlinarith [Nat.zero_le (Nat.log2 input.length)]

/-- The encoded state bound holds on every computation prefix, including rejecting branches. -/
theorem length_run_le (input : List Bool) (choices : List Bool) :
    (encRuntime ((queryMachine ntm D).run input choices)).length ≤
      storageConstant k D * (Nat.log2 input.length + 1) :=
  length_runtime_le D (runtimeInvariant_run ntm D input choices)

end Turing.InductiveCounting
