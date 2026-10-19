/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.Optimization

/-!
# Iterating for a number of steps given as input

A circuit with `n + m` inputs reads a state from its first `n` inputs and a number of steps from
its last `m` inputs, in binary with the least significant bit first, and returns that iterate of
`f` (`inputTimeIterate`). Binary powering builds it from fixed powers: stage `j` applies a circuit
for `f^[2 ^ j]` to the current state, and bit `j` of the time selects its result or the current
state, at four gates per state bit (`synthesis_binary_powering`). With the fixed-power circuits
of size `40000 * powerBudget n s (2 ^ n) L`, an `m`-bit time costs at most
`m * (40000 * powerBudget n s (2 ^ n) L + 4 * n)` (`variable_time`), and
`m * (120000 * optimizedBudget n s (2 ^ n) + 4 * n)` with the balanced parameter
(`variable_time_optimized`). The cost is linear in `m`; a bound additive in `m`, which first
reduces the time modulo the cycle length, needs cycle labels and is not proved here.

The circuits are native De Morgan circuits: every NOT, AND and OR gate and every constant is
charged, while wiring and fanout are free. They exist for each `m`, because the fixed-power
circuits do; nothing here bounds the time to construct them.

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.inputTimeIterate`: the iterate whose number of steps is part
  of the input.

## Main results

* `Cslib.Circuits.Boolean.Iteration.synthesis_binary_powering`: binary powering from circuits for
  the powers `f^[2 ^ j]`.
* `Cslib.Circuits.Boolean.Iteration.binary_powering`: its circuit form.
* `Cslib.Circuits.Boolean.Iteration.variable_time`,
  `Cslib.Circuits.Boolean.Iteration.variable_time_optimized`: input times through fixed powers.

## References

* Adapted from `lean/Proofs/{VariableTime,BinaryNumbers}.lean` in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

variable {n m : ℕ}

/-- The state after `T` steps of `f`, where the first `n` of the `n + m` input bits are the state
and the last `m` bits are `T` in binary, least significant bit first. -/
def inputTimeIterate (f : BitString n → BitString n) (m : ℕ) (y : BitString (n + m)) :
    BitString n :=
  f^[(word fun j : Fin m => y (Fin.natAdd n j)).toNat] fun i => y (Fin.castAdd m i)

/-- Without time bits the state is returned unchanged. -/
theorem inputTimeIterate_zero (f : BitString n → BitString n) (y : BitString (n + 0)) :
    inputTimeIterate f 0 y = fun i => y (Fin.castAdd 0 i) := by
  have h : (word fun j : Fin 0 => y (Fin.natAdd n j)).toNat = 0 := by
    simpa only [pow_zero, Nat.lt_one_iff] using (word fun j : Fin 0 => y (Fin.natAdd n j)).isLt
  simp only [inputTimeIterate, h, Function.iterate_zero, id_eq]

/-- Reading one more bit of a binary time adds that bit's power of two. -/
theorem toNat_word_mod_two_pow_succ (bits : BitString m) {j : ℕ} (hj : j < m) :
    (word bits).toNat % 2 ^ (j + 1) =
      (word bits).toNat % 2 ^ j + if bits ⟨j, hj⟩ then 2 ^ j else 0 := by
  have hbit : (word bits).toNat / 2 ^ j % 2 = if bits ⟨j, hj⟩ then 1 else 0 := by
    have ht : bits ⟨j, hj⟩ = decide ((word bits).toNat / 2 ^ j % 2 = 1) := by
      rw [← getLsbD_word bits ⟨j, hj⟩, ← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
    have hlt := Nat.mod_lt ((word bits).toNat / 2 ^ j) (show 0 < 2 by decide)
    rw [ht]
    by_cases h : (word bits).toNat / 2 ^ j % 2 = 1
    · simp only [h, decide_true, ite_true]
    · simp only [h, decide_false, Bool.false_eq_true, ite_false]
      omega
  rw [Nat.mod_pow_succ, hbit]
  split_ifs <;> simp

/-- Applying `f^[2 ^ j]` exactly when bit `j` is set extends the time read so far by that bit. -/
theorem iterate_toNat_word_mod_two_pow_succ {α : Type*} (f : α → α) (bits : BitString m)
    {j : ℕ} (hj : j < m) (y : α) :
    f^[(word bits).toNat % 2 ^ (j + 1)] y =
      if bits ⟨j, hj⟩ then f^[2 ^ j] (f^[(word bits).toNat % 2 ^ j] y)
      else f^[(word bits).toNat % 2 ^ j] y := by
  rw [toNat_word_mod_two_pow_succ bits hj]
  split_ifs
  · rw [← Function.iterate_add_apply, Nat.add_comm]
  · rfl

/-- **Binary powering.** If every power `f^[2 ^ j]` with `j < m` has a circuit of size at most
`C`, then `T` steps of `f` from an available state, with `T` given by `m` available bits, cost at
most `m * (C + 4 * n)` gates: one power circuit and one multiplexer per bit. -/
theorem synthesis_binary_powering {a : ℕ} (f : BitString n → BitString n) (C : ℕ)
    (hpowers : ∀ j < m, ∃ c : Circuit signature n n,
      c.Computes interpretation f^[2 ^ j] ∧ c.size ≤ C)
    (s : Set (BooleanFunction a)) (init : BitString a → BitString n)
    (bits : BitString a → BitString m) (hi : wires init ⊆ s) (hb : wires bits ⊆ s) :
    Synthesis interpretation s (wires fun x => f^[(word (bits x)).toNat] (init x))
      (m * (C + 4 * n)) := by
  let state := fun j x => f^[(word (bits x)).toNat % 2 ^ j] (init x)
  let q := fun j => wires (state j)
  have hz : q 0 ⊆ s := by simpa only [q, state, pow_zero, Nat.mod_one,
    Function.iterate_zero, id_eq] using hi
  have hstep (j : ℕ) (hj : j < m) :
      Synthesis interpretation (s ∪ Synthesis.stages q j) (q (j + 1)) (C + 4 * n) := by
    obtain ⟨pow, hp, hs⟩ := hpowers j hj
    let src := s ∪ Synthesis.stages q j
    have hav : wires (state j) ⊆ src := fun _ h => Or.inr (Synthesis.subset_stages q le_rfl h)
    have hpow := Synthesis.circuit (I := interpretation) (s := src) pow (fun i x => state j x i)
      (fun i => hav ⟨i, rfl⟩)
    have hmux := synthesis_bits_mux (src ∪ wires fun x => pow.eval interpretation (state j x))
      (fun x => pow.eval interpretation (state j x)) (state j) (fun x => bits x ⟨j, hj⟩)
      (fun _ h => Or.inr h) (fun _ h => Or.inl (hav h)) (Or.inl (Or.inl (hb ⟨⟨j, hj⟩, rfl⟩)))
    have he : (fun x => if bits x ⟨j, hj⟩ then pow.eval interpretation (state j x)
        else state j x) = state (j + 1) := by
      funext x
      rw [hp]
      exact (iterate_toNat_word_mod_two_pow_succ f (bits x) hj (init x)).symm
    rw [he] at hmux
    exact (hpow.trans hmux).mono Set.Subset.rfl Set.Subset.rfl (Nat.add_le_add_right hs _)
  have h := (Synthesis.steps q _ m hz hstep).mono Set.Subset.rfl
    (Synthesis.subset_stages q le_rfl) le_rfl
  simpa only [q, state, Nat.mod_eq_of_lt (word _).isLt] using h

/-- **Binary powering**, as a circuit on `n + m` inputs. -/
theorem binary_powering (f : BitString n → BitString n) (m C : ℕ)
    (hpowers : ∀ j < m, ∃ c : Circuit signature n n,
      c.Computes interpretation f^[2 ^ j] ∧ c.size ≤ C) :
    ∃ out : Circuit signature (n + m) n,
      out.Computes interpretation (inputTimeIterate f m) ∧ out.size ≤ m * (C + 4 * n) :=
  (synthesis_binary_powering f C hpowers (inputs (n + m))
    (fun y i => y (Fin.castAdd m i)) (fun y j => y (Fin.natAdd n j))
    (by rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩) (by rintro _ ⟨j, rfl⟩; exact ⟨_, rfl⟩)
    ).exists_circuit_outputs

/-- **Input times.** For every `0 < L ≤ 2 ^ n`, some circuit of size at most
`m * (40000 * powerBudget n c.size (2 ^ n) L + 4 * n)` iterates `c` for a number of steps given
by `m` input bits. -/
theorem variable_time (c : Circuit signature n n) (m L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature (n + m) n,
      out.Computes interpretation (inputTimeIterate (c.eval interpretation) m) ∧
      out.size ≤ m * (40000 * powerBudget n c.size (2 ^ n) L + 4 * n) :=
  binary_powering _ m _ fun j _ => fixed_power n c (2 ^ j) L hL hLN

/-- **Square-root input times.** -/
theorem variable_time_optimized (c : Circuit signature n n) (m : ℕ) :
    ∃ out : Circuit signature (n + m) n,
      out.Computes interpretation (inputTimeIterate (c.eval interpretation) m) ∧
      (out.size : ℝ) ≤ m * (120000 * optimizedBudget n c.size (2 ^ n) + 4 * n) := by
  obtain ⟨L, hL, hLN, hopt⟩ := exists_powerBudget_le_optimizedBudget n c.size (2 ^ n) le_rfl
  obtain ⟨out, hout, hs⟩ := variable_time c m L hL hLN
  refine ⟨out, hout, ?_⟩
  have hs' : (out.size : ℝ) ≤ m * (40000 * (powerBudget n c.size (2 ^ n) L : ℝ) + 4 * n) := by
    exact_mod_cast hs
  exact hs'.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

end Cslib.Circuits.Boolean.Iteration
