/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.RAM.Cost

/-!
# Repeated squaring: why unit cost is unsound

The unit cost measure charges a RAM one unit per instruction, however large the numbers involved.
Without multiplication this is harmless: apart from loading a constant, an instruction at most
doubles the largest number held, and a Turing machine simulates a RAM running in unit time `T(n)`
within time `T(n) ^ 3` [Cook and Reckhow, Section 4, Theorem 2][CookReckhow1973]. With
multiplication it is not. The program `Cslib.RAM.repeatedSquaring k`, whose only constant is `2`,
squares register `1` a total of `k` times, so after `k + 1` steps register `1` holds `2 ^ 2 ^ k`.
That number has `2 ^ k + 1` binary digits, so a Turing machine needs at least `2 ^ k` steps just
to write it down: unit-cost RAM time is not polynomially related to Turing machine time. Hartmanis
and Simon showed much more: under unit cost, RAMs with multiplication and bitwise Boolean
operations decide in polynomial time exactly the languages that Turing machines decide in
polynomial space [Hartmanis and Simon, Abstract][HartmanisSimon1974].

The logarithmic cost measure has no such gap. The same run takes logarithmic time more than
`2 ^ k`, as it must, since logarithmic time bounds the length of every number held
(`Cslib.RAM.bitLength_read_run_le`).

## Main definitions

* `Cslib.RAM.repeatedSquaring`: the program that squares register `1` a given number of times.

## Main results

* `Cslib.RAM.run_repeatedSquaring`: the state after each step of the program.
* `Cslib.RAM.time_unitCost_repeatedSquaring`: the run takes unit time `k + 1`.
* `Cslib.RAM.two_pow_lt_time_logCost_repeatedSquaring`: the run takes logarithmic time more than
  `2 ^ k`.
* `Cslib.RAM.logGap_squaring`: the gap between the two measures on the same run.

## References

* [S. A. Cook and R. A. Reckhow, *Time bounded random access machines*][CookReckhow1973]
* [J. Hartmanis and J. Simon, *On the power of multiplication in random access
  machines*][HartmanisSimon1974]
-/

@[expose] public section

namespace Cslib.RAM

/-- The `k`-fold repeated-squaring program: put the constant `2` into register `1`, then square
register `1` a total of `k` times. -/
def repeatedSquaring (k : ℕ) : Program := .const 1 2 :: List.replicate k (.mul 1 1 1)

variable {j k : ℕ}

@[simp]
theorem length_repeatedSquaring : (repeatedSquaring k).length = k + 1 := by
  simp [repeatedSquaring]

/-- After `j + 1` steps from the all-zero state, for `j ≤ k`, the program counter is `j + 1`,
register `1` holds `2 ^ 2 ^ j`, and every other register still holds `0`. -/
theorem run_repeatedSquaring (hj : j ≤ k) :
    run (repeatedSquaring k) (j + 1) (State.init []) =
      ⟨j + 1, (State.init []).regs.write 1 (2 ^ 2 ^ j)⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hi : (repeatedSquaring k)[j + 1]? = some (.mul 1 1 1) := by
      simp [repeatedSquaring, Nat.lt_of_succ_le hj]
    rw [run_succ', ih (Nat.le_of_succ_le hj), step_of_getElem? (s := ⟨j + 1, _⟩) hi]
    ext1
    · rfl
    · simp only [Instr.exec, URM.Regs.write_read_self]
      rw [URM.Regs.write, URM.Regs.write, URM.Regs.write, Function.update_idem, ← pow_add,
        ← two_mul, ← pow_succ']

/-- The run halts after `k + 1` steps. -/
theorem isHalted_run_repeatedSquaring :
    (run (repeatedSquaring k) (k + 1) (State.init [])).isHalted (repeatedSquaring k) := by
  simp [run_repeatedSquaring le_rfl]

/-- After `k + 1` steps, register `1` holds `2 ^ 2 ^ k`. -/
theorem read_run_repeatedSquaring :
    (run (repeatedSquaring k) (k + 1) (State.init [])).regs.read 1 = 2 ^ 2 ^ k := by
  rw [run_repeatedSquaring le_rfl, URM.Regs.write_read_self]

/-- Under unit cost, the run takes time `k + 1`. -/
theorem time_unitCost_repeatedSquaring :
    time unitCost (repeatedSquaring k) (k + 1) (State.init []) = k + 1 :=
  time_unitCost fun j hj => by
    cases j with
    | zero => simp
    | succ j =>
      rw [run_repeatedSquaring (by omega)]
      simpa using hj

/-- Under logarithmic cost, the run takes time more than `2 ^ k`: it builds a number of length
`2 ^ k + 1`. -/
theorem two_pow_lt_time_logCost_repeatedSquaring :
    2 ^ k < time logCost (repeatedSquaring k) (k + 1) (State.init []) := by
  have h := bitLength_read_run_le (p := repeatedSquaring k) (s := State.init []) (b := 1)
    (by simp) (k + 1) 1
  rw [read_run_repeatedSquaring, bitLength_two_pow] at h
  have := Nat.two_pow_pos k
  omega

/-- **Unit cost is unsound.** The repeated-squaring program `repeatedSquaring k`, whose only
constant is `2`, halts after `k + 1` steps from the all-zero state with `2 ^ 2 ^ k` in register
`1`. Under unit cost the run takes time `k + 1`; under logarithmic cost it takes time more than
`2 ^ k`. A Turing machine writing `2 ^ 2 ^ k` in binary writes its `2 ^ k + 1` digits, which takes
at least `2 ^ k` steps, so unit-cost RAM time is not polynomially related to Turing machine time.
Logarithmic time has no such gap: it bounds the length of every number held
(`Cslib.RAM.bitLength_read_run_le`). -/
theorem logGap_squaring (k : ℕ) :
    (run (repeatedSquaring k) (k + 1) (State.init [])).isHalted (repeatedSquaring k) ∧
      (run (repeatedSquaring k) (k + 1) (State.init [])).regs.read 1 = 2 ^ 2 ^ k ∧
      time unitCost (repeatedSquaring k) (k + 1) (State.init []) = k + 1 ∧
      2 ^ k < time logCost (repeatedSquaring k) (k + 1) (State.init []) :=
  ⟨isHalted_run_repeatedSquaring, read_run_repeatedSquaring, time_unitCost_repeatedSquaring,
    two_pow_lt_time_logCost_repeatedSquaring⟩

end Cslib.RAM

end
