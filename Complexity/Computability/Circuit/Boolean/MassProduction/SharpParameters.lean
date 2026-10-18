/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Parameters for sharp mass production

Fix a rational copy exponent `γ = num / den < 1` and a slack `X`. Inputs of length `n` are split
into a prefix of `prefixWidth n ≈ (γ + (1 - γ) / (X + 1)) n` bits and a suffix of the remaining
`suffixWidth n ≥ (X / (X + 1)) (1 - γ) n` bits (`mul_le_suffixWidth`). The prefix is encoded in
line-parity codes on `K ^ dimension` over a field of `2 ^ fieldWidth n` elements, where
`fieldWidth n` is a multiple of `blockWidth` and `dimension ≤ 2 ^ blockWidth`. Batches have
`2 ^ depth n` requests, where `depth n = ⌊γ n⌋ + 1`.

The dimension is large enough that `(dimension - 2) * fieldWidth n` eventually exceeds
`depth n` by any fixed amount (`eventually_add_depth_le`): this is the projective-direction
budget of the scheduler. The field width leaves `3 log₂ (n + 2)` prefix bits unused
(`dimension_mul_fieldWidth_le`), so a single code copy is negligible against `2 ^ prefixWidth n`.

## Main definitions

* `Cslib.Circuits.Boolean.MassProduction.Sharp.prefixWidth`,
  `Cslib.Circuits.Boolean.MassProduction.Sharp.suffixWidth`: the input split.
* `Cslib.Circuits.Boolean.MassProduction.Sharp.dimension`,
  `Cslib.Circuits.Boolean.MassProduction.Sharp.blockWidth`,
  `Cslib.Circuits.Boolean.MassProduction.Sharp.blocks`,
  `Cslib.Circuits.Boolean.MassProduction.Sharp.fieldWidth`: the code geometry.
* `Cslib.Circuits.Boolean.MassProduction.Sharp.depth`: the batch exponent.

## References

* Simplifies `MassProduction/Nonuniform/{GeometricSlopes,BlockParameters,
  CoefficientParameters}.lean` in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.MassProduction.Sharp

variable (num den X : ℕ)

/-- The prefix width `⌊n (den + num X) / ((X + 1) den)⌋`. -/
def prefixWidth (n : ℕ) : ℕ :=
  n * (den + num * X) / ((X + 1) * den)

/-- The suffix width, the rest of the input. -/
def suffixWidth (n : ℕ) : ℕ :=
  n - prefixWidth num den X n

/-- The dimension of the code geometry. -/
def dimension : ℕ :=
  4 * (den + num * X) + 3

/-- The block width of the field exponent: `dimension ≤ 2 ^ blockWidth`. -/
def blockWidth : ℕ :=
  Nat.clog 2 (dimension num den X)

/-- The number of blocks of the field exponent. -/
def blocks (n : ℕ) : ℕ :=
  (prefixWidth num den X n - 3 * Nat.log 2 (n + 2)) / (dimension num den X * blockWidth num den X)

/-- The field has `2 ^ fieldWidth n` elements. -/
def fieldWidth (n : ℕ) : ℕ :=
  blockWidth num den X * blocks num den X n

/-- Batches have `2 ^ depth n` requests. -/
def depth (n : ℕ) : ℕ :=
  num * n / den + 1

variable {num den X}

theorem prefixWidth_le (hnd : num ≤ den) (n : ℕ) : prefixWidth num den X n ≤ n := by
  rcases Nat.eq_zero_or_pos den with rfl | hden
  · simp [prefixWidth]
  apply Nat.div_le_of_le_mul
  calc n * (den + num * X) ≤ n * ((X + 1) * den) := by
        apply Nat.mul_le_mul_left
        nlinarith
    _ = (X + 1) * den * n := by ring

theorem prefixWidth_add_suffixWidth (hnd : num ≤ den) (n : ℕ) :
    prefixWidth num den X n + suffixWidth num den X n = n :=
  Nat.add_sub_of_le (prefixWidth_le hnd n)

/-- The suffix keeps at least a `X / (X + 1)` fraction of `(1 - γ) n` bits. -/
theorem mul_le_suffixWidth (hnd : num ≤ den) (n : ℕ) :
    X * (den - num) * n ≤ (X + 1) * den * suffixWidth num den X n := by
  have hp : (X + 1) * den * prefixWidth num den X n ≤ n * (den + num * X) := by
    unfold prefixWidth
    rw [mul_comm]
    exact Nat.div_mul_le_self _ _
  obtain ⟨e, rfl⟩ : ∃ e, den = num + e := ⟨den - num, by omega⟩
  rw [show num + e - num = e by omega]
  unfold suffixWidth
  rw [Nat.mul_sub]
  have h1 : (X + 1) * (num + e) * n = n * (num + e + num * X) + X * e * n := by ring
  omega

theorem three_le_dimension : 3 ≤ dimension num den X := by
  unfold dimension
  omega

theorem dimension_le_two_pow_blockWidth : dimension num den X ≤ 2 ^ blockWidth num den X :=
  Nat.le_pow_clog (by norm_num) _

theorem blockWidth_pos : 0 < blockWidth num den X := by
  unfold blockWidth
  have h := three_le_dimension (num := num) (den := den) (X := X)
  exact Nat.clog_pos (by norm_num) (by omega)

/-- The code points use all but `3 log₂ (n + 2)` of the prefix bits. -/
theorem dimension_mul_fieldWidth_le (n : ℕ) :
    dimension num den X * fieldWidth num den X n + 3 * Nat.log 2 (n + 2) ≤
      prefixWidth num den X n ∨ fieldWidth num den X n = 0 := by
  by_cases h : 3 * Nat.log 2 (n + 2) ≤ prefixWidth num den X n
  · left
    have := Nat.div_mul_le_self (prefixWidth num den X n - 3 * Nat.log 2 (n + 2))
      (dimension num den X * blockWidth num den X)
    unfold fieldWidth blocks
    calc dimension num den X * (blockWidth num den X *
          ((prefixWidth num den X n - 3 * Nat.log 2 (n + 2)) /
            (dimension num den X * blockWidth num den X))) + 3 * Nat.log 2 (n + 2)
        = (prefixWidth num den X n - 3 * Nat.log 2 (n + 2)) /
            (dimension num den X * blockWidth num den X) *
            (dimension num den X * blockWidth num den X) + 3 * Nat.log 2 (n + 2) := by ring
      _ ≤ prefixWidth num den X n := by omega
  · right
    unfold fieldWidth blocks
    rw [Nat.sub_eq_zero_of_le (by omega), Nat.zero_div, Nat.mul_zero]

end Cslib.Circuits.Boolean.MassProduction.Sharp
