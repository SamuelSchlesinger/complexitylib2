/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Filter.AtTopBot.Basic
import Cslib.Foundations.Data.Nat.Asymptotics
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

open Filter

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

/-- Linear growth eventually dominates any affine function of `log₂ (n + 2)`. -/
theorem eventually_add_mul_log_le (A B : ℕ) : ∀ᶠ n in atTop, A + B * Nat.log 2 (n + 2) ≤ n := by
  filter_upwards [Nat.eventually_mul_log_le (2 * B + 1) one_lt_two,
    eventually_ge_atTop (2 * (A + 2 * B) + 4)] with n hlog hn
  have h2 : Nat.log 2 (n + 2) ≤ Nat.log 2 n + 1 := by
    calc Nat.log 2 (n + 2) ≤ Nat.log 2 (2 * n) := Nat.log_mono_right (by omega)
      _ = Nat.log 2 n + 1 := by
        rw [mul_comm, Nat.log_mul_base (by norm_num) (by omega)]
  nlinarith

/-- The scheduler budget: `(dimension - 2) * fieldWidth n` eventually exceeds `depth n` by any
fixed amount. -/
theorem eventually_add_depth_le (hnd : num < den) (c : ℕ) :
    ∀ᶠ n in atTop, c + depth num den n ≤ (dimension num den X - 2) * fieldWidth num den X n := by
  set a := den + num * X with ha
  set ℓ := dimension num den X with hℓ
  set h := blockWidth num den X with hh
  set m := (X + 1) * den with hm
  have hℓa : ℓ = 4 * a + 3 := rfl
  have hhpos : 0 < h := blockWidth_pos
  have hmpos : 0 < m := Nat.mul_pos (by omega) (by omega)
  filter_upwards [eventually_add_mul_log_le (ℓ * m * c + ℓ * (X + 1) * den +
      (4 * a + 1) * (m + m * ℓ * h)) (3 * (4 * a + 1) * m)] with n hn
  set p := prefixWidth num den X n with hp
  set L := Nat.log 2 (n + 2) with hL
  set F := fieldWidth num den X n with hF
  set D := depth num den n with hD
  -- Floor bounds.
  have F1 : n * a < m * (p + 1) := by
    rw [hp, prefixWidth, ← ha, ← hm]
    exact Nat.lt_mul_div_succ _ hmpos
  have F2 : p < ℓ * F + ℓ * h + 3 * L := by
    have := Nat.lt_mul_div_succ (p - 3 * L) (Nat.mul_pos (by omega : 0 < ℓ) hhpos)
    rw [hF, fieldWidth, blocks]
    rw [← hp, ← hL, ← hℓ, ← hh]
    have e : ℓ * h * ((p - 3 * L) / (ℓ * h) + 1) =
        ℓ * (h * ((p - 3 * L) / (ℓ * h))) + ℓ * h := by ring
    omega
  have F3 : den * D ≤ num * n + den := by
    rw [hD, depth]
    have := Nat.div_mul_le_self (num * n) den
    nlinarith
  have F4 : ℓ * ((X + 1) * num) + 2 * a + 3 ≤ (4 * a + 1) * a := by
    obtain ⟨e, rfl⟩ : ∃ e, den = num + 1 + e := ⟨den - num - 1, by omega⟩
    rw [ha]
    nlinarith
  have hℓ2 : ℓ - 2 = 4 * a + 1 := by omega
  rw [hℓ2]
  -- Multiply the goal by `ℓ * m` and combine the scaled floor bounds.
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.mul_pos (by omega : 0 < ℓ) hmpos)
  have R1 : ℓ * m * (c + D) = ℓ * m * c + ℓ * (X + 1) * (den * D) := by rw [hm]; ring
  have R2 : ℓ * (X + 1) * (den * D) ≤ ℓ * (X + 1) * (num * n) + ℓ * (X + 1) * den := by
    have := Nat.mul_le_mul_left (ℓ * (X + 1)) F3
    have e : ℓ * (X + 1) * (num * n + den) = ℓ * (X + 1) * (num * n) + ℓ * (X + 1) * den := by
      ring
    omega
  have R3 : ℓ * (X + 1) * (num * n) + (2 * a + 3) * n ≤ (4 * a + 1) * (a * n) := by
    have := Nat.mul_le_mul_right n F4
    have e1 : (ℓ * ((X + 1) * num) + 2 * a + 3) * n =
        ℓ * (X + 1) * (num * n) + (2 * a + 3) * n := by ring
    have e2 : (4 * a + 1) * a * n = (4 * a + 1) * (a * n) := by ring
    omega
  have R4 : (4 * a + 1) * (a * n) ≤ (4 * a + 1) * (m * p) + (4 * a + 1) * m := by
    have := Nat.mul_le_mul_left (4 * a + 1) F1.le
    have e1 : (4 * a + 1) * (n * a) = (4 * a + 1) * (a * n) := by ring
    have e2 : (4 * a + 1) * (m * (p + 1)) = (4 * a + 1) * (m * p) + (4 * a + 1) * m := by ring
    omega
  have R5 : (4 * a + 1) * (m * p) + (4 * a + 1) * m ≤ ℓ * m * ((4 * a + 1) * F) +
      (4 * a + 1) * (m * ℓ * h) + 3 * (4 * a + 1) * m * L := by
    have : (4 * a + 1) * m * (p + 1) ≤ (4 * a + 1) * m * (ℓ * F + ℓ * h + 3 * L) :=
      Nat.mul_le_mul_left _ F2
    have e1 : (4 * a + 1) * m * (p + 1) = (4 * a + 1) * (m * p) + (4 * a + 1) * m := by ring
    have e2 : (4 * a + 1) * m * (ℓ * F + ℓ * h + 3 * L) = ℓ * m * ((4 * a + 1) * F) +
        (4 * a + 1) * (m * ℓ * h) + 3 * (4 * a + 1) * m * L := by ring
    omega
  have R6 : (4 * a + 1) * (m + m * ℓ * h) = (4 * a + 1) * m + (4 * a + 1) * (m * ℓ * h) := by
    ring
  have R7 : n ≤ (2 * a + 3) * n := Nat.le_mul_of_pos_left n (by omega)
  omega

/-- The prefix grows at least linearly: `n < (X + 1) * (prefixWidth n + 1)`. -/
theorem lt_mul_prefixWidth_add_one (hden : 0 < den) (n : ℕ) :
    n < (X + 1) * (prefixWidth num den X n + 1) := by
  have F1 : n * (den + num * X) < (X + 1) * den * (prefixWidth num den X n + 1) :=
    Nat.lt_mul_div_succ _ (Nat.mul_pos (by omega) hden)
  have : n * den ≤ n * (den + num * X) := Nat.mul_le_mul_left _ (by omega)
  have e : (X + 1) * den * (prefixWidth num den X n + 1) =
      den * ((X + 1) * (prefixWidth num den X n + 1)) := by ring
  have e2 : n * den = den * n := by ring
  exact Nat.lt_of_mul_lt_mul_left (a := den) (by omega)

/-- Eventually the field exponent has at least `c` blocks. -/
theorem eventually_le_blocks (hden : 0 < den) (c : ℕ) :
    ∀ᶠ n in atTop, c ≤ blocks num den X n := by
  have hℓh : 0 < dimension num den X * blockWidth num den X :=
    Nat.mul_pos (by have := three_le_dimension (num := num) (den := den) (X := X); omega)
      blockWidth_pos
  filter_upwards [eventually_add_mul_log_le ((X + 1) * (c * (dimension num den X *
      blockWidth num den X) + 1)) (3 * (X + 1))] with n hn
  have hp := lt_mul_prefixWidth_add_one (X := X) (num := num) hden n
  unfold blocks
  apply (Nat.le_div_iff_mul_le hℓh).mpr
  have e : (X + 1) * (c * (dimension num den X * blockWidth num den X) + 1) +
      3 * (X + 1) * Nat.log 2 (n + 2) =
      (X + 1) * (c * (dimension num den X * blockWidth num den X) + 1 +
        3 * Nat.log 2 (n + 2)) := by ring
  have : c * (dimension num den X * blockWidth num den X) + 3 * Nat.log 2 (n + 2) ≤
      prefixWidth num den X n := by
    by_contra hlt
    have := Nat.mul_le_mul_left (X + 1) (show prefixWidth num den X n + 1 ≤
      c * (dimension num den X * blockWidth num den X) + 1 + 3 * Nat.log 2 (n + 2) by omega)
    omega
  omega

/-- Eventually the suffix has at least `c` bits, when the slack is positive. -/
theorem eventually_le_suffixWidth (hnd : num < den) (hX : 0 < X) (c : ℕ) :
    ∀ᶠ n in atTop, c ≤ suffixWidth num den X n := by
  filter_upwards [eventually_ge_atTop ((X + 1) * den * c)] with n hn
  have h := mul_le_suffixWidth (X := X) hnd.le n
  have h1 : n ≤ X * (den - num) * n :=
    Nat.le_mul_of_pos_left n (Nat.mul_pos hX (by omega))
  by_contra hlt
  have := Nat.mul_lt_mul_of_pos_left (show suffixWidth num den X n < c by omega)
    (Nat.mul_pos (by omega : 0 < X + 1) (by omega : 0 < den))
  omega

end Cslib.Circuits.Boolean.MassProduction.Sharp
