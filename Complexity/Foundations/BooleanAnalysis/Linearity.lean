/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Convolution
public import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Linearity testing

A Boolean function on the cube is *linear* when it turns sums into sums,
`f (x + y) = f x + f y`, where bits add modulo two (`^^`) and bit strings add coordinatewise. The
linear functions are exactly the parities (`BitString.exists_eq_parityOn_iff`).

The *Blum–Luby–Rubinfeld test* queries `f` at independent uniformly random `x` and `y` and at
`x + y`, and accepts when `f x + f y = f (x + y)`; `BitString.blrAcceptance f` is the probability
that it accepts. Reading `f` as the function `F x = (-1) ^ f x`, the test accepts with probability
`1/2 + 1/2 ∑_S F̂(S)³` (`BitString.blrAcceptance_eq_sum_fourierCoeff_pow_three`), by the
convolution theorem. Parities pass with probability one (`BitString.blrAcceptance_parityOn`).
Conversely, a function passing with probability at least `1 - ε` differs from some parity on at
most an `ε` fraction of the inputs
(`BitString.exists_hammingDist_parityOn_le_of_le_blrAcceptance`): the squares `F̂(S)²` sum to one
by Parseval's identity, so `∑_S F̂(S)³ ≤ max_S F̂(S)`, and `F̂(S)` is one minus twice the relative
Hamming distance from `f` to the parity on `S` (`BitString.fourierCoeff_signVal`)
[O'Donnell, Section 1.6][ODonnell2014], [BlumLubyRubinfeld1993].

## Main definitions

* `Cslib.BitString.blrAcceptance`: the acceptance probability of the Blum–Luby–Rubinfeld test.

## Main results

* `Cslib.BitString.exists_eq_parityOn_iff`: the linear Boolean functions are the parities.
* `Cslib.BitString.parityOn_xor`: parities are linear.
* `Cslib.BitString.expect_signVal_mul_signVal`, `Cslib.BitString.fourierCoeff_signVal`: the
  correlation of two Boolean functions is one minus twice their relative Hamming distance.
* `Cslib.BitString.blrAcceptance_eq_sum_fourierCoeff_pow_three`: the acceptance probability in
  terms of the Fourier coefficients.
* `Cslib.BitString.blrAcceptance_parityOn`: completeness of the test.
* `Cslib.BitString.exists_hammingDist_parityOn_le_of_le_blrAcceptance`: soundness of the test.

## References

* [M. Blum, M. Luby, R. Rubinfeld, *Self-testing/correcting with applications to numerical
  problems*][BlumLubyRubinfeld1993]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {n : ℕ}

/-! ### Linear functions -/

/-- **Parities are linear**: the parity of a sum of bit strings is the exclusive or of the
parities. -/
theorem parityOn_xor (S : Finset (Fin n)) (x y : BitString n) :
    parityOn S (fun i => x i ^^ y i) = (parityOn S x ^^ parityOn S y) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [parityOn_insert hi, parityOn_insert hi, parityOn_insert hi, ih]
    simp only [Bool.xor_assoc, Bool.xor_left_comm (y i)]

/-- **The linear Boolean functions are the parities**: a Boolean function turns the exclusive or
of bit strings into the exclusive or of its values exactly when it is the parity of some set of
coordinates [O'Donnell, Definition 1.28][ODonnell2014]. -/
theorem exists_eq_parityOn_iff {f : BooleanFunction n} :
    (∃ S, f = parityOn S) ↔ ∀ x y, f (fun i => x i ^^ y i) = (f x ^^ f y) := by
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨S, rfl⟩
    exact parityOn_xor S
  -- `a i` is the value of `f` at the unit vector of `i`.
  set a : BitString n := fun i => f fun j => decide (j = i)
  have hT (T : Finset (Fin n)) : f (fun j => decide (j ∈ T)) = parityOn T a := by
    induction T using Finset.induction_on with
    | empty => simpa using hf (fun _ => false) (fun _ => false)
    | insert i T hi ih =>
      have h : (fun j => decide (j ∈ insert i T)) = fun j => decide (j = i) ^^ decide (j ∈ T) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [hi]
        · simp [hj]
      rw [h, hf, ih, parityOn_insert hi]
  refine ⟨({i | a i = true} : Finset (Fin n)), funext fun x => ?_⟩
  calc f x = f fun j => decide (j ∈ ({j | x j = true} : Finset (Fin n))) := by simp
    _ = parityOn {j | x j = true} a := hT _
    _ = parityOn {i | a i = true} x := by simp only [parityOn, filter_filter, and_comm]

/-! ### Distance and correlation -/

/-- **Correlation is one minus twice the distance**: the correlation of two Boolean functions,
read as signs, is one minus twice the fraction of the inputs on which they differ
[O'Donnell, Section 1.4][ODonnell2014]. -/
theorem expect_signVal_mul_signVal (f g : BooleanFunction n) :
    𝔼 x, signVal (f x) * signVal (g x) = 1 - 2 * hammingDist f g / 2 ^ n := by
  have h (x : BitString n) :
      signVal (f x) * signVal (g x) = 1 - 2 * if f x ≠ g x then 1 else 0 := by
    rw [signVal_mul_signVal]
    by_cases hx : f x = g x <;> norm_num [hx]
  rw [hammingDist]
  simp only [h, expect_eq_sum_div_card, sum_sub_distrib, ← mul_sum, sum_boole, sum_const,
    card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Nat.cast_pow, Nat.cast_ofNat]
  rw [sub_div, div_self (pow_ne_zero n two_ne_zero)]

/-- The Fourier coefficient on `S` of a Boolean function read as signs is one minus twice the
relative Hamming distance from the function to the parity on `S`. -/
theorem fourierCoeff_signVal (f : BooleanFunction n) (S : Finset (Fin n)) :
    fourierCoeff (fun x => signVal (f x)) S = 1 - 2 * hammingDist f (parityOn S) / 2 ^ n := by
  simp only [fourierCoeff, chi_eq_signVal_parityOn]
  exact expect_signVal_mul_signVal f (parityOn S)

/-! ### The Blum–Luby–Rubinfeld test -/

/-- The acceptance probability of the Blum–Luby–Rubinfeld linearity test on `f`: the probability,
over independent uniformly random bit strings `x` and `y`, that `f x + f y = f (x + y)`, where
bits add modulo two and bit strings add coordinatewise. -/
noncomputable def blrAcceptance (f : BooleanFunction n) : ℝ :=
  𝔼 x, 𝔼 y, if (f x ^^ f y) = f (fun i => x i ^^ y i) then 1 else 0

/-- **The acceptance probability of the BLR test**: reading `f` as signs, the test accepts with
probability `1/2 + 1/2 ∑_S F̂(S)³`. -/
theorem blrAcceptance_eq_sum_fourierCoeff_pow_three (f : BooleanFunction n) :
    blrAcceptance f = 1 / 2 + 1 / 2 * ∑ S, fourierCoeff (fun x => signVal (f x)) S ^ 3 := by
  set F : BitString n → ℝ := fun x => signVal (f x)
  have hind (a b c : Bool) : (if (a ^^ b) = c then (1 : ℝ) else 0) =
      1 / 2 + 1 / 2 * (signVal a * (signVal b * signVal c)) := by
    cases a <;> cases b <;> cases c <;> norm_num
  have hconv : 𝔼 x, 𝔼 y, F x * (F y * F (fun i => x i ^^ y i)) =
      𝔼 x, F x * convolution F F x := by
    simp only [convolution, mul_expect]
  calc blrAcceptance f = 1 / 2 + 1 / 2 * 𝔼 x, 𝔼 y, F x * (F y * F (fun i => x i ^^ y i)) := by
        simp only [blrAcceptance, hind, expect_add_distrib, ← mul_expect, Fintype.expect_const]
        rfl
    _ = 1 / 2 + 1 / 2 * ∑ S, fourierCoeff F S ^ 3 := by
        rw [hconv, expect_mul_eq_sum_fourierCoeff_mul]
        simp only [fourierCoeff_convolution, pow_three]

/-- **Completeness of the BLR test**: parities pass with probability one. -/
theorem blrAcceptance_parityOn (S : Finset (Fin n)) : blrAcceptance (parityOn S) = 1 := by
  simp [blrAcceptance, parityOn_xor]

/-- **Soundness of the BLR test**: if the test accepts `f` with probability at least `1 - ε`,
then `f` differs from some parity on at most an `ε` fraction of the inputs
[O'Donnell, Theorem 1.30][ODonnell2014]. -/
theorem exists_hammingDist_parityOn_le_of_le_blrAcceptance {f : BooleanFunction n} {ε : ℝ}
    (h : 1 - ε ≤ blrAcceptance f) : ∃ S, (hammingDist f (parityOn S) : ℝ) / 2 ^ n ≤ ε := by
  rw [blrAcceptance_eq_sum_fourierCoeff_pow_three] at h
  set c := fourierCoeff fun x => signVal (f x)
  obtain ⟨S, -, hS⟩ := exists_max_image univ c univ_nonempty
  refine ⟨S, ?_⟩
  have hc : ∑ T, c T ^ 3 ≤ c S := calc
    ∑ T, c T ^ 3 ≤ ∑ T, c S * c T ^ 2 := sum_le_sum fun T _ => by
        rw [pow_succ, mul_comm]
        exact mul_le_mul_of_nonneg_right (hS T (mem_univ T)) (sq_nonneg _)
    _ = c S := by rw [← mul_sum, sum_fourierCoeff_sq_signVal, mul_one]
  have hcS : c S = 1 - 2 * hammingDist f (parityOn S) / 2 ^ n := fourierCoeff_signVal f S
  rw [mul_div_assoc] at hcS
  linarith

end Cslib.BitString
