/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Bernoulli
public import Complexity.Foundations.Data.BitString.Influence
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith

/-!
# Noise stability and noise sensitivity

Flipping each bit of a string `x` independently with probability `(1 - ρ) / 2` gives a random
string `y` that is *`ρ`-correlated* with `x`. The *noise operator* `T_ρ` (`BitString.noiseOp`)
averages a real function over this noise, `T_ρ f x = 𝔼_y f y`. It damps the Fourier coefficient of
`S` by `ρ ^ |S|` (`BitString.fourierCoeff_noiseOp`), so it has Fourier expansion
`∑_S ρ ^ |S| f̂(S) χ_S` (`BitString.noiseOp_eq_sum`) and the noise operators form a semigroup,
`T_ρ T_σ = T_{ρ σ}` (`BitString.noiseOp_noiseOp`).

The *noise stability* `Stab_ρ[f] = 𝔼_x f x T_ρ f x` (`BitString.noiseStability`) is the
correlation of `f` at two `ρ`-correlated strings. It is `∑_S ρ ^ |S| f̂(S) ^ 2`
(`BitString.noiseStability_eq_sum`), so on `0 ≤ ρ ≤ 1` it increases with `ρ` from the squared
mean `(𝔼 f) ^ 2` to the second moment `𝔼 f ^ 2`.

The *noise sensitivity* `NS_δ[f]` of a Boolean function (`BitString.noiseSensitivity`) is the
probability that `f x ≠ f y` when `y` flips each bit of a uniform `x` independently with
probability `δ`. Reading `f` as the function `F = (-1) ^ f` with values `±1`, it is
`NS_δ[f] = 1 / 2 - 1 / 2 Stab_{1 - 2 δ}[F]` (`BitString.noiseSensitivity_eq_noiseStability`),
hence `NS_δ[f] = ∑_S (1 - (1 - 2 δ) ^ |S|) / 2 F̂(S) ^ 2` (`BitString.noiseSensitivity_eq_sum`)
and `NS_δ[f] ≤ δ I[F]`, at most `δ` times the total influence
(`BitString.noiseSensitivity_le_mul_totalInfluence`) [O'Donnell, Section 2.4][ODonnell2014].

The noise is a random mask of `BooleanAnalysis.bernoulliAverage`. Its coordinates are independent:
the average of a product of functions of the separate coordinates factorizes
(`BooleanAnalysis.bernoulliAverage_prod`), so the character of `S` averages to `(1 - 2 p) ^ |S|`
over a mask of rate `p` (`BitString.bernoulliAverage_chi`).

## Main definitions

* `Cslib.BitString.noiseOp`: the noise operator `T_ρ`.
* `Cslib.BitString.noiseStability`: the noise stability of a real function.
* `Cslib.BitString.noiseSensitivity`: the noise sensitivity of a Boolean function.

## Main results

* `Cslib.BitString.noiseOp_eq_sum`, `Cslib.BitString.fourierCoeff_noiseOp`: the Fourier expansion
  of `T_ρ f` [O'Donnell, Proposition 2.47][ODonnell2014].
* `Cslib.BitString.noiseOp_noiseOp`: the noise operators form a semigroup.
* `Cslib.BitString.noiseStability_eq_sum`: the Fourier formula for the noise stability
  [O'Donnell, Theorem 2.49][ODonnell2014].
* `Cslib.BitString.sq_expect_le_noiseStability`, `Cslib.BitString.noiseStability_le_expect_sq`,
  `Cslib.BitString.noiseStability_mono`: the noise stability lies between the squared mean and the
  second moment, increasingly in `ρ`.
* `Cslib.BitString.noiseSensitivity_eq_noiseStability`, `Cslib.BitString.noiseSensitivity_eq_sum`:
  the noise sensitivity through the noise stability and its Fourier formula
  [O'Donnell, Definition 2.43 and Theorem 2.49][ODonnell2014].
* `Cslib.BitString.noiseSensitivity_le_mul_totalInfluence`: the noise sensitivity at `δ` is at
  most `δ` times the total influence.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

open Finset BooleanAnalysis
open scoped BigOperators

variable {n : ℕ}

/-- The character of `S` averages to `(1 - 2 p) ^ |S|` over a random mask of rate `p`: each of its
coordinates is selected, negating the sign, with probability `p`. -/
theorem bernoulliAverage_chi (p : ℝ) (S : Finset (Fin n)) :
    bernoulliAverage p (chi S) = (1 - 2 * p) ^ #S := by
  have h : chi S = fun P => ∏ i, if i ∈ S then signVal (P i) else 1 :=
    funext (chi_eq_prod_univ S)
  rw [h, bernoulliAverage_prod p fun i b => if i ∈ S then signVal b else 1, ← prod_const,
    ← Fintype.prod_ite_mem S]
  refine prod_congr rfl fun i _ => ?_
  split_ifs
  · simp only [signVal_false, signVal_true]
    ring
  · ring

/-! ### The noise operator -/

/-- The **noise operator** `T_ρ`: the average of `f` at a string `ρ`-correlated with `x`, which
flips each bit of `x` independently with probability `(1 - ρ) / 2`. It is an average over a
probability distribution when `-1 ≤ ρ ≤ 1`. -/
noncomputable def noiseOp (ρ : ℝ) (f : BitString n → ℝ) (x : BitString n) : ℝ :=
  bernoulliAverage ((1 - ρ) / 2) fun P => f fun i => x i ^^ P i

/-- **The Fourier expansion of `T_ρ f`**: the noise operator damps the coefficient of `S` by
`ρ ^ |S|` [O'Donnell, Proposition 2.47][ODonnell2014]. -/
theorem noiseOp_eq_sum (ρ : ℝ) (f : BitString n → ℝ) (x : BitString n) :
    noiseOp ρ f x = ∑ S, ρ ^ #S * fourierCoeff f S * chi S x := by
  have hf (P : BitString n) :
      f (fun i => x i ^^ P i) = ∑ S, fourierCoeff f S * chi S x * chi S P := by
    rw [← sum_fourierCoeff_mul_chi f (fun i => x i ^^ P i)]
    simp only [chi_xor, mul_assoc]
  simp only [noiseOp, hf, bernoulliAverage, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun S _ => ?_
  have hS := bernoulliAverage_chi ((1 - ρ) / 2) S
  rw [show 1 - 2 * ((1 - ρ) / 2) = ρ by ring, bernoulliAverage] at hS
  rw [← hS, sum_mul, sum_mul]
  exact sum_congr rfl fun P _ => by ring

/-- **The noise operator damps the Fourier coefficient of `S` by `ρ ^ |S|`**
[O'Donnell, Proposition 2.47][ODonnell2014]. -/
theorem fourierCoeff_noiseOp (ρ : ℝ) (f : BitString n → ℝ) (S : Finset (Fin n)) :
    fourierCoeff (noiseOp ρ f) S = ρ ^ #S * fourierCoeff f S := by
  have h : noiseOp ρ f = fun x => ∑ T, ρ ^ #T * fourierCoeff f T * chi T x :=
    funext (noiseOp_eq_sum ρ f)
  rw [h, fourierCoeff_sum_mul_chi]

/-- The characters are eigenfunctions of the noise operator. -/
theorem noiseOp_chi (ρ : ℝ) (S : Finset (Fin n)) (x : BitString n) :
    noiseOp ρ (chi S) x = ρ ^ #S * chi S x := by
  simp only [noiseOp, chi_xor, bernoulliAverage_const_mul, bernoulliAverage_chi]
  rw [show 1 - 2 * ((1 - ρ) / 2) = ρ by ring, mul_comm]

/-- At `ρ = 1` no bit is flipped, so the noise operator is the identity. -/
@[simp] theorem noiseOp_one (f : BitString n → ℝ) : noiseOp 1 f = f := by
  funext x
  simp [noiseOp, bernoulliAverage_zero]

/-- At `ρ = 0` the noised string is uniform, so the noise operator returns the mean. -/
theorem noiseOp_zero (f : BitString n → ℝ) (x : BitString n) : noiseOp 0 f x = 𝔼 y, f y := by
  rw [noiseOp_eq_sum, sum_eq_single ∅ (fun S _ hS => by simp [hS]) (by simp)]
  simp

/-- The noise operator fixes the constants. -/
@[simp] theorem noiseOp_const (ρ c : ℝ) (x : BitString n) : noiseOp ρ (fun _ => c) x = c :=
  bernoulliAverage_const _ c

/-- The noise operator is additive. -/
theorem noiseOp_add (ρ : ℝ) (f g : BitString n → ℝ) (x : BitString n) :
    noiseOp ρ (fun y => f y + g y) x = noiseOp ρ f x + noiseOp ρ g x :=
  bernoulliAverage_add _ _ _

/-- The noise operator commutes with subtraction. -/
theorem noiseOp_sub (ρ : ℝ) (f g : BitString n → ℝ) (x : BitString n) :
    noiseOp ρ (fun y => f y - g y) x = noiseOp ρ f x - noiseOp ρ g x :=
  bernoulliAverage_sub _ _ _

/-- The noise operator commutes with scaling. -/
theorem noiseOp_const_mul (ρ c : ℝ) (f : BitString n → ℝ) (x : BitString n) :
    noiseOp ρ (fun y => c * f y) x = c * noiseOp ρ f x :=
  bernoulliAverage_const_mul _ _ _

/-- **The noise operators form a semigroup**: `T_ρ T_σ = T_{ρ σ}`. -/
theorem noiseOp_noiseOp (ρ σ : ℝ) (f : BitString n → ℝ) :
    noiseOp ρ (noiseOp σ f) = noiseOp (ρ * σ) f :=
  fourierCoeff_injective <| funext fun S => by
    simp only [fourierCoeff_noiseOp, mul_pow, mul_assoc]

/-- The correlation of `f` with `T_ρ g` is the sum of the products of the Fourier coefficients
damped by `ρ ^ |S|`; in particular `T_ρ` is self-adjoint. -/
theorem expect_mul_noiseOp_eq_sum (ρ : ℝ) (f g : BitString n → ℝ) :
    𝔼 x, f x * noiseOp ρ g x = ∑ S, ρ ^ #S * (fourierCoeff f S * fourierCoeff g S) := by
  rw [expect_mul_eq_sum_fourierCoeff_mul]
  exact sum_congr rfl fun S _ => by rw [fourierCoeff_noiseOp, mul_left_comm]

/-! ### Noise stability -/

/-- The **noise stability** `Stab_ρ[f]` of `f` at `ρ`: the correlation `𝔼 f x f y` of `f` at a
uniform string `x` and a string `y` that is `ρ`-correlated with `x`. -/
noncomputable def noiseStability (ρ : ℝ) (f : BitString n → ℝ) : ℝ :=
  𝔼 x, f x * noiseOp ρ f x

/-- **The Fourier formula for the noise stability**: `Stab_ρ[f] = ∑_S ρ ^ |S| f̂(S) ^ 2`
[O'Donnell, Theorem 2.49][ODonnell2014]. -/
theorem noiseStability_eq_sum (ρ : ℝ) (f : BitString n → ℝ) :
    noiseStability ρ f = ∑ S, ρ ^ #S * fourierCoeff f S ^ 2 := by
  simp only [noiseStability, expect_mul_noiseOp_eq_sum, sq]

/-- At `ρ = 1` the noise stability is the second moment. -/
theorem noiseStability_one (f : BitString n → ℝ) : noiseStability 1 f = 𝔼 x, f x ^ 2 := by
  simp only [noiseStability, noiseOp_one, sq]

/-- At `ρ = 0` the noise stability is the squared mean. -/
theorem noiseStability_zero (f : BitString n → ℝ) : noiseStability 0 f = (𝔼 x, f x) ^ 2 := by
  simp only [noiseStability, noiseOp_zero, ← expect_mul, sq]

/-- On `0 ≤ ρ`, the noise stability increases with `ρ`. -/
theorem noiseStability_mono {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hρσ : ρ ≤ σ) (f : BitString n → ℝ) :
    noiseStability ρ f ≤ noiseStability σ f := by
  simp only [noiseStability_eq_sum]
  exact sum_le_sum fun S _ =>
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hρ hρσ _) (sq_nonneg _)

/-- On `0 ≤ ρ`, the noise stability is at least the squared mean. -/
theorem sq_expect_le_noiseStability {ρ : ℝ} (hρ : 0 ≤ ρ) (f : BitString n → ℝ) :
    (𝔼 x, f x) ^ 2 ≤ noiseStability ρ f :=
  noiseStability_zero f ▸ noiseStability_mono le_rfl hρ f

/-- On `0 ≤ ρ`, the noise stability is nonnegative. -/
theorem noiseStability_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (f : BitString n → ℝ) :
    0 ≤ noiseStability ρ f :=
  (sq_nonneg _).trans (sq_expect_le_noiseStability hρ f)

/-- On `|ρ| ≤ 1`, the noise stability is at most the second moment. -/
theorem noiseStability_le_expect_sq {ρ : ℝ} (hρ : |ρ| ≤ 1) (f : BitString n → ℝ) :
    noiseStability ρ f ≤ 𝔼 x, f x ^ 2 := by
  rw [noiseStability_eq_sum, expect_sq_eq_sum_fourierCoeff_sq]
  refine sum_le_sum fun S _ => ?_
  have h : ρ ^ #S ≤ 1 :=
    (le_abs_self _).trans (abs_pow ρ #S ▸ pow_le_one₀ (abs_nonneg ρ) hρ)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h (sq_nonneg (fourierCoeff f S))

/-! ### Noise sensitivity -/

/-- The **noise sensitivity** `NS_δ[f]` of a Boolean function `f` at `δ`: the probability that
`f x ≠ f y` for a uniform string `x` and the string `y` that flips each bit of `x` independently
with probability `δ`. -/
noncomputable def noiseSensitivity (δ : ℝ) (f : BooleanFunction n) : ℝ :=
  𝔼 x, bernoulliAverage δ fun P => if f x ≠ f (fun i => x i ^^ P i) then 1 else 0

/-- **The noise sensitivity through the noise stability**:
`NS_δ[f] = 1 / 2 - 1 / 2 Stab_{1 - 2 δ}[F]`, for `F` the function `f` with values `±1`. -/
theorem noiseSensitivity_eq_noiseStability (δ : ℝ) (f : BooleanFunction n) :
    noiseSensitivity δ f = 1 / 2 - 1 / 2 * noiseStability (1 - 2 * δ) fun x => signVal (f x) := by
  have h (a b : Bool) :
      (if a ≠ b then (1 : ℝ) else 0) = 1 / 2 - 1 / 2 * (signVal a * signVal b) := by
    cases a <;> cases b <;> norm_num
  simp only [noiseSensitivity, noiseStability, noiseOp, show (1 - (1 - 2 * δ)) / 2 = δ by ring, h,
    bernoulliAverage_sub, bernoulliAverage_const, bernoulliAverage_const_mul, expect_sub_distrib,
    Fintype.expect_const, mul_expect]

/-- **The Fourier formula for the noise sensitivity**:
`NS_δ[f] = ∑_S (1 - (1 - 2 δ) ^ |S|) / 2 F̂(S) ^ 2`, for `F` the function `f` with values `±1`
[O'Donnell, Theorem 2.49][ODonnell2014]. -/
theorem noiseSensitivity_eq_sum (δ : ℝ) (f : BooleanFunction n) :
    noiseSensitivity δ f =
      ∑ S, (1 - (1 - 2 * δ) ^ #S) / 2 * fourierCoeff (fun x => signVal (f x)) S ^ 2 := by
  have h (S : Finset (Fin n)) (c : ℝ) : (1 - (1 - 2 * δ) ^ #S) / 2 * c ^ 2 =
      1 / 2 * c ^ 2 - 1 / 2 * ((1 - 2 * δ) ^ #S * c ^ 2) := by
    ring
  simp only [noiseSensitivity_eq_noiseStability, noiseStability_eq_sum, h, sum_sub_distrib,
    ← mul_sum, sum_fourierCoeff_sq_signVal, mul_one]

/-- With no noise, `f` never changes. -/
@[simp] theorem noiseSensitivity_zero (f : BooleanFunction n) : noiseSensitivity 0 f = 0 := by
  simp [noiseSensitivity, bernoulliAverage_zero]

/-- On `0 ≤ δ ≤ 1`, the noise sensitivity is a probability. -/
theorem noiseSensitivity_mem_Icc {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) (f : BooleanFunction n) :
    noiseSensitivity δ f ∈ Set.Icc 0 1 := by
  have h (b : Prop) [Decidable b] :
      (0 : ℝ) ≤ (if b then 1 else 0) ∧ (if b then 1 else 0 : ℝ) ≤ 1 := by
    split_ifs <;> norm_num
  refine ⟨expect_nonneg fun x _ => ?_, expect_le univ_nonempty fun x _ => ?_⟩
  · simpa only [bernoulliAverage_const] using
      bernoulliAverage_mono hδ hδ' (f := fun _ => 0) fun _ => (h _).1
  · simpa only [bernoulliAverage_const] using
      bernoulliAverage_mono hδ hδ' (g := fun _ => 1) fun _ => (h _).2

/-- On `δ ≤ 1 / 2`, the noise sensitivity increases with `δ`. -/
theorem noiseSensitivity_mono {δ δ' : ℝ} (hδδ' : δ ≤ δ') (hδ' : δ' ≤ 1 / 2)
    (f : BooleanFunction n) : noiseSensitivity δ f ≤ noiseSensitivity δ' f := by
  simp only [noiseSensitivity_eq_noiseStability]
  have := noiseStability_mono (by linarith : 0 ≤ 1 - 2 * δ') (by linarith : 1 - 2 * δ' ≤ 1 - 2 * δ)
    fun x => signVal (f x)
  linarith

/-- **The noise sensitivity is at most `δ` times the total influence**: `NS_δ[f] ≤ δ I[F]` for
`δ ≤ 1`, for `F` the function `f` with values `±1` [O'Donnell, Exercise 2.42][ODonnell2014]. -/
theorem noiseSensitivity_le_mul_totalInfluence {δ : ℝ} (hδ : δ ≤ 1) (f : BooleanFunction n) :
    noiseSensitivity δ f ≤ δ * totalInfluence (fun x => signVal (f x)) := by
  rw [noiseSensitivity_eq_sum, totalInfluence_eq_sum_card_mul_fourierCoeff_sq, mul_sum]
  refine sum_le_sum fun S _ => ?_
  have h := one_add_mul_sub_le_pow (show -1 ≤ 1 - 2 * δ by linarith) #S
  nlinarith [sq_nonneg (fourierCoeff (fun x => signVal (f x)) S)]

end Cslib.BitString
