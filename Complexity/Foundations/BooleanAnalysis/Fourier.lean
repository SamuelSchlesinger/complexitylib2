/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Parity
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Fourier analysis on the Boolean cube

Reading a bit `b` as the sign `(-1) ^ b` (`BitString.signVal`), the *character* of a set `S` of
coordinates is `χ_S x = ∏_{i ∈ S} (-1) ^ (x i)` (`BitString.chi`), the sign of the parity of the
bits of `x` in `S`. Bit strings add coordinatewise modulo two, `(x + y) i = (x i ^^ y i)`, through
Mathlib's Boolean ring structure on `Bool`, and the characters turn sums into products
(`BitString.chi_add`). The characters are orthonormal for the uniform expectation
(`BitString.expect_chi_mul_chi`), and every real function on the cube is the sum of its *Fourier
expansion* `f = ∑_S f̂(S) χ_S`, with the *Fourier coefficients* `f̂(S) = 𝔼_x f x χ_S x`
(`BitString.fourierCoeff`, `BitString.sum_fourierCoeff_mul_chi`), which are unique
(`BitString.fourierCoeff_sum_mul_chi`), so the Fourier transform is a linear equivalence
(`BitString.fourierTransform`). The expectation of a product is the sum of products of
coefficients (**Plancherel**, `BitString.expect_mul_eq_sum_fourierCoeff_mul`), so the squared
coefficients of a function with values `±1` sum to one (`BitString.sum_fourierCoeff_sq_signVal`).
For Boolean functions read as signs, correlation is one minus twice the relative Hamming distance
(`BitString.expect_signVal_mul_signVal`), so the coefficient on `S` measures the distance to the
parity on `S` (`BitString.fourierCoeff_signVal`) [O'Donnell, Chapter 1][ODonnell2014].

The coefficients are named `BitString.fourierCoeff`; Mathlib's root `fourierCoeff` is the Fourier
coefficient on the circle, so the name is meant to be used qualified.

## Main definitions

* `Cslib.BitString.signVal`: a bit as a sign, `false ↦ 1` and `true ↦ -1`.
* `Cslib.BitString.chi`: the character of a set of coordinates.
* `Cslib.BitString.fourierCoeff`: the Fourier coefficient of a real function on the cube, and
  `Cslib.BitString.fourierCoeffₗ` the same as a linear map.
* `Cslib.BitString.fourierTransform`: the Fourier transform, as a linear equivalence.

## Main results

* `Cslib.BitString.expect_chi_mul_chi`: the characters are orthonormal.
* `Cslib.BitString.chi_add`: the characters are multiplicative.
* `Cslib.BitString.sum_fourierCoeff_mul_chi`: the Fourier expansion.
* `Cslib.BitString.fourierCoeff_sum_mul_chi`, `Cslib.BitString.fourierCoeff_injective`:
  uniqueness of the Fourier coefficients.
* `Cslib.BitString.expect_mul_eq_sum_fourierCoeff_mul`: Plancherel's identity.
* `Cslib.BitString.sum_fourierCoeff_sq_signVal`: Parseval's identity for functions with values
  `±1`.
* `Cslib.BitString.expect_signVal_mul_signVal`, `Cslib.BitString.fourierCoeff_signVal`: the
  correlation of two Boolean functions is one minus twice their relative Hamming distance.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {n : ℕ}

/-- A bit read as a sign: `false ↦ 1` and `true ↦ -1`. -/
def signVal (b : Bool) : ℝ :=
  if b then -1 else 1

@[simp] theorem signVal_false : signVal false = 1 := rfl

@[simp] theorem signVal_true : signVal true = -1 := rfl

@[simp] theorem signVal_not (b : Bool) : signVal (!b) = -signVal b := by
  cases b <;> simp

/-- A sign squares to one. -/
theorem signVal_mul_self (b : Bool) : signVal b * signVal b = 1 := by
  cases b <;> simp

/-- The product of two signs records whether the bits agree. -/
theorem signVal_mul_signVal (a b : Bool) : signVal a * signVal b = if a = b then 1 else -1 := by
  cases a <;> cases b <;> simp

/-- The sign of an exclusive or is the product of the signs. -/
@[simp] theorem signVal_xor (a b : Bool) : signVal (a ^^ b) = signVal a * signVal b := by
  cases a <;> cases b <;> simp

/-- The character of a set `S` of coordinates: the sign of the parity of the bits in `S`. -/
def chi (S : Finset (Fin n)) (x : BitString n) : ℝ :=
  ∏ i ∈ S, signVal (x i)

@[simp] theorem chi_empty (x : BitString n) : chi ∅ x = 1 :=
  prod_empty

/-- The character of `S` is the sign of the parity of the bits in `S`. -/
theorem chi_eq_signVal_parityOn (S : Finset (Fin n)) (x : BitString n) :
    chi S x = signVal (parityOn S x) := by
  induction S using Finset.induction_on with
  | empty => simp [parityOn]
  | insert i S hi ih =>
    rw [chi, prod_insert hi, ← chi, ih, parityOn_insert hi]
    cases x i <;> simp

/-- The character as a product over all coordinates. -/
theorem chi_eq_prod_univ (S : Finset (Fin n)) (x : BitString n) :
    chi S x = ∏ i, if i ∈ S then signVal (x i) else 1 := by
  rw [prod_ite_mem, univ_inter, chi]

/-- **Characters multiply** by the symmetric difference of their sets. -/
theorem chi_mul_chi (S T : Finset (Fin n)) (x : BitString n) :
    chi S x * chi T x = chi (symmDiff S T) x := by
  simp only [chi_eq_prod_univ, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT, mem_symmDiff, signVal_mul_self]

/-- **Characters are multiplicative**: the character of the sum of two bit strings, their
coordinatewise exclusive or, is the product of their characters. -/
theorem chi_add (S : Finset (Fin n)) (x y : BitString n) : chi S (x + y) = chi S x * chi S y := by
  simp only [chi, Pi.add_apply, Bool.add_eq_xor, signVal_xor, prod_mul_distrib]

section Update

variable {i : Fin n} {S : Finset (Fin n)}

/-- Changing a bit outside `S` leaves the character of `S` unchanged. -/
theorem chi_update_of_notMem (hi : i ∉ S) (x : BitString n) (b : Bool) :
    chi S (Function.update x i b) = chi S x :=
  prod_congr rfl fun _ hj => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]

/-- Setting a bit in `S` to `b` splits off the sign of `b` from the character of `S`. -/
theorem chi_update_of_mem (hi : i ∈ S) (x : BitString n) (b : Bool) :
    chi S (Function.update x i b) = signVal b * chi (S.erase i) x := by
  rw [chi, ← mul_prod_erase S _ hi, Function.update_self, ← chi,
    chi_update_of_notMem (notMem_erase i S)]

end Update

/-- The characters of nonempty sets sum to zero. -/
theorem sum_chi (S : Finset (Fin n)) :
    ∑ x, chi S x = if S = ∅ then 2 ^ n else 0 := by
  simp only [chi_eq_prod_univ]
  rw [← Fintype.prod_sum (fun i (b : Bool) => if i ∈ S then signVal b else 1)]
  simp only [Fintype.sum_bool, signVal_true, signVal_false]
  split_ifs with hS
  · simp [hS, one_add_one_eq_two]
  · obtain ⟨i, hi⟩ := nonempty_iff_ne_empty.2 hS
    exact prod_eq_zero (mem_univ i) (by simp [hi])

/-- **The characters are orthonormal.** -/
theorem expect_chi_mul_chi (S T : Finset (Fin n)) :
    𝔼 x, chi S x * chi T x = if S = T then 1 else 0 := by
  have h : symmDiff S T = ∅ ↔ S = T := by rw [← bot_eq_empty, symmDiff_eq_bot]
  simp only [chi_mul_chi, expect_eq_sum_div_card, sum_chi, h, card_univ, card_eq, Nat.cast_pow,
    Nat.cast_ofNat]
  split_ifs <;> simp

/-- The characters at two points, summed over all sets, detect equality of the points. -/
theorem sum_chi_mul_chi (x y : BitString n) :
    ∑ S, chi S x * chi S y = if x = y then 2 ^ n else 0 := by
  have h := prod_add (fun i => signVal (x i) * signVal (y i)) (fun _ => (1 : ℝ)) univ
  simp only [prod_const_one, mul_one, powerset_univ] at h
  simp only [chi, ← prod_mul_distrib]
  rw [← h]
  simp only [signVal_mul_signVal]
  split_ifs with hxy
  · subst hxy
    simp [one_add_one_eq_two]
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
    exact prod_eq_zero (mem_univ i) (by simp [hi])

/-- The Fourier coefficient of `f` on `S`: the correlation of `f` with the character of `S`. -/
noncomputable def fourierCoeff (f : BitString n → ℝ) (S : Finset (Fin n)) : ℝ :=
  𝔼 x, f x * chi S x

/-- The Fourier coefficient as a normalised sum. -/
theorem fourierCoeff_eq_sum (f : BitString n → ℝ) (S : Finset (Fin n)) :
    fourierCoeff f S = (∑ x, f x * chi S x) / 2 ^ n := by
  simp [fourierCoeff, expect_eq_sum_div_card]

/-- The Fourier coefficients are additive. -/
theorem fourierCoeff_add (f g : BitString n → ℝ) (S : Finset (Fin n)) :
    fourierCoeff (fun x => f x + g x) S = fourierCoeff f S + fourierCoeff g S := by
  simp only [fourierCoeff, add_mul, expect_add_distrib]

/-- The Fourier coefficients commute with subtraction. -/
theorem fourierCoeff_sub (f g : BitString n → ℝ) (S : Finset (Fin n)) :
    fourierCoeff (fun x => f x - g x) S = fourierCoeff f S - fourierCoeff g S := by
  simp only [fourierCoeff, sub_mul, expect_sub_distrib]

/-- The Fourier coefficients commute with scaling. -/
theorem fourierCoeff_const_mul (c : ℝ) (f : BitString n → ℝ) (S : Finset (Fin n)) :
    fourierCoeff (fun x => c * f x) S = c * fourierCoeff f S := by
  simp only [fourierCoeff, mul_assoc, mul_expect]

/-- Multiplying by a character shifts the coefficients by the symmetric difference. -/
theorem fourierCoeff_chi_mul (T : Finset (Fin n)) (f : BitString n → ℝ) (S : Finset (Fin n)) :
    fourierCoeff (fun x => chi T x * f x) S = fourierCoeff f (symmDiff T S) := by
  simp only [fourierCoeff, ← chi_mul_chi, mul_comm (chi T _), mul_assoc]

/-- The characters of nonempty sets have expectation zero. -/
theorem expect_chi (S : Finset (Fin n)) : 𝔼 x, chi S x = if S = ∅ then 1 else 0 := by
  simpa using expect_chi_mul_chi S ∅

/-- A constant has all its weight on the empty set. -/
theorem fourierCoeff_const (c : ℝ) (S : Finset (Fin n)) :
    fourierCoeff (fun _ => c) S = if S = ∅ then c else 0 := by
  simp only [fourierCoeff, ← mul_expect, expect_chi, mul_ite, mul_one, mul_zero]

/-- A parity, read as `±1`, is the character of its set, so all its weight is on that set. -/
theorem fourierCoeff_signVal_parityOn (S U : Finset (Fin n)) :
    fourierCoeff (fun x => signVal (parityOn S x)) U = if U = S then 1 else 0 := by
  have h : (fun x => signVal (parityOn S x)) = fun x => chi S x :=
    funext fun x => (chi_eq_signVal_parityOn S x).symm
  rw [h, fourierCoeff, expect_chi_mul_chi]
  exact if_congr eq_comm rfl rfl

/-- The coefficient on the empty set is the expectation. -/
@[simp] theorem fourierCoeff_empty (f : BitString n → ℝ) : fourierCoeff f ∅ = 𝔼 x, f x := by
  simp [fourierCoeff]

/-- **The Fourier expansion**: every function is the sum of its characters weighted by its
Fourier coefficients. -/
theorem sum_fourierCoeff_mul_chi (f : BitString n → ℝ) (x : BitString n) :
    ∑ S, fourierCoeff f S * chi S x = f x := by
  simp only [fourierCoeff_eq_sum, div_mul_eq_mul_div, sum_mul, ← sum_div]
  rw [sum_comm]
  simp only [mul_assoc, ← mul_sum, sum_chi_mul_chi, mul_ite, mul_zero, sum_ite_eq', mem_univ,
    ite_true]
  field_simp

/-- **The Fourier coefficients are unique**: a combination of characters has its weights as
coefficients. -/
theorem fourierCoeff_sum_mul_chi (c : Finset (Fin n) → ℝ) (T : Finset (Fin n)) :
    fourierCoeff (fun x => ∑ S, c S * chi S x) T = c T := by
  simp only [fourierCoeff, sum_mul, mul_assoc]
  rw [expect_sum_comm]
  simp only [← mul_expect, expect_chi_mul_chi, mul_ite, mul_one, mul_zero, sum_ite_eq',
    mem_univ, ite_true]

/-- A function is determined by its Fourier coefficients. -/
theorem fourierCoeff_injective : Function.Injective (fourierCoeff (n := n)) := fun f g h => by
  funext x
  rw [← sum_fourierCoeff_mul_chi f, ← sum_fourierCoeff_mul_chi g, h]

/-- The Fourier coefficient on `S`, as a linear map. -/
noncomputable def fourierCoeffₗ (S : Finset (Fin n)) : (BitString n → ℝ) →ₗ[ℝ] ℝ where
  toFun f := fourierCoeff f S
  map_add' f g := fourierCoeff_add f g S
  map_smul' c f := fourierCoeff_const_mul c f S

@[simp] theorem fourierCoeffₗ_apply (S : Finset (Fin n)) (f : BitString n → ℝ) :
    fourierCoeffₗ S f = fourierCoeff f S :=
  rfl

/-- The Fourier transform, sending a real function on the cube to its Fourier coefficients, as a
linear equivalence: its inverse is the Fourier expansion. -/
noncomputable def fourierTransform : (BitString n → ℝ) ≃ₗ[ℝ] (Finset (Fin n) → ℝ) where
  toFun := fourierCoeff
  map_add' f g := funext (fourierCoeff_add f g)
  map_smul' c f := funext (fourierCoeff_const_mul c f)
  invFun c x := ∑ S, c S * chi S x
  left_inv f := funext (sum_fourierCoeff_mul_chi f)
  right_inv c := funext (fourierCoeff_sum_mul_chi c)

@[simp] theorem fourierTransform_apply (f : BitString n → ℝ) :
    fourierTransform f = fourierCoeff f :=
  rfl

@[simp] theorem fourierTransform_symm_apply (c : Finset (Fin n) → ℝ) (x : BitString n) :
    fourierTransform.symm c x = ∑ S, c S * chi S x :=
  rfl

/-- **Plancherel's identity**: the expectation of a product is the sum of the products of the
Fourier coefficients. -/
theorem expect_mul_eq_sum_fourierCoeff_mul (f g : BitString n → ℝ) :
    𝔼 x, f x * g x = ∑ S, fourierCoeff f S * fourierCoeff g S := by
  have h (x : BitString n) : f x * g x = ∑ S, fourierCoeff g S * (f x * chi S x) := by
    conv_lhs => rw [← sum_fourierCoeff_mul_chi g x]
    rw [mul_sum]
    exact sum_congr rfl fun S _ => mul_left_comm _ _ _
  simp only [h]
  rw [expect_sum_comm]
  refine sum_congr rfl fun S _ => ?_
  rw [← mul_expect, mul_comm]
  rfl

/-- **Parseval's identity.** -/
theorem expect_sq_eq_sum_fourierCoeff_sq (f : BitString n → ℝ) :
    𝔼 x, f x ^ 2 = ∑ S, fourierCoeff f S ^ 2 := by
  simpa only [sq] using expect_mul_eq_sum_fourierCoeff_mul f f

/-- **Parseval's identity for functions with values `±1`**: the squared Fourier coefficients sum
to one. -/
theorem sum_fourierCoeff_sq_signVal (f : BitString n → Bool) :
    ∑ S, fourierCoeff (fun x => signVal (f x)) S ^ 2 = 1 := by
  rw [← expect_sq_eq_sum_fourierCoeff_sq]
  simp only [sq, signVal_mul_self]
  exact expect_const univ_nonempty 1

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
    card_univ, card_eq, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
  rw [sub_div, div_self (pow_ne_zero n two_ne_zero)]

/-- The Fourier coefficient on `S` of a Boolean function read as signs is one minus twice the
relative Hamming distance from the function to the parity on `S`. -/
theorem fourierCoeff_signVal (f : BooleanFunction n) (S : Finset (Fin n)) :
    fourierCoeff (fun x => signVal (f x)) S = 1 - 2 * hammingDist f (parityOn S) / 2 ^ n := by
  simp only [fourierCoeff, chi_eq_signVal_parityOn]
  exact expect_signVal_mul_signVal f (parityOn S)

end Cslib.BitString
