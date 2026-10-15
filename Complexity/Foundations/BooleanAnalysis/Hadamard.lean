/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Linearity
public import Mathlib.Data.Matrix.Mul
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Tactic.Linarith

/-!
# The Hadamard code

The *Hadamard code* (or Walsh–Hadamard code) encodes a bit string `x` of length `n` as the truth
table of the function `a ↦ x ⬝ᵥ a`, the dot product in the Boolean ring `Bool`, that is, the inner
product modulo two (`BitString.hadamardCode`). Bit strings add coordinatewise through the same
ring structure, and the code is bilinear (`BitString.hadamardCode_add`,
`BitString.hadamardCode_add_left`). Its codewords are exactly the parities, hence exactly the
linear Boolean functions
(`BitString.exists_eq_hadamardCode_iff`), and two distinct codewords differ on exactly half of the
inputs (`BitString.two_mul_hammingDist_hadamardCode`).

A function `f` that is close to a parity can be *self-corrected*: to read the parity at `x`, read
`f` at a uniformly random `y` and at `x + y`, both uniformly distributed, and add the two bits
(`BitString.selfCorrect`). If `f` differs from the parity on an `ε` fraction of the inputs, this
returns the parity's value at `x` with probability at least `1 - 2ε`, whatever `x` is
(`BitString.one_sub_two_mul_le_expect_selfCorrect`). For the Hadamard code this is a two-query
*local decoder*: the `i`-th bit of the message is read off at the `i`-th unit vector
(`BitString.one_sub_two_mul_le_expect_selfCorrect_eq_apply`). A word within relative distance
`δ < 1/4` of a codeword determines the codeword (`BitString.eq_of_hammingDist_hadamardCode_le`),
and with the soundness of the Blum–Luby–Rubinfeld test, a function passing that test with
probability `1 - ε` is within `ε` of the encoding of some message, unique when `ε < 1/4`
(`BitString.existsUnique_hammingDist_hadamardCode_le_of_le_blrAcceptance`)
[O'Donnell, Section 1.6][ODonnell2014], [Arora and Barak, Section 11.5][AroraBarak09].

The distance of the code comes from the fact that distinct parities differ on half of the inputs
(`BitString.two_mul_hammingDist_parityOn`).

## Main definitions

* `Cslib.BitString.selfCorrect`: the two-query self-corrected read of a Boolean function.
* `Cslib.BitString.hadamardCode`: the Hadamard encoding of a bit string.

## Main results

* `Cslib.BitString.hadamardCode_eq_parityOn`: a codeword is a parity.
* `Cslib.BitString.card_filter_selfCorrect_ne_le`,
  `Cslib.BitString.one_sub_two_mul_le_expect_selfCorrect`: local correctability of parities.
* `Cslib.BitString.exists_eq_hadamardCode_iff`: the codewords are the linear functions.
* `Cslib.BitString.hadamardCode_injective`, `Cslib.BitString.two_mul_hammingDist_hadamardCode`:
  the Hadamard code is injective with relative distance one half.
* `Cslib.BitString.eq_of_hammingDist_hadamardCode_le`: unique decoding below distance `1/4`.
* `Cslib.BitString.one_sub_two_mul_le_expect_selfCorrect_eq_apply`: local decoding with two
  queries.
* `Cslib.BitString.exists_hammingDist_hadamardCode_le_of_le_blrAcceptance`,
  `Cslib.BitString.existsUnique_hammingDist_hadamardCode_le_of_le_blrAcceptance`: decoding a
  function that passes the linearity test.

## References

* [M. Blum, M. Luby, R. Rubinfeld, *Self-testing/correcting with applications to numerical
  problems*][BlumLubyRubinfeld1993]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {n : ℕ}

/-! ### Self-correction -/

/-- The self-corrected read of `f` at `x` with randomness `y`: the exclusive or of `f y` and
`f (x + y)`. For uniformly random `y`, both points read are uniformly random, and on a parity the
read is exact (`selfCorrect_parityOn`). -/
def selfCorrect (f : BooleanFunction n) (x y : BitString n) : Bool :=
  f y ^^ f (x + y)

/-- Self-correction reads a parity exactly. -/
@[simp] theorem selfCorrect_parityOn (S : Finset (Fin n)) (x y : BitString n) :
    selfCorrect (parityOn S) x y = parityOn S x := by
  rw [selfCorrect, parityOn_add, Bool.xor_left_comm, Bool.xor_self, Bool.xor_false]

/-- **Local correctability of parities**, counting version: the self-corrected read of `f` at `x`
differs from the parity on `S` at `x` for at most twice as many `y` as there are inputs on which
`f` differs from that parity. -/
theorem card_filter_selfCorrect_ne_le (f : BooleanFunction n) (S : Finset (Fin n))
    (x : BitString n) :
    #{y | selfCorrect f x y ≠ parityOn S x} ≤ 2 * hammingDist f (parityOn S) := by
  have htrans : #{y : BitString n | f (x + y) ≠ parityOn S (x + y)} =
      hammingDist f (parityOn S) :=
    card_equiv (Equiv.addLeft x) fun y => by
      simp only [mem_filter, mem_univ, true_and]
      exact Iff.rfl
  calc #{y | selfCorrect f x y ≠ parityOn S x}
      ≤ #(({y | f y ≠ parityOn S y} : Finset (BitString n)) ∪
          ({y | f (x + y) ≠ parityOn S (x + y)} : Finset _)) := by
        refine card_le_card fun y hy => ?_
        simp only [mem_union, mem_filter, mem_univ, true_and] at hy ⊢
        by_contra h
        simp only [not_or, ne_eq, not_not] at h
        exact hy (by rw [selfCorrect, h.1, h.2]; exact selfCorrect_parityOn S x y)
    _ ≤ _ := card_union_le _ _
    _ = 2 * hammingDist f (parityOn S) := by rw [htrans, two_mul]; rfl

/-- **Local correctability of parities**: if `f` differs from the parity on `S` on at most an `ε`
fraction of the inputs, then for every `x`, self-correction at `x` returns the parity's value at
`x` with probability at least `1 - 2ε` over a uniformly random `y`
[O'Donnell, Proposition 1.31][ODonnell2014]. -/
theorem one_sub_two_mul_le_expect_selfCorrect {f : BooleanFunction n} {S : Finset (Fin n)}
    {ε : ℝ} (h : (hammingDist f (parityOn S) : ℝ) / 2 ^ n ≤ ε) (x : BitString n) :
    1 - 2 * ε ≤ 𝔼 y, if selfCorrect f x y = parityOn S x then 1 else 0 := by
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have hne : (#{y | selfCorrect f x y ≠ parityOn S x} : ℝ) ≤ 2 * hammingDist f (parityOn S) := by
    exact_mod_cast card_filter_selfCorrect_ne_le f S x
  have htotal : (#{y | selfCorrect f x y = parityOn S x} : ℝ) +
      #{y | selfCorrect f x y ≠ parityOn S x} = 2 ^ n := by
    exact_mod_cast (card_filter_add_card_filter_not (s := univ)
      fun y : BitString n => selfCorrect f x y = parityOn S x).trans (by simp)
  rw [div_le_iff₀ hpos] at h
  rw [Fintype.expect_boole, nnratCast_dens, BitString.card_eq, Nat.cast_pow, Nat.cast_ofNat,
    le_div_iff₀ hpos]
  linarith

/-! ### The Hadamard code -/

/-- The Hadamard encoding of `x`: the Boolean function sending `a` to the dot product `x ⬝ᵥ a` in
the Boolean ring `Bool`, the inner product of `x` and `a` modulo two
[Arora and Barak, Section 11.5][AroraBarak09]. -/
def hadamardCode (x : BitString n) : BooleanFunction n :=
  fun a => x ⬝ᵥ a

theorem hadamardCode_apply (x a : BitString n) : hadamardCode x a = x ⬝ᵥ a :=
  rfl

/-- A Hadamard codeword is the parity of the bits at the positions where the message is
`true`. -/
theorem hadamardCode_eq_parityOn (x : BitString n) :
    hadamardCode x = parityOn {i | x i = true} := by
  funext a
  rw [parityOn_eq_sum, sum_filter, hadamardCode_apply, dotProduct]
  exact sum_congr rfl fun i _ => by cases x i <;> rfl

/-- The inner product is symmetric. -/
theorem hadamardCode_comm (x a : BitString n) : hadamardCode x a = hadamardCode a x :=
  dotProduct_comm x a

/-- Hadamard codewords are linear. -/
theorem hadamardCode_add (x a b : BitString n) :
    hadamardCode x (a + b) = (hadamardCode x a ^^ hadamardCode x b) :=
  dotProduct_add x a b

/-- The Hadamard code is linear. -/
theorem hadamardCode_add_left (x y a : BitString n) :
    hadamardCode (x + y) a = (hadamardCode x a ^^ hadamardCode y a) :=
  add_dotProduct x y a

/-- Self-correction reads a Hadamard codeword exactly. -/
@[simp] theorem selfCorrect_hadamardCode (x a y : BitString n) :
    selfCorrect (hadamardCode x) a y = hadamardCode x a := by
  rw [hadamardCode_eq_parityOn, selfCorrect_parityOn]

/-- The parity on `S` is the Hadamard encoding of the indicator of `S`. -/
theorem hadamardCode_decide_mem (S : Finset (Fin n)) :
    hadamardCode (fun i => decide (i ∈ S)) = parityOn S := by
  simp [hadamardCode_eq_parityOn]

/-- **The Hadamard codewords are the linear Boolean functions.** -/
theorem exists_eq_hadamardCode_iff {f : BooleanFunction n} :
    (∃ x, f = hadamardCode x) ↔ ∀ x y, f (x + y) = (f x ^^ f y) := by
  rw [← exists_eq_parityOn_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, hadamardCode_eq_parityOn x⟩
  · rintro ⟨S, rfl⟩
    exact ⟨_, (hadamardCode_decide_mem S).symm⟩

/-- The value of a Hadamard codeword at the `i`-th unit vector is the `i`-th bit of the
message. -/
theorem hadamardCode_apply_decide_eq (x : BitString n) (i : Fin n) :
    hadamardCode x (fun j => decide (j = i)) = x i := by
  have h : (fun j => decide (j = i)) = Pi.single i 1 := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [Bool.one_eq_true]
    · simp [hj, Bool.zero_eq_false]
  rw [h, hadamardCode_apply, dotProduct_single_one]

/-- The Hadamard code is injective. -/
theorem hadamardCode_injective : Function.Injective (hadamardCode (n := n)) := fun x y h =>
  funext fun i => by rw [← hadamardCode_apply_decide_eq x, h, hadamardCode_apply_decide_eq]

/-- **The Hadamard code has relative distance one half**: the encodings of distinct bit strings
differ on exactly half of the inputs. -/
theorem two_mul_hammingDist_hadamardCode {x y : BitString n} (h : x ≠ y) :
    2 * hammingDist (hadamardCode x) (hadamardCode y) = 2 ^ n := by
  rw [hadamardCode_eq_parityOn, hadamardCode_eq_parityOn]
  exact two_mul_hammingDist_parityOn fun hS => h <| hadamardCode_injective <| by
    rw [hadamardCode_eq_parityOn, hadamardCode_eq_parityOn, hS]

/-- **Unique decoding**: a Boolean function within relative distance `δ < 1/4` of the encodings
of `x` and of `y` forces `x = y`. -/
theorem eq_of_hammingDist_hadamardCode_le {f : BooleanFunction n} {x y : BitString n} {δ : ℝ}
    (hδ : δ < 1 / 4) (hx : (hammingDist f (hadamardCode x) : ℝ) / 2 ^ n ≤ δ)
    (hy : (hammingDist f (hadamardCode y) : ℝ) / 2 ^ n ≤ δ) : x = y := by
  by_contra hxy
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have hdist : (2 * hammingDist (hadamardCode x) (hadamardCode y) : ℝ) = 2 ^ n := by
    exact_mod_cast two_mul_hammingDist_hadamardCode hxy
  have htri : (hammingDist (hadamardCode x) (hadamardCode y) : ℝ) ≤
      hammingDist f (hadamardCode x) + hammingDist f (hadamardCode y) := by
    exact_mod_cast hammingDist_triangle_left _ _ f
  rw [div_le_iff₀ hpos] at hx hy
  nlinarith

/-- **Local correction for the Hadamard code**: if `f` is within relative distance `ε` of the
encoding of `x`, then for every `a`, self-correction at `a` returns the codeword's value at `a`
with probability at least `1 - 2ε`. -/
theorem one_sub_two_mul_le_expect_selfCorrect_hadamardCode {f : BooleanFunction n}
    {x : BitString n} {ε : ℝ} (h : (hammingDist f (hadamardCode x) : ℝ) / 2 ^ n ≤ ε)
    (a : BitString n) :
    1 - 2 * ε ≤ 𝔼 y, if selfCorrect f a y = hadamardCode x a then 1 else 0 := by
  rw [hadamardCode_eq_parityOn] at h ⊢
  exact one_sub_two_mul_le_expect_selfCorrect h a

/-- **Local decoding of the Hadamard code with two queries**: if `f` is within relative distance
`ε` of the encoding of `x`, then self-correction at the `i`-th unit vector returns `x i` with
probability at least `1 - 2ε` [Arora and Barak, Section 11.5][AroraBarak09]. -/
theorem one_sub_two_mul_le_expect_selfCorrect_eq_apply {f : BooleanFunction n}
    {x : BitString n} {ε : ℝ} (h : (hammingDist f (hadamardCode x) : ℝ) / 2 ^ n ≤ ε)
    (i : Fin n) :
    1 - 2 * ε ≤ 𝔼 y, if selfCorrect f (fun j => decide (j = i)) y = x i then 1 else 0 := by
  simpa only [hadamardCode_apply_decide_eq] using
    one_sub_two_mul_le_expect_selfCorrect_hadamardCode h fun j => decide (j = i)

/-! ### Decoding a function that passes the linearity test -/

/-- Hadamard codewords pass the BLR test with probability one. -/
@[simp] theorem blrAcceptance_hadamardCode (x : BitString n) :
    blrAcceptance (hadamardCode x) = 1 := by
  rw [hadamardCode_eq_parityOn, blrAcceptance_parityOn]

/-- **Decoding from the BLR test**: if the test accepts `f` with probability at least `1 - ε`,
then `f` is within relative distance `ε` of the Hadamard encoding of some bit string. -/
theorem exists_hammingDist_hadamardCode_le_of_le_blrAcceptance {f : BooleanFunction n} {ε : ℝ}
    (h : 1 - ε ≤ blrAcceptance f) :
    ∃ x, (hammingDist f (hadamardCode x) : ℝ) / 2 ^ n ≤ ε := by
  obtain ⟨S, hS⟩ := exists_hammingDist_parityOn_le_of_le_blrAcceptance h
  exact ⟨fun i => decide (i ∈ S), by rwa [hadamardCode_decide_mem]⟩

/-- **Unique decoding from the BLR test**: if the test accepts `f` with probability at least
`1 - ε` and `ε < 1/4`, then exactly one bit string has its Hadamard encoding within relative
distance `ε` of `f`. -/
theorem existsUnique_hammingDist_hadamardCode_le_of_le_blrAcceptance {f : BooleanFunction n}
    {ε : ℝ} (hε : ε < 1 / 4) (h : 1 - ε ≤ blrAcceptance f) :
    ∃! x, (hammingDist f (hadamardCode x) : ℝ) / 2 ^ n ≤ ε :=
  let ⟨x, hx⟩ := exists_hammingDist_hadamardCode_le_of_le_blrAcceptance h
  ⟨x, hx, fun _ hy => eq_of_hammingDist_hadamardCode_le hε hy hx⟩

end Cslib.BitString
