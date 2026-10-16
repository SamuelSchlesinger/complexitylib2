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

The *Hadamard code* (or Walsh–Hadamard code) encodes a bit string `x : ι → Bool` as the truth
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

The *long code* of a label `a : ι` is the dictator `r ↦ r a`, the evaluation `Function.eval a` on
`ι → Bool` (`BitString.longCode`). It is the Hadamard encoding of the unit vector of `a`
(`BitString.longCode_eq_hadamardCode`), so a table within relative distance `1/4` of a long code
determines its label (`BitString.eq_of_hammingDist_longCode_lt`).

The distance of the code comes from the fact that distinct parities differ on half of the inputs
(`BitString.two_mul_hammingDist_parityOn`).

## Main definitions

* `Cslib.BitString.selfCorrect`: the two-query self-corrected read of a Boolean function.
* `Cslib.BitString.hadamardCode`: the Hadamard encoding of a bit string.
* `Cslib.BitString.longCode`: the long code of a label.

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
* `Cslib.BitString.longCode_eq_hadamardCode`, `Cslib.BitString.eq_of_hammingDist_longCode_lt`: the
  long code is a Hadamard code, and unique decoding of the long code.

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

variable {ι : Type*}

/-! ### Self-correction -/

/-- The self-corrected read of `f` at `x` with randomness `y`: the exclusive or of `f y` and
`f (x + y)`. For uniformly random `y`, both points read are uniformly random, and on a parity the
read is exact (`selfCorrect_parityOn`). -/
def selfCorrect (f : (ι → Bool) → Bool) (x y : ι → Bool) : Bool :=
  f y ^^ f (x + y)

/-- Self-correction reads a parity exactly. -/
@[simp] theorem selfCorrect_parityOn (S : Finset ι) (x y : ι → Bool) :
    selfCorrect (parityOn S) x y = parityOn S x := by
  rw [selfCorrect, parityOn_add, Bool.xor_left_comm, Bool.xor_self, Bool.xor_false]

/-! ### The long code -/

/-- The **long code** of a label `a : ι`: the dictator `r ↦ r a` on `ι → Bool`, that is, the
evaluation `Function.eval a` [Arora and Barak, Chapter 22][AroraBarak09]. It is the Hadamard
encoding of the unit vector of `a` (`longCode_eq_hadamardCode`). -/
def longCode (a : ι) : (ι → Bool) → Bool :=
  Function.eval a

@[simp]
theorem longCode_apply (a : ι) (r : ι → Bool) : longCode a r = r a :=
  rfl

variable [Fintype ι]

section DecidableEq

variable [DecidableEq ι]

/-- **Local correctability of parities**, counting version: the self-corrected read of `f` at `x`
differs from the parity on `S` at `x` for at most twice as many `y` as there are inputs on which
`f` differs from that parity. -/
theorem card_filter_selfCorrect_ne_le (f : (ι → Bool) → Bool) (S : Finset ι)
    (x : ι → Bool) :
    #{y | selfCorrect f x y ≠ parityOn S x} ≤ 2 * hammingDist f (parityOn S) := by
  have htrans : #{y : ι → Bool | f (x + y) ≠ parityOn S (x + y)} =
      hammingDist f (parityOn S) :=
    card_equiv (Equiv.addLeft x) fun y => by
      simp only [mem_filter, mem_univ, true_and]
      exact Iff.rfl
  calc #{y | selfCorrect f x y ≠ parityOn S x}
      ≤ #(({y | f y ≠ parityOn S y} : Finset (ι → Bool)) ∪
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
theorem one_sub_two_mul_le_expect_selfCorrect {f : (ι → Bool) → Bool} {S : Finset ι}
    {ε : ℝ} (h : (hammingDist f (parityOn S) : ℝ) / 2 ^ Fintype.card ι ≤ ε) (x : ι → Bool) :
    1 - 2 * ε ≤ 𝔼 y, if selfCorrect f x y = parityOn S x then 1 else 0 := by
  have hpos : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hne : (#{y | selfCorrect f x y ≠ parityOn S x} : ℝ) ≤ 2 * hammingDist f (parityOn S) := by
    exact_mod_cast card_filter_selfCorrect_ne_le f S x
  have htotal : (#{y | selfCorrect f x y = parityOn S x} : ℝ) +
      #{y | selfCorrect f x y ≠ parityOn S x} = 2 ^ Fintype.card ι := by
    exact_mod_cast (card_filter_add_card_filter_not (s := univ)
      fun y : ι → Bool => selfCorrect f x y = parityOn S x).trans (by simp)
  rw [div_le_iff₀ hpos] at h
  rw [Fintype.expect_boole, nnratCast_dens, Fintype.card_fun, Fintype.card_bool, Nat.cast_pow,
    Nat.cast_ofNat, le_div_iff₀ hpos]
  linarith

end DecidableEq

/-! ### The Hadamard code -/

/-- The Hadamard encoding of `x`: the Boolean function sending `a` to the dot product `x ⬝ᵥ a` in
the Boolean ring `Bool`, the inner product of `x` and `a` modulo two
[Arora and Barak, Section 11.5][AroraBarak09]. -/
def hadamardCode (x : ι → Bool) : (ι → Bool) → Bool :=
  fun a => x ⬝ᵥ a

theorem hadamardCode_apply (x a : ι → Bool) : hadamardCode x a = x ⬝ᵥ a :=
  rfl

/-- A Hadamard codeword is the parity of the bits at the positions where the message is
`true`. -/
theorem hadamardCode_eq_parityOn (x : ι → Bool) :
    hadamardCode x = parityOn {i | x i = true} := by
  funext a
  rw [parityOn_eq_sum, sum_filter, hadamardCode_apply, dotProduct]
  exact sum_congr rfl fun i _ => by cases x i <;> rfl

/-- The inner product is symmetric. -/
theorem hadamardCode_comm (x a : ι → Bool) : hadamardCode x a = hadamardCode a x :=
  dotProduct_comm x a

/-- Hadamard codewords are linear. -/
theorem hadamardCode_add (x a b : ι → Bool) :
    hadamardCode x (a + b) = (hadamardCode x a ^^ hadamardCode x b) :=
  dotProduct_add x a b

/-- The Hadamard code is linear. -/
theorem hadamardCode_add_left (x y a : ι → Bool) :
    hadamardCode (x + y) a = (hadamardCode x a ^^ hadamardCode y a) :=
  add_dotProduct x y a

/-- Self-correction reads a Hadamard codeword exactly. -/
@[simp] theorem selfCorrect_hadamardCode (x a y : ι → Bool) :
    selfCorrect (hadamardCode x) a y = hadamardCode x a := by
  rw [hadamardCode_eq_parityOn, selfCorrect_parityOn]

/-- The parity on `S` is the Hadamard encoding of the indicator of `S`. -/
theorem hadamardCode_decide_mem [DecidableEq ι] (S : Finset ι) :
    hadamardCode (fun i => decide (i ∈ S)) = parityOn S := by
  simp [hadamardCode_eq_parityOn]

/-- The value of a Hadamard codeword at the `i`-th unit vector is the `i`-th bit of the
message. -/
@[simp] theorem hadamardCode_single [DecidableEq ι] (x : ι → Bool) (i : ι) :
    hadamardCode x (Pi.single i true) = x i :=
  dotProduct_single_one x i

/-- **The Hadamard codewords are the linear Boolean functions.** -/
theorem exists_eq_hadamardCode_iff {f : (ι → Bool) → Bool} :
    (∃ x, f = hadamardCode x) ↔ ∀ x y, f (x + y) = (f x ^^ f y) := by
  classical
  rw [← exists_eq_parityOn_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, hadamardCode_eq_parityOn x⟩
  · rintro ⟨S, rfl⟩
    exact ⟨_, (hadamardCode_decide_mem S).symm⟩

/-- The Hadamard code is injective. -/
theorem hadamardCode_injective : Function.Injective (hadamardCode (ι := ι)) := fun x y h => by
  classical
  exact funext fun i => by rw [← hadamardCode_single x, h, hadamardCode_single]

variable [DecidableEq ι]

/-- **The Hadamard code has relative distance one half**: the encodings of distinct bit strings
differ on exactly half of the inputs. -/
theorem two_mul_hammingDist_hadamardCode {x y : ι → Bool} (h : x ≠ y) :
    2 * hammingDist (hadamardCode x) (hadamardCode y) = 2 ^ Fintype.card ι := by
  rw [hadamardCode_eq_parityOn, hadamardCode_eq_parityOn]
  exact two_mul_hammingDist_parityOn fun hS => h <| hadamardCode_injective <| by
    rw [hadamardCode_eq_parityOn, hadamardCode_eq_parityOn, hS]

/-- **Unique decoding**: a Boolean function within relative distance `δ < 1/4` of the encodings
of `x` and of `y` forces `x = y`. -/
theorem eq_of_hammingDist_hadamardCode_le {f : (ι → Bool) → Bool} {x y : ι → Bool} {δ : ℝ}
    (hδ : δ < 1 / 4) (hx : (hammingDist f (hadamardCode x) : ℝ) / 2 ^ Fintype.card ι ≤ δ)
    (hy : (hammingDist f (hadamardCode y) : ℝ) / 2 ^ Fintype.card ι ≤ δ) : x = y := by
  by_contra hxy
  have hpos : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hdist : (2 * hammingDist (hadamardCode x) (hadamardCode y) : ℝ) = 2 ^ Fintype.card ι := by
    exact_mod_cast two_mul_hammingDist_hadamardCode hxy
  have htri : (hammingDist (hadamardCode x) (hadamardCode y) : ℝ) ≤
      hammingDist f (hadamardCode x) + hammingDist f (hadamardCode y) := by
    exact_mod_cast hammingDist_triangle_left _ _ f
  rw [div_le_iff₀ hpos] at hx hy
  nlinarith

/-- **Local correction for the Hadamard code**: if `f` is within relative distance `ε` of the
encoding of `x`, then for every `a`, self-correction at `a` returns the codeword's value at `a`
with probability at least `1 - 2ε`. -/
theorem one_sub_two_mul_le_expect_selfCorrect_hadamardCode {f : (ι → Bool) → Bool}
    {x : ι → Bool} {ε : ℝ} (h : (hammingDist f (hadamardCode x) : ℝ) / 2 ^ Fintype.card ι ≤ ε)
    (a : ι → Bool) :
    1 - 2 * ε ≤ 𝔼 y, if selfCorrect f a y = hadamardCode x a then 1 else 0 := by
  rw [hadamardCode_eq_parityOn] at h ⊢
  exact one_sub_two_mul_le_expect_selfCorrect h a

/-- **Local decoding of the Hadamard code with two queries**: if `f` is within relative distance
`ε` of the encoding of `x`, then self-correction at the `i`-th unit vector returns `x i` with
probability at least `1 - 2ε` [Arora and Barak, Section 11.5][AroraBarak09]. -/
theorem one_sub_two_mul_le_expect_selfCorrect_eq_apply {f : (ι → Bool) → Bool}
    {x : ι → Bool} {ε : ℝ} (h : (hammingDist f (hadamardCode x) : ℝ) / 2 ^ Fintype.card ι ≤ ε)
    (i : ι) :
    1 - 2 * ε ≤ 𝔼 y, if selfCorrect f (Pi.single i true) y = x i then 1 else 0 := by
  simpa only [hadamardCode_single] using
    one_sub_two_mul_le_expect_selfCorrect_hadamardCode h (Pi.single i true)

/-! ### Decoding a function that passes the linearity test -/

/-- Hadamard codewords pass the BLR test with probability one. -/
@[simp] theorem blrAcceptance_hadamardCode (x : ι → Bool) :
    blrAcceptance (hadamardCode x) = 1 := by
  rw [hadamardCode_eq_parityOn, blrAcceptance_parityOn]

/-- **Decoding from the BLR test**: if the test accepts `f` with probability at least `1 - ε`,
then `f` is within relative distance `ε` of the Hadamard encoding of some bit string. -/
theorem exists_hammingDist_hadamardCode_le_of_le_blrAcceptance {f : (ι → Bool) → Bool} {ε : ℝ}
    (h : 1 - ε ≤ blrAcceptance f) :
    ∃ x, (hammingDist f (hadamardCode x) : ℝ) / 2 ^ Fintype.card ι ≤ ε := by
  obtain ⟨S, hS⟩ := exists_hammingDist_parityOn_le_of_le_blrAcceptance h
  exact ⟨fun i => decide (i ∈ S), by rwa [hadamardCode_decide_mem]⟩

/-- **Unique decoding from the BLR test**: if the test accepts `f` with probability at least
`1 - ε` and `ε < 1/4`, then exactly one bit string has its Hadamard encoding within relative
distance `ε` of `f`. -/
theorem existsUnique_hammingDist_hadamardCode_le_of_le_blrAcceptance {f : (ι → Bool) → Bool}
    {ε : ℝ} (hε : ε < 1 / 4) (h : 1 - ε ≤ blrAcceptance f) :
    ∃! x, (hammingDist f (hadamardCode x) : ℝ) / 2 ^ Fintype.card ι ≤ ε :=
  let ⟨x, hx⟩ := exists_hammingDist_hadamardCode_le_of_le_blrAcceptance h
  ⟨x, hx, fun _ hy => eq_of_hammingDist_hadamardCode_le hε hy hx⟩

/-! ### Decoding the long code -/

/-- The long code of `a` is the Hadamard encoding of the unit vector of `a`. -/
theorem longCode_eq_hadamardCode (a : ι) : longCode a = hadamardCode (Pi.single a true) := by
  funext r
  rw [hadamardCode_comm, hadamardCode_single, longCode_apply]

/-- **Unique decoding of the long code**: a Boolean function within relative distance less than
`1/4` of the long codes of `a` and of `b` forces `a = b`. -/
theorem eq_of_hammingDist_longCode_lt {f : (ι → Bool) → Bool} {a b : ι}
    (ha : (hammingDist f (longCode a) : ℝ) / 2 ^ Fintype.card ι < 1 / 4)
    (hb : (hammingDist f (longCode b) : ℝ) / 2 ^ Fintype.card ι < 1 / 4) : a = b := by
  rw [longCode_eq_hadamardCode] at ha hb
  have h := congrFun (eq_of_hammingDist_hadamardCode_le (max_lt ha hb) (le_max_left _ _)
    (le_max_right _ _)) a
  simpa [Pi.single_apply, Bool.zero_eq_false] using h.symm

end Cslib.BitString
