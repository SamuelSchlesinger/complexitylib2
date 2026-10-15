/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Linearity
import Mathlib.Tactic.Linarith

/-!
# The Hadamard code

The *Hadamard code* (or Walsh–Hadamard code) encodes a bit string `x` of length `n` as the truth
table of the function `a ↦ ⟨x, a⟩`, the inner product modulo two (`BitString.hadamardCode`). Its
codewords are exactly the parities, hence exactly the linear Boolean functions
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

Two facts about parities underlie the distance of the code: distinct parities differ on half of
the inputs (`BitString.two_mul_hammingDist_parityOn`), and a linear function that is not
constantly `false` takes the value `true` on half of the inputs
(`BitString.expect_boole_eq_one_div_two_of_xor`).

## Main definitions

* `Cslib.BitString.selfCorrect`: the two-query self-corrected read of a Boolean function.
* `Cslib.BitString.hadamardCode`: the Hadamard encoding of a bit string.

## Main results

* `Cslib.BitString.card_filter_selfCorrect_ne_le`,
  `Cslib.BitString.one_sub_two_mul_le_expect_selfCorrect`: local correctability of parities.
* `Cslib.BitString.two_mul_hammingDist_parityOn`: distinct parities differ on half the inputs.
* `Cslib.BitString.expect_boole_eq_one_div_two_of_xor`: nonzero linear functions are balanced.
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

/-- The uniform probability of an event on the cube is its density. -/
private theorem expect_boole_eq_card_div (P : BitString n → Prop) [DecidablePred P] :
    𝔼 y, (if P y then (1 : ℝ) else 0) = #{y | P y} / 2 ^ n := by
  simp [expect_eq_sum_div_card, sum_boole]

/-! ### Self-correction -/

/-- The self-corrected read of `f` at `x` with randomness `y`: the sum `f y + f (x + y)`, where
bits add modulo two and bit strings add coordinatewise. For uniformly random `y`, both points
read are uniformly random, and on a parity the read is exact (`selfCorrect_parityOn`). -/
def selfCorrect (f : BooleanFunction n) (x y : BitString n) : Bool :=
  f y ^^ f fun i => x i ^^ y i

/-- Self-correction reads a parity exactly. -/
@[simp] theorem selfCorrect_parityOn (S : Finset (Fin n)) (x y : BitString n) :
    selfCorrect (parityOn S) x y = parityOn S x := by
  rw [selfCorrect, parityOn_xor, Bool.xor_left_comm, Bool.xor_self, Bool.xor_false]

/-- **Local correctability of parities**, counting version: the self-corrected read of `f` at `x`
differs from the parity on `S` at `x` for at most twice as many `y` as there are inputs on which
`f` differs from that parity. -/
theorem card_filter_selfCorrect_ne_le (f : BooleanFunction n) (S : Finset (Fin n))
    (x : BitString n) :
    #{y | selfCorrect f x y ≠ parityOn S x} ≤ 2 * hammingDist f (parityOn S) := by
  have htrans : #{y : BitString n | f (fun i => x i ^^ y i) ≠ parityOn S fun i => x i ^^ y i} =
      hammingDist f (parityOn S) :=
    card_equiv (Function.Involutive.toPerm (fun (y : BitString n) i => x i ^^ y i)
      fun y => funext fun i => Bool.bne_self_left (x i) (y i)) fun y => by
        simp only [mem_filter, mem_univ, true_and]
        exact Iff.rfl
  calc #{y | selfCorrect f x y ≠ parityOn S x}
      ≤ #(({y | f y ≠ parityOn S y} : Finset (BitString n)) ∪
          ({y | f (fun i => x i ^^ y i) ≠ parityOn S fun i => x i ^^ y i} : Finset _)) := by
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
  rw [expect_boole_eq_card_div, le_div_iff₀ hpos]
  linarith

/-! ### Parities -/

/-- **Distinct parities differ on half of the inputs.** -/
theorem two_mul_hammingDist_parityOn {S T : Finset (Fin n)} (h : S ≠ T) :
    2 * hammingDist (parityOn S) (parityOn T) = 2 ^ n := by
  have hcorr := expect_signVal_mul_signVal (parityOn S) (parityOn T)
  simp only [← chi_eq_signVal_parityOn, expect_chi_mul_chi, h, ite_false] at hcorr
  have : (2 * hammingDist (parityOn S) (parityOn T) : ℝ) = 2 ^ n := by
    rw [mul_div_assoc] at hcorr
    field_simp at hcorr
    linarith
  exact_mod_cast this

/-- **Nonzero linear functions are balanced**: a Boolean function that turns the exclusive or of
bit strings into the exclusive or of its values, and is not constantly `false`, takes the value
`true` with probability one half at a uniformly random input. -/
theorem expect_boole_eq_one_div_two_of_xor {f : BooleanFunction n}
    (hf : ∀ x y, f (fun i => x i ^^ y i) = (f x ^^ f y)) (h : ∃ x, f x = true) :
    𝔼 x, (if f x = true then (1 : ℝ) else 0) = 1 / 2 := by
  obtain ⟨S, rfl⟩ := exists_eq_parityOn_iff.2 hf
  have hS : S ≠ ∅ := by
    rintro rfl
    simp at h
  have hb (b : Bool) : (if b = true then (1 : ℝ) else 0) = 1 / 2 - 1 / 2 * signVal b := by
    cases b <;> norm_num
  simp only [hb, ← chi_eq_signVal_parityOn, expect_sub_distrib, ← mul_expect, expect_chi, hS,
    ite_false, Fintype.expect_const]
  norm_num

/-! ### The Hadamard code -/

/-- The Hadamard encoding of `x`: the Boolean function sending `a` to the inner product of `x`
and `a` modulo two, that is, to the parity of the bits of `a` at the positions where `x` is
`true` (`hadamardCode_apply`) [Arora and Barak, Section 11.5][AroraBarak09]. -/
def hadamardCode (x : BitString n) : BooleanFunction n :=
  parityOn {i | x i = true}

/-- The Hadamard code is the inner product modulo two. -/
theorem hadamardCode_apply (x a : BitString n) :
    hadamardCode x a = parity n fun i => x i && a i := by
  simp only [hadamardCode, parity, parityOn, filter_filter, Bool.and_eq_true]

/-- The inner product is symmetric. -/
theorem hadamardCode_comm (x a : BitString n) : hadamardCode x a = hadamardCode a x := by
  simp only [hadamardCode_apply, Bool.and_comm]

/-- Hadamard codewords are linear. -/
theorem hadamardCode_xor (x a b : BitString n) :
    hadamardCode x (fun i => a i ^^ b i) = (hadamardCode x a ^^ hadamardCode x b) :=
  parityOn_xor _ a b

/-- The Hadamard code is linear. -/
theorem hadamardCode_xor_left (x y a : BitString n) :
    hadamardCode (fun i => x i ^^ y i) a = (hadamardCode x a ^^ hadamardCode y a) := by
  rw [hadamardCode_comm _ a, hadamardCode_xor, hadamardCode_comm a, hadamardCode_comm a]

/-- Self-correction reads a Hadamard codeword exactly. -/
@[simp] theorem selfCorrect_hadamardCode (x a y : BitString n) :
    selfCorrect (hadamardCode x) a y = hadamardCode x a :=
  selfCorrect_parityOn _ a y

/-- The parity on `S` is the Hadamard encoding of the indicator of `S`. -/
theorem hadamardCode_decide_mem (S : Finset (Fin n)) :
    hadamardCode (fun i => decide (i ∈ S)) = parityOn S := by
  simp [hadamardCode]

/-- **The Hadamard codewords are the linear Boolean functions.** -/
theorem exists_eq_hadamardCode_iff {f : BooleanFunction n} :
    (∃ x, f = hadamardCode x) ↔ ∀ x y, f (fun i => x i ^^ y i) = (f x ^^ f y) := by
  rw [← exists_eq_parityOn_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨S, rfl⟩
    exact ⟨_, (hadamardCode_decide_mem S).symm⟩

/-- The value of a Hadamard codeword at the `i`-th unit vector is the `i`-th bit of the
message. -/
theorem hadamardCode_apply_decide_eq (x : BitString n) (i : Fin n) :
    hadamardCode x (fun j => decide (j = i)) = x i := by
  rw [hadamardCode_comm, hadamardCode]
  simp only [decide_eq_true_eq, filter_eq', mem_univ, ite_true]
  exact (parityOn_insert (notMem_empty i) x).trans (by simp)

/-- The Hadamard code is injective. -/
theorem hadamardCode_injective : Function.Injective (hadamardCode (n := n)) := fun x y h =>
  funext fun i => by rw [← hadamardCode_apply_decide_eq x, h, hadamardCode_apply_decide_eq]

/-- **The Hadamard code has relative distance one half**: the encodings of distinct bit strings
differ on exactly half of the inputs. -/
theorem two_mul_hammingDist_hadamardCode {x y : BitString n} (h : x ≠ y) :
    2 * hammingDist (hadamardCode x) (hadamardCode y) = 2 ^ n :=
  two_mul_hammingDist_parityOn fun hS => h <| hadamardCode_injective <| by
    rw [hadamardCode, hadamardCode, hS]

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
    1 - 2 * ε ≤ 𝔼 y, if selfCorrect f a y = hadamardCode x a then 1 else 0 :=
  one_sub_two_mul_le_expect_selfCorrect h a

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
    blrAcceptance (hadamardCode x) = 1 :=
  blrAcceptance_parityOn _

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
