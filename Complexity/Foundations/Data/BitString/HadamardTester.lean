/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Hadamard
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.Linarith

/-!
# Testing quadratic equations with the Hadamard code

A system of quadratic equations over the two-element field in the unknowns `x : BitString n` can
be written as `⟨x ⊗ x, A e⟩ = b e` for `e : Fin m`, where `x ⊗ x` is the tensor product of `x`
with itself (`BitString.tensor`), indexed by pairs of coordinates through `finProdFinEquiv`, and
`⟨·, ·⟩` is the inner product modulo two. A proof that the system has a solution `x` consists of
two tables: the Hadamard encodings `f` of `x` and `g` of `x ⊗ x`. Since
`⟨x ⊗ x, y ⊗ z⟩ = ⟨x, y⟩ ⟨x, z⟩` (`BitString.hadamardCode_tensor_tensor`), the tables can be
checked with a constant number of queries, every value being read by self-correction
[Arora and Barak, Section 11.5][AroraBarak09]:

* the *linearity test* on `f` and on `g` (`BitString.blrAcceptance`): passing it, a table is
  close to the encoding of some bit string;
* the *tensor test* (`BitString.tensorTestAcceptance`), comparing `g` at `y ⊗ z` with the product
  of `f` at `y` and at `z` for uniformly random `y` and `z`: when `g` encodes `w ≠ x ⊗ x`, the
  encodings disagree on at least a quarter of the pairs
  (`BitString.one_div_four_le_expect_hadamardCode_tensor`), so the test rejects with probability
  at least `1/4` less the probability that a read is wrong
  (`BitString.eq_tensor_of_lt_tensorTestAcceptance`);
* the *equation test* (`BitString.equationTestAcceptance`), comparing `g` at the sum of a
  uniformly random set of the `A e` with the sum of the corresponding `b e`: when `g` encodes
  some `w` violating an equation, a random set of equations has a violated sum with probability
  one half (`BitString.hadamardCode_eq_of_lt_equationTestAcceptance`).

Together they make the Hadamard tester: the encodings of a solution pass all four tests with
probability one, and tables passing them with high enough probability certify that the system is
solvable, by a solution that `f` encodes
(`BitString.exists_forall_hadamardCode_tensor_eq_of_le_blrAcceptance`).

## Main definitions

* `Cslib.BitString.tensor`: the tensor product of two bit strings.
* `Cslib.BitString.tensorTestAcceptance`: the acceptance probability of the tensor test.
* `Cslib.BitString.equationTestAcceptance`: the acceptance probability of the equation test.

## Main results

* `Cslib.BitString.hadamardCode_tensor_tensor`: the inner product of tensor products is the
  product of the inner products.
* `Cslib.BitString.one_div_four_le_expect_hadamardCode_tensor`: a nonzero bilinear form is
  nonzero on at least a quarter of the pairs.
* `Cslib.BitString.tensorTestAcceptance_hadamardCode`,
  `Cslib.BitString.eq_tensor_of_lt_tensorTestAcceptance`: completeness and soundness of the
  tensor test.
* `Cslib.BitString.equationTestAcceptance_hadamardCode`,
  `Cslib.BitString.hadamardCode_eq_of_lt_equationTestAcceptance`: completeness and soundness of
  the equation test.
* `Cslib.BitString.exists_forall_hadamardCode_tensor_eq_of_le_blrAcceptance`: soundness of the
  Hadamard tester for quadratic equations.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {m n N : ℕ}

/-! ### Tensor products -/

/-- The tensor product of bit strings `x` and `y`: its bit at the position of `(i, j)` under
`finProdFinEquiv` is `x i && y j`. -/
def tensor (x : BitString m) (y : BitString n) : BitString (m * n) :=
  fun k => x (finProdFinEquiv.symm k).1 && y (finProdFinEquiv.symm k).2

/-- The bit of `x ⊗ y` at the position of `(i, j)` is `x i && y j`. -/
@[simp] theorem tensor_finProdFinEquiv (x : BitString m) (y : BitString n) (i : Fin m)
    (j : Fin n) : tensor x y (finProdFinEquiv (i, j)) = (x i && y j) := by
  simp [tensor]

/-- The tensor product is linear in its first argument. -/
theorem tensor_xor_left (x x' : BitString m) (y : BitString n) :
    tensor (fun i => x i ^^ x' i) y = fun k => tensor x y k ^^ tensor x' y k :=
  funext fun _ => Bool.and_xor_distrib_right _ _ _

/-- The tensor product is linear in its second argument. -/
theorem tensor_xor_right (x : BitString m) (y y' : BitString n) :
    tensor x (fun j => y j ^^ y' j) = fun k => tensor x y k ^^ tensor x y' k :=
  funext fun _ => Bool.and_xor_distrib_left _ _ _

/-- The tensor product of two unit vectors is a unit vector. -/
theorem tensor_decide_eq (i : Fin m) (j : Fin n) :
    tensor (fun i' => decide (i' = i)) (fun j' => decide (j' = j)) =
      fun k => decide (k = finProdFinEquiv (i, j)) := by
  funext k
  obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp

/-- **The inner product of tensor products is the product of the inner products**:
`⟨x ⊗ y, a ⊗ b⟩ = ⟨x, a⟩ ⟨y, b⟩`. -/
theorem hadamardCode_tensor_tensor (x a : BitString m) (y b : BitString n) :
    hadamardCode (tensor x y) (tensor a b) = (hadamardCode x a && hadamardCode y b) := by
  have hcard : #{k | (tensor x y k && tensor a b k) = true} =
      #{i | (x i && a i) = true} * #{j | (y j && b j) = true} := by
    rw [← card_product, ← filter_product]
    refine card_equiv finProdFinEquiv.symm fun k => ?_
    simp only [tensor, mem_filter, mem_univ, mem_product, true_and, Bool.and_eq_true]
    tauto
  simp only [hadamardCode_apply, parity, parityOn]
  rw [hcard]
  generalize #{i | (x i && a i) = true} = p
  generalize #{j | (y j && b j) = true} = q
  rcases Nat.mod_two_eq_zero_or_one p with h₁ | h₁ <;>
    rcases Nat.mod_two_eq_zero_or_one q with h₂ | h₂ <;>
    simp [Nat.mul_mod, h₁, h₂]

/-- **A nonzero bilinear form is nonzero on a quarter of the pairs**: if `M` is not all `false`,
then `⟨M, y ⊗ z⟩ = 1` with probability at least `1/4` over uniformly random `y` and `z`. -/
theorem one_div_four_le_expect_hadamardCode_tensor {M : BitString (m * n)}
    (hM : ∃ k, M k = true) :
    1 / 4 ≤ 𝔼 y, 𝔼 z, if hadamardCode M (tensor y z) = true then (1 : ℝ) else 0 := by
  obtain ⟨k, hk⟩ := hM
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  have hrow (y : BitString m) :
      1 / 2 * (if hadamardCode M (tensor y fun j' => decide (j' = j)) = true then 1 else 0) ≤
        𝔼 z, if hadamardCode M (tensor y z) = true then (1 : ℝ) else 0 := by
    split_ifs with hy
    · rw [mul_one, expect_boole_eq_one_div_two_of_xor (f := fun z => hadamardCode M (tensor y z))
        (fun z z' => by rw [tensor_xor_right, hadamardCode_xor]) ⟨_, hy⟩]
    · rw [mul_zero]
      exact expect_nonneg fun z _ => by split_ifs <;> norm_num
  have hcol : 𝔼 y, (if hadamardCode M (tensor y fun j' => decide (j' = j)) = true then
      (1 : ℝ) else 0) = 1 / 2 :=
    expect_boole_eq_one_div_two_of_xor
      (f := fun y => hadamardCode M (tensor y fun j' => decide (j' = j)))
      (fun y y' => by rw [tensor_xor_left, hadamardCode_xor])
      ⟨fun i' => decide (i' = i), by rwa [tensor_decide_eq, hadamardCode_apply_decide_eq]⟩
  calc (1 / 4 : ℝ) = 𝔼 y, 1 / 2 * (if hadamardCode M (tensor y fun j' => decide (j' = j)) = true
        then (1 : ℝ) else 0) := by
        rw [← mul_expect, hcol]
        norm_num
    _ ≤ _ := expect_le_expect fun y _ => hrow y

/-! ### Union bounds -/

/-- One step of a union bound: if `A` implies `F` whenever `G` holds, the indicator of `A` is at
most the indicator of `F` plus the indicator of the failure of `G`. -/
private theorem boole_le_add_one_sub {A F G : Prop} [Decidable A] [Decidable F] [Decidable G]
    (h : A → G → F) :
    (if A then (1 : ℝ) else 0) ≤ (if F then 1 else 0) + (1 - if G then 1 else 0) := by
  split_ifs <;> first | exact absurd (h ‹A› ‹G›) ‹¬F› | norm_num

/-- The union bound over three events `G₁`, `G₂`, `G₃`. -/
private theorem boole_le_add_one_sub₃ {A F G₁ G₂ G₃ : Prop} [Decidable A] [Decidable F]
    [Decidable G₁] [Decidable G₂] [Decidable G₃] (h : A → G₁ → G₂ → G₃ → F) :
    (if A then (1 : ℝ) else 0) ≤ (if F then 1 else 0) + (1 - if G₁ then 1 else 0) +
      (1 - if G₂ then 1 else 0) + (1 - if G₃ then 1 else 0) := by
  split_ifs <;> first | exact absurd (h ‹A› ‹G₁› ‹G₂› ‹G₃›) ‹¬F› | norm_num

/-- A read that is correct with probability at least `1 - δ` for every input is wrong with
probability at most `δ` on average. -/
private theorem expect_expect_one_sub_le {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    [Nonempty κ] {c : ι → κ → ℝ} {δ : ℝ} (h : ∀ i, 1 - δ ≤ 𝔼 j, c i j) :
    𝔼 i, 𝔼 j, (1 - c i j) ≤ δ :=
  expect_le univ_nonempty fun i _ => by
    rw [expect_sub_distrib, Fintype.expect_const]
    linarith [h i]

/-! ### The tensor test -/

/-- The acceptance probability of the tensor test on tables `f` and `g`: the probability, over
independent uniformly random `y`, `z`, `r`, `s` and `t`, that the self-corrected read of `g` at
`y ⊗ z` with randomness `t` is the product of the self-corrected reads of `f` at `y` with
randomness `r` and at `z` with randomness `s`. -/
noncomputable def tensorTestAcceptance (f : BooleanFunction n) (g : BooleanFunction (n * n)) :
    ℝ :=
  𝔼 y, 𝔼 z, 𝔼 r, 𝔼 s, 𝔼 t,
    if selfCorrect g (tensor y z) t = (selfCorrect f y r && selfCorrect f z s) then 1 else 0

/-- **Completeness of the tensor test**: the encodings of `x` and of `x ⊗ x` pass it with
probability one. -/
@[simp] theorem tensorTestAcceptance_hadamardCode (x : BitString n) :
    tensorTestAcceptance (hadamardCode x) (hadamardCode (tensor x x)) = 1 := by
  simp [tensorTestAcceptance, hadamardCode_tensor_tensor]

/-- **Soundness of the tensor test**: if `f` and `g` are within relative distances `ε` and `ε'`
of the encodings of `x` and of `w`, and the test accepts with probability more than
`3/4 + 4ε + 2ε'`, then `w = x ⊗ x`. -/
theorem eq_tensor_of_lt_tensorTestAcceptance {f : BooleanFunction n}
    {g : BooleanFunction (n * n)} {x : BitString n} {w : BitString (n * n)} {ε ε' : ℝ}
    (hf : (hammingDist f (hadamardCode x) : ℝ) / 2 ^ n ≤ ε)
    (hg : (hammingDist g (hadamardCode w) : ℝ) / 2 ^ (n * n) ≤ ε')
    (h : 3 / 4 + (4 * ε + 2 * ε') < tensorTestAcceptance f g) : w = tensor x x := by
  by_contra hw
  -- The test made on the codewords themselves, and the events that the reads are correct.
  set D : BitString n → BitString n → ℝ := fun y z =>
    if hadamardCode w (tensor y z) = (hadamardCode x y && hadamardCode x z) then 1 else 0
  set c : BitString n → BitString n → ℝ := fun y r =>
    if selfCorrect f y r = hadamardCode x y then 1 else 0
  set c' : BitString n → BitString n → BitString (n * n) → ℝ := fun y z t =>
    if selfCorrect g (tensor y z) t = hadamardCode w (tensor y z) then 1 else 0
  have hD : 𝔼 y, 𝔼 z, D y z ≤ 3 / 4 := by
    have hM : ∃ k, (w k ^^ tensor x x k) = true := by
      by_contra hc
      refine hw (funext fun k => ?_)
      have hk := not_exists.1 hc k
      revert hk
      cases w k <;> cases tensor x x k <;> simp
    have hpt (y z : BitString n) : D y z =
        1 - if hadamardCode (fun k => w k ^^ tensor x x k) (tensor y z) = true then 1 else 0 := by
      simp only [D, hadamardCode_xor_left, hadamardCode_tensor_tensor]
      cases hadamardCode w (tensor y z) <;> cases (hadamardCode x y && hadamardCode x z) <;>
        norm_num
    simp only [hpt, expect_sub_distrib, Fintype.expect_const]
    linarith [one_div_four_le_expect_hadamardCode_tensor hM]
  have hbound : tensorTestAcceptance f g ≤ 𝔼 y, 𝔼 z, 𝔼 r, 𝔼 s, 𝔼 t,
      (D y z + (1 - c y r) + (1 - c z s) + (1 - c' y z t)) := by
    unfold tensorTestAcceptance
    gcongr with y _ z _ r _ s _ t _
    exact boole_le_add_one_sub₃ fun hA h₁ h₂ h₃ => by rw [← h₁, ← h₂, ← h₃]; exact hA
  simp only [expect_add_distrib, Fintype.expect_const] at hbound
  have hc : 𝔼 y, 𝔼 r, (1 - c y r) ≤ 2 * ε :=
    expect_expect_one_sub_le fun y => one_sub_two_mul_le_expect_selfCorrect_hadamardCode hf y
  have hc' : 𝔼 y, 𝔼 z, 𝔼 t, (1 - c' y z t) ≤ 2 * ε' :=
    expect_le univ_nonempty fun y _ => expect_expect_one_sub_le fun z =>
      one_sub_two_mul_le_expect_selfCorrect_hadamardCode hg _
  linarith

/-! ### The equation test -/

/-- The inner product of `w` with the sum of the `A e` for the `e` with `k e = true` is the sum of
the inner products of `w` with those `A e`. -/
private theorem hadamardCode_hadamardCode (w : BitString N) (k : BitString m)
    (A : Fin m → BitString N) :
    hadamardCode w (fun j => hadamardCode k fun e => A e j) =
      hadamardCode k fun e => hadamardCode w (A e) := by
  simp only [hadamardCode]
  induction ({e | k e = true} : Finset (Fin m)) using Finset.induction_on with
  | empty => simp [parityOn]
  | insert e T he ih => simp only [parityOn_insert he, parityOn_xor, ih]

/-- The acceptance probability of the equation test on a table `g`, for the linear equations
`⟨w, A e⟩ = b e` in `w`: the probability, over independent uniformly random `k` and `t`, that the
self-corrected read of `g` at the sum of the `A e` for the `e` with `k e = true`, with randomness
`t`, is the sum of the corresponding `b e`. -/
noncomputable def equationTestAcceptance (g : BooleanFunction N) (A : Fin m → BitString N)
    (b : BitString m) : ℝ :=
  𝔼 k, 𝔼 t,
    if selfCorrect g (fun j => hadamardCode k fun e => A e j) t = hadamardCode k b then 1 else 0

/-- **Completeness of the equation test**: the encoding of a solution of the equations passes it
with probability one. -/
theorem equationTestAcceptance_hadamardCode {A : Fin m → BitString N} {b : BitString m}
    {w : BitString N} (h : ∀ e, hadamardCode w (A e) = b e) :
    equationTestAcceptance (hadamardCode w) A b = 1 := by
  simp [equationTestAcceptance, hadamardCode_hadamardCode, h]

/-- **Soundness of the equation test**: if `g` is within relative distance `ε` of the encoding of
`w`, and the test accepts with probability more than `1/2 + 2ε`, then `w` solves the
equations. -/
theorem hadamardCode_eq_of_lt_equationTestAcceptance {g : BooleanFunction N}
    {A : Fin m → BitString N} {b : BitString m} {w : BitString N} {ε : ℝ}
    (hg : (hammingDist g (hadamardCode w) : ℝ) / 2 ^ N ≤ ε)
    (h : 1 / 2 + 2 * ε < equationTestAcceptance g A b) (e : Fin m) :
    hadamardCode w (A e) = b e := by
  by_contra he
  -- The test made on the codeword itself, and the event that the read is correct.
  set D : BitString m → ℝ := fun k =>
    if hadamardCode w (fun j => hadamardCode k fun e' => A e' j) = hadamardCode k b then 1 else 0
  set c : BitString m → BitString N → ℝ := fun k t =>
    if selfCorrect g (fun j => hadamardCode k fun e' => A e' j) t =
      hadamardCode w (fun j => hadamardCode k fun e' => A e' j) then 1 else 0
  have hD : 𝔼 k, D k = 1 / 2 := by
    -- The parity of the equations violated by `w` in a random set of equations.
    have hv : ∃ k, hadamardCode (fun e' => hadamardCode w (A e') ^^ b e') k = true :=
      ⟨fun e' => decide (e' = e), by simpa [hadamardCode_apply_decide_eq] using he⟩
    have hpt (k : BitString m) : D k =
        1 - if hadamardCode (fun e' => hadamardCode w (A e') ^^ b e') k = true then 1 else 0 := by
      simp only [D]
      rw [hadamardCode_hadamardCode, hadamardCode_comm _ k, hadamardCode_xor]
      cases hadamardCode k (fun e' => hadamardCode w (A e')) <;> cases hadamardCode k b <;> norm_num
    simp only [hpt, expect_sub_distrib, Fintype.expect_const,
      expect_boole_eq_one_div_two_of_xor (hadamardCode_xor _) hv]
    norm_num
  have hbound : equationTestAcceptance g A b ≤ 𝔼 k, 𝔼 t, (D k + (1 - c k t)) := by
    unfold equationTestAcceptance
    gcongr with k _ t _
    exact boole_le_add_one_sub fun hA hG => by rw [← hG]; exact hA
  simp only [expect_add_distrib, Fintype.expect_const] at hbound
  have hc : 𝔼 k, 𝔼 t, (1 - c k t) ≤ 2 * ε :=
    expect_expect_one_sub_le fun k => one_sub_two_mul_le_expect_selfCorrect_hadamardCode hg _
  linarith

/-! ### The Hadamard tester -/

/-- **Soundness of the Hadamard tester for quadratic equations**: if tables `f` and `g` pass the
linearity test with probabilities at least `1 - ε` and `1 - ε'`, the tensor test with probability
more than `3/4 + 4ε + 2ε'`, and the equation test for `A` and `b` with probability more than
`1/2 + 2ε'`, then `f` is within relative distance `ε` of the encoding of a solution `x` of the
quadratic equations `⟨x ⊗ x, A e⟩ = b e`. -/
theorem exists_forall_hadamardCode_tensor_eq_of_le_blrAcceptance {f : BooleanFunction n}
    {g : BooleanFunction (n * n)} {A : Fin m → BitString (n * n)} {b : BitString m} {ε ε' : ℝ}
    (hf : 1 - ε ≤ blrAcceptance f) (hg : 1 - ε' ≤ blrAcceptance g)
    (htensor : 3 / 4 + (4 * ε + 2 * ε') < tensorTestAcceptance f g)
    (hequation : 1 / 2 + 2 * ε' < equationTestAcceptance g A b) :
    ∃ x, (hammingDist f (hadamardCode x) : ℝ) / 2 ^ n ≤ ε ∧
      ∀ e, hadamardCode (tensor x x) (A e) = b e := by
  obtain ⟨x, hx⟩ := exists_hammingDist_hadamardCode_le_of_le_blrAcceptance hf
  obtain ⟨w, hw⟩ := exists_hammingDist_hadamardCode_le_of_le_blrAcceptance hg
  obtain rfl := eq_tensor_of_lt_tensorTestAcceptance hx hw htensor
  exact ⟨x, hx, hadamardCode_eq_of_lt_equationTestAcceptance hw hequation⟩

end Cslib.BitString
