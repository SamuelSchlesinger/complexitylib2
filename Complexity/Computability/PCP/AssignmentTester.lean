/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.LocalTest
public import Complexity.Foundations.BooleanAnalysis.HadamardTester
public import Mathlib.Data.Fin.VecNotation
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# The Hadamard assignment tester

An **assignment tester** [Dinur, Definition 3.1][Dinur2007] for a constraint `C` on the labels of
the two ends of an edge checks, with a constant number of queries and a constant rejection rate,
that two tables encode labels satisfying `C`. It is handed the tables and a proof; it accepts the
encodings of satisfying labels together with an honest proof, and rejects every proof with
probability at least a constant times the distance of the tables from the encodings of the closest
satisfying labels. Running it on every edge of a constraint graph over a large alphabet reduces the
alphabet to a constant one (`Complexity.Computability.PCP.Composition`): for this, the number of
queries and the rejection rate must not depend on the alphabet, however large the proof is.

The tester here, for constraints on labels in `Fin k`, follows Arora and Barak
[Arora and Barak, Chapter 22][AroraBarak09] and is built on the Hadamard tester for quadratic
equations (`Complexity.Foundations.BooleanAnalysis.HadamardTester`).

* A label `a` is encoded by its **long code** `BitString.longCode a`, the dictator `r ↦ r a` on
  `BitString k`, which is the Hadamard encoding of the indicator vector of `a`. The long codes of
  distinct labels differ on half of the inputs, so a table within relative distance `1/4` of a long
  code determines its label (`BitString.eq_of_hammingDist_longCode_lt`).
* The labels `σ : Fin 2 → Fin k` of the two ends are described by `2 * k` Boolean variables, their
  **one-hot encoding** `HadamardTester.oneHot σ`. The constraint becomes a system of quadratic
  equations in the variables (`HadamardTester.equationCoeff`): no two variables incompatible with
  `C` are both set, and an odd number of the variables of each end are set. Its solutions are the
  one-hot encodings of the labels satisfying `C`
  (`HadamardTester.forall_hadamardCode_tensor_equationCoeff_iff`). Reading the Hadamard encoding of
  the one-hot encoding at the vector that is `r` on the variables of an end and zero elsewhere
  (`HadamardTester.endEmbed`) reads the long code of the label of that end at `r`.
* The proof consists of a *linear table*, supposedly the Hadamard encoding of the variables, and a
  *quadratic table*, supposedly that of their tensor square. On independent random strings, the
  tester `hadamardTester C` runs five checks, each a local test
  (`Complexity.Computability.PCP.LocalTest`): the linearity test on both tables, the tensor test,
  the equation test for the quadratic equations of `C`, and the *input test*, which compares the
  bit of the table of a random end at a random point with the self-corrected read of the linear
  table at the corresponding vector. It accepts when all five do, and makes `17` queries.

If the tester accepts with probability at least `1 - ρ` for some `ρ < 1/28`, the linear table is
within `ρ` of the Hadamard encoding of a solution of the equations, which is the one-hot encoding of
labels satisfying `C`, and the input test puts the tables within distance `3ρ` of the long codes of
these labels (`HadamardTester.exists_inputDist_le_of_le_acceptProb`). So the tester rejects with
probability at least `1/28` times the distance of the tables from the long codes of satisfying
labels (`HadamardTester.exists_inputDist_div_le_one_sub_acceptProb`). As a constraint graph, over
the alphabet `Bool × (HadamardTester.Query → Bool)` of `2 ^ 18` symbols, it is an assignment tester
in the sense of Dinur: a labelling violates a proportion of the edges at least `1/476` times that
distance (`HadamardTester.exists_inputDist_div_le_unsatFrac`).

## Main definitions

* `Cslib.BitString.longCode`: the long code of a label.
* `Cslib.PCP.HadamardTester.oneHot`: the one-hot encoding of the labels of the two ends.
* `Cslib.PCP.HadamardTester.equationCoeff`, `Cslib.PCP.HadamardTester.equationRhs`: the quadratic
  equations of a constraint.
* `Cslib.PCP.HadamardTester.blrTest`, `Cslib.PCP.HadamardTester.tensorTest`,
  `Cslib.PCP.HadamardTester.equationTest`, `Cslib.PCP.HadamardTester.inputTest`: the checks of the
  tester, as local tests.
* `Cslib.PCP.hadamardTester`: the assignment tester of a constraint.
* `Cslib.PCP.HadamardTester.inputDist`: the distance of the tables of a proof from the long codes
  of labels.
* `Cslib.PCP.HadamardTester.honestProof`: the proof of satisfying labels.

## Main results

* `Cslib.BitString.eq_of_hammingDist_longCode_lt`: unique decoding of the long code.
* `Cslib.PCP.HadamardTester.forall_hadamardCode_tensor_equationCoeff_iff`: the solutions of the
  quadratic equations of a constraint are the one-hot encodings of its satisfying labels.
* `Cslib.PCP.HadamardTester.passes_honestProof`: completeness of the tester.
* `Cslib.PCP.HadamardTester.exists_inputDist_le_of_le_acceptProb`,
  `Cslib.PCP.HadamardTester.exists_inputDist_div_le_one_sub_acceptProb`,
  `Cslib.PCP.HadamardTester.one_div_le_one_sub_acceptProb_of_forall_not`: soundness of the tester.
* `Cslib.PCP.HadamardTester.satisfies_toConstraintGraph_honestProof`,
  `Cslib.PCP.HadamardTester.exists_inputDist_div_le_unsatFrac`,
  `Cslib.PCP.HadamardTester.one_div_le_unsatFrac_of_forall_not`: completeness and soundness of the
  tester as a constraint graph.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Cslib.BitString

variable {k n : ℕ}

/-! ### The long code -/

/-- The **long code** of a label `a : Fin k`: the Boolean function `r ↦ r a` on `BitString k`, the
dictator of the coordinate `a`. It is the Hadamard encoding of the indicator vector of `a`
(`BitString.longCode_eq_hadamardCode`). -/
def longCode (a : Fin k) : BooleanFunction k :=
  fun r ↦ r a

@[simp]
theorem longCode_apply (a : Fin k) (r : BitString k) : longCode a r = r a :=
  rfl

/-- The long code of `a` is the Hadamard encoding of the indicator vector of `a`. -/
theorem longCode_eq_hadamardCode (a : Fin k) :
    longCode a = hadamardCode fun i ↦ decide (i = a) := by
  funext r
  rw [hadamardCode_comm, hadamardCode_apply_decide_eq, longCode_apply]

/-- **Unique decoding of the long code**: a Boolean function within relative distance less than
`1/4` of the long codes of `a` and of `b` forces `a = b`. -/
theorem eq_of_hammingDist_longCode_lt {f : BooleanFunction k} {a b : Fin k}
    (ha : (hammingDist f (longCode a) : ℝ) / 2 ^ k < 1 / 4)
    (hb : (hammingDist f (longCode b) : ℝ) / 2 ^ k < 1 / 4) : a = b := by
  rw [longCode_eq_hadamardCode] at ha hb
  have h := congrFun (eq_of_hammingDist_hadamardCode_le (max_lt ha hb) (le_max_left _ _)
    (le_max_right _ _)) a
  simpa using h.symm

/-- The relative Hamming distance between two Boolean functions is the probability that they
differ at a uniformly random input. -/
theorem hammingDist_div_eq_expect (f g : BooleanFunction k) :
    (hammingDist f g : ℝ) / 2 ^ k = 𝔼 r, if f r ≠ g r then 1 else 0 := by
  rw [Fintype.expect_eq_sum_div_card, sum_boole, BitString.card_eq, Nat.cast_pow, Nat.cast_ofNat]
  rfl

/-- The Hadamard encoding of the tensor square of `x`, read at a unit vector, is a product of two
bits of `x`. -/
theorem hadamardCode_tensor_single (x : BitString n) (p p' : Fin n) :
    hadamardCode (tensor x x) (Pi.single (finProdFinEquiv (p, p')) 1) = (x p && x p') := by
  rw [hadamardCode_apply, dotProduct_single, mul_one, tensor_finProdFinEquiv]

end Cslib.BitString

namespace Cslib.PCP

open BitString

variable {k m n N : ℕ}

namespace HadamardTester

/-! ### The one-hot encoding and the quadratic equations of a constraint -/

/-- The **one-hot encoding** of the labels `σ : Fin 2 → Fin k` of the two ends of an edge, as
`2 * k` Boolean variables: the variable at `finProdFinEquiv (b, a)` is set exactly when the end `b`
has the label `a`. -/
def oneHot (σ : Fin 2 → Fin k) : BitString (2 * k) :=
  fun p ↦ decide (σ (finProdFinEquiv.symm p).1 = (finProdFinEquiv.symm p).2)

@[simp]
theorem oneHot_finProdFinEquiv (σ : Fin 2 → Fin k) (b : Fin 2) (a : Fin k) :
    oneHot σ (finProdFinEquiv (b, a)) = decide (σ b = a) := by
  simp [oneHot]

/-- Two variables, given by an end and a label, are **compatible** with the constraint `C` when
some labels satisfying `C` set both of them. -/
def Compatible (C : Fin k → Fin k → Prop) (p p' : Fin 2 × Fin k) : Prop :=
  ∃ σ : Fin 2 → Fin k, C (σ 0) (σ 1) ∧ σ p.1 = p.2 ∧ σ p'.1 = p'.2

open Classical in
/-- The coefficients of the **quadratic equations of the constraint `C`** in the `2 * k` variables
`x`, as linear equations `hadamardCode (tensor x x) (equationCoeff C e) = equationRhs e` in the
tensor square of the variables: for every pair of variables incompatible with `C`, the equation
saying that they are not both set, and for every end, the equation saying that an odd number of its
variables are set. Their solutions are the one-hot encodings of the labels satisfying `C`
(`forall_hadamardCode_tensor_equationCoeff_iff`). -/
noncomputable def equationCoeff (C : Fin k → Fin k → Prop) :
    Fin (2 * k * (2 * k) + 2) → BitString (2 * k * (2 * k)) :=
  Fin.append
    (fun q ↦ if Compatible C (finProdFinEquiv.symm (finProdFinEquiv.symm q).1)
        (finProdFinEquiv.symm (finProdFinEquiv.symm q).2) then 0 else Pi.single q 1)
    fun b ↦ ∑ a, Pi.single (finProdFinEquiv (finProdFinEquiv (b, a), finProdFinEquiv (b, a))) 1

/-- The right-hand sides of the quadratic equations of a constraint: `0` for the pairs of
variables, `1` for the ends. -/
def equationRhs : BitString (2 * k * (2 * k) + 2) :=
  Fin.append (0 : BitString (2 * k * (2 * k))) (1 : BitString 2)

open Classical in
/-- The equation of a pair of variables, read on the tensor square of `x`. -/
theorem hadamardCode_tensor_equationCoeff_castAdd (C : Fin k → Fin k → Prop)
    (x : BitString (2 * k)) (p p' : Fin 2 × Fin k) :
    hadamardCode (tensor x x) (equationCoeff C
        (Fin.castAdd 2 (finProdFinEquiv (finProdFinEquiv p, finProdFinEquiv p')))) =
      if Compatible C p p' then false else (x (finProdFinEquiv p) && x (finProdFinEquiv p')) := by
  classical
  rw [equationCoeff, Fin.append_left]
  simp only [Equiv.symm_apply_apply]
  split_ifs
  · rw [hadamardCode_apply, dotProduct_zero, Bool.zero_eq_false]
  · exact hadamardCode_tensor_single x _ _

/-- The equation of an end, read on the tensor square of `x`: the sum of the variables of the
end. -/
theorem hadamardCode_tensor_equationCoeff_natAdd (C : Fin k → Fin k → Prop)
    (x : BitString (2 * k)) (b : Fin 2) :
    hadamardCode (tensor x x) (equationCoeff C (Fin.natAdd _ b)) =
      ∑ a, x (finProdFinEquiv (b, a)) := by
  rw [equationCoeff, Fin.append_right, hadamardCode_apply, dotProduct_sum]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [← hadamardCode_apply, hadamardCode_tensor_single, Bool.and_self]

/-- **The quadratic equations of a constraint**: their solutions are exactly the one-hot encodings
of the labels satisfying the constraint. -/
theorem forall_hadamardCode_tensor_equationCoeff_iff {C : Fin k → Fin k → Prop}
    {x : BitString (2 * k)} :
    (∀ e, hadamardCode (tensor x x) (equationCoeff C e) = equationRhs e) ↔
      ∃ σ : Fin 2 → Fin k, C (σ 0) (σ 1) ∧ x = oneHot σ := by
  classical
  -- The equations of the pairs of variables and those of the ends.
  have hiff : (∀ e, hadamardCode (tensor x x) (equationCoeff C e) = equationRhs e) ↔
      (∀ p p', ¬ Compatible C p p' → (x (finProdFinEquiv p) && x (finProdFinEquiv p')) = false) ∧
        ∀ b, ∑ a, x (finProdFinEquiv (b, a)) = true := by
    rw [Fin.forall_fin_add]
    refine and_congr ⟨fun h p p' hpp' ↦ ?_, fun h q ↦ ?_⟩ ?_
    · have h := h (finProdFinEquiv (finProdFinEquiv p, finProdFinEquiv p'))
      rwa [hadamardCode_tensor_equationCoeff_castAdd, ite_eq_right hpp', equationRhs,
        Fin.append_left] at h
    · obtain ⟨⟨P, P'⟩, rfl⟩ := finProdFinEquiv.surjective q
      obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective P
      obtain ⟨p', rfl⟩ := finProdFinEquiv.surjective P'
      rw [hadamardCode_tensor_equationCoeff_castAdd, equationRhs, Fin.append_left]
      split_ifs with hpp'
      · rfl
      · exact h p p' hpp'
    · refine forall_congr' fun b ↦ ?_
      rw [hadamardCode_tensor_equationCoeff_natAdd, equationRhs, Fin.append_right]
      rfl
  rw [hiff]
  constructor
  · rintro ⟨hpair, hsum⟩
    -- Every end has a set variable.
    have hex (b : Fin 2) : ∃ a, x (finProdFinEquiv (b, a)) = true := by
      by_contra! h
      have h0 : ∑ a, x (finProdFinEquiv (b, a)) = 0 :=
        sum_eq_zero fun a _ ↦ by simpa [Bool.zero_eq_false] using h a
      rw [hsum b] at h0
      exact absurd h0 (by decide)
    choose σ hσ using hex
    -- Two variables of the same end, or of the two ends violating `C`, are never both set.
    have hboth {p p' : Fin 2 × Fin k} (hp : x (finProdFinEquiv p) = true)
        (hp' : x (finProdFinEquiv p') = true) : Compatible C p p' := by
      by_contra hpp'
      have h := hpair p p' hpp'
      rw [hp, hp', Bool.and_self] at h
      exact absurd h (by decide)
    refine ⟨σ, ?_, funext fun q ↦ ?_⟩
    · obtain ⟨τ, hτ, h0, h1⟩ := hboth (hσ 0) (hσ 1)
      have hτσ : τ = σ := funext <| Fin.forall_fin_two.2 ⟨h0, h1⟩
      rwa [hτσ] at hτ
    · obtain ⟨⟨b, a⟩, rfl⟩ := finProdFinEquiv.surjective q
      rw [oneHot_finProdFinEquiv]
      by_cases ha : σ b = a
      · rw [← ha, hσ b]
        exact (decide_eq_true rfl).symm
      · rw [decide_eq_false ha]
        by_contra hx
        obtain ⟨τ, -, hτ, hτ'⟩ := hboth (Bool.not_eq_false _ ▸ hx) (hσ b)
        exact ha (hτ'.symm.trans hτ)
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨fun p p' hpp' ↦ ?_, fun b ↦ ?_⟩
    · rw [oneHot_finProdFinEquiv, oneHot_finProdFinEquiv]
      by_contra h
      simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at h
      exact hpp' ⟨σ, hσ, h.1, h.2⟩
    · simp_rw [oneHot_finProdFinEquiv]
      rw [sum_eq_single (σ b) (fun a _ ha ↦ decide_eq_false (Ne.symm ha)) (by simp)]
      exact decide_eq_true rfl

/-- The assignment of the `2 * k` variables that is `r` on the variables of the end `b` and zero on
those of the other end. -/
def endEmbed (b : Fin 2) (r : BitString k) : BitString (2 * k) :=
  fun p ↦ decide ((finProdFinEquiv.symm p).1 = b) && r (finProdFinEquiv.symm p).2

/-- The Hadamard encoding of the variables `x`, read at `endEmbed b r`, is that of the variables of
the end `b`, read at `r`. -/
theorem hadamardCode_endEmbed (x : BitString (2 * k)) (b : Fin 2) (r : BitString k) :
    hadamardCode x (endEmbed b r) = hadamardCode (fun a ↦ x (finProdFinEquiv (b, a))) r := by
  rw [hadamardCode_apply, hadamardCode_apply, dotProduct, dotProduct,
    ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type, sum_eq_single b]
  · simp [endEmbed]
  · intro b' _ hb'
    simp only [endEmbed, Equiv.symm_apply_apply, decide_eq_false hb', Bool.false_and]
    exact sum_eq_zero fun _ _ ↦ mul_zero _
  · simp

/-- The Hadamard encoding of the one-hot encoding of the labels `σ`, read at `endEmbed b r`, is the
long code of the label of the end `b`, read at `r`. -/
theorem hadamardCode_oneHot_endEmbed (σ : Fin 2 → Fin k) (b : Fin 2) (r : BitString k) :
    hadamardCode (oneHot σ) (endEmbed b r) = longCode (σ b) r := by
  rw [hadamardCode_endEmbed, longCode_eq_hadamardCode]
  congr 1
  funext a
  rw [oneHot_finProdFinEquiv, decide_eq_decide]
  exact eq_comm

/-! ### The checks, as local tests -/

/-- The **linearity test** of Blum, Luby and Rubinfeld, as a local test on a table
`f : BooleanFunction n`: on the random string `(x, y)`, it reads `f` at `x`, `y` and `x + y`, and
accepts when `(f x ^^ f y) = f (x + y)`. -/
def blrTest (n : ℕ) : LocalTest (BitString n) (BitString n × BitString n) (Fin 3) Bool where
  query ω := ![ω.1, ω.2, ω.1 + ω.2]
  Accepts _ a := (a 0 ^^ a 1) = a 2

/-- The linearity test accepts with the probability `blrAcceptance`. -/
theorem acceptProb_blrTest (f : BooleanFunction n) :
    (blrTest n).acceptProb f = blrAcceptance f := by
  simp only [LocalTest.acceptProb, Fintype.expect_prod, LocalTest.Passes, blrTest, blrAcceptance,
    Matrix.cons_val]
  refine expect_congr rfl fun x _ ↦ expect_congr rfl fun y _ ↦ ?_
  congr

/-- The **tensor test**, as a local test on the pair of tables `Sum.elim f g`: on the random string
`(y, z, r, s, t)`, it compares the self-corrected read of `g` at `tensor y z` with randomness `t`
with the product of the self-corrected reads of `f` at `y` and `z` with randomnesses `r` and `s`.
-/
def tensorTest (n : ℕ) : LocalTest (BitString n ⊕ BitString (n * n))
    (BitString n × BitString n × BitString n × BitString n × BitString (n * n)) (Fin 6) Bool where
  query ω := ![.inr ω.2.2.2.2, .inr (tensor ω.1 ω.2.1 + ω.2.2.2.2), .inl ω.2.2.1,
    .inl (ω.1 + ω.2.2.1), .inl ω.2.2.2.1, .inl (ω.2.1 + ω.2.2.2.1)]
  Accepts _ a := (a 0 ^^ a 1) = ((a 2 ^^ a 3) && (a 4 ^^ a 5))

/-- The tensor test accepts with the probability `tensorTestAcceptance`. -/
theorem acceptProb_tensorTest (f : BooleanFunction n) (g : BooleanFunction (n * n)) :
    (tensorTest n).acceptProb (Sum.elim f g) = tensorTestAcceptance f g := by
  simp only [LocalTest.acceptProb, Fintype.expect_prod, LocalTest.Passes, tensorTest,
    tensorTestAcceptance, selfCorrect, Matrix.cons_val, Sum.elim_inl, Sum.elim_inr]
  refine expect_congr rfl fun y _ ↦ expect_congr rfl fun z _ ↦ expect_congr rfl fun r _ ↦
    expect_congr rfl fun s _ ↦ expect_congr rfl fun t _ ↦ ?_
  congr

/-- The **equation test** for the linear equations `hadamardCode w (A e) = b e`, as a local test on
a table `g : BooleanFunction N`: on the random string `(κ, t)`, it compares the self-corrected read
of `g` at the sum of the `A e` with `κ e` set, with randomness `t`, with the sum of the `b e` with
`κ e` set. -/
def equationTest (A : Fin m → BitString N) (b : BitString m) :
    LocalTest (BitString N) (BitString m × BitString N) (Fin 2) Bool where
  query ω := ![ω.2, (fun j ↦ hadamardCode ω.1 fun e ↦ A e j) + ω.2]
  Accepts ω a := (a 0 ^^ a 1) = hadamardCode ω.1 b

/-- The equation test accepts with the probability `equationTestAcceptance`. -/
theorem acceptProb_equationTest (g : BooleanFunction N) (A : Fin m → BitString N)
    (b : BitString m) : (equationTest A b).acceptProb g = equationTestAcceptance g A b := by
  simp only [LocalTest.acceptProb, Fintype.expect_prod, LocalTest.Passes, equationTest,
    equationTestAcceptance, selfCorrect, Matrix.cons_val]
  refine expect_congr rfl fun κ _ ↦ expect_congr rfl fun t _ ↦ ?_
  congr

/-- The **input test**, as a local test on the tables of the two ends and the linear table,
`Sum.elim (fun p ↦ T p.1 p.2) f`: on the random string `(b, r, y)`, it compares the bit of the table
`T b` at `r` with the self-corrected read of `f` at `endEmbed b r` with randomness `y`. -/
def inputTest (k : ℕ) : LocalTest ((Fin 2 × BitString k) ⊕ BitString (2 * k))
    (Fin 2 × BitString k × BitString (2 * k)) (Fin 3) Bool where
  query ω := ![.inl (ω.1, ω.2.1), .inr ω.2.2, .inr (endEmbed ω.1 ω.2.1 + ω.2.2)]
  Accepts _ a := a 0 = (a 1 ^^ a 2)

/-- The input test accepts when the bit of the table of a random end at a random point is the
self-corrected read of the linear table at the corresponding vector. -/
theorem acceptProb_inputTest (T : Fin 2 → BooleanFunction k) (f : BooleanFunction (2 * k)) :
    (inputTest k).acceptProb (Sum.elim (fun p ↦ T p.1 p.2) f) =
      𝔼 b, 𝔼 r, 𝔼 y, if T b r = selfCorrect f (endEmbed b r) y then 1 else 0 := by
  simp only [LocalTest.acceptProb, Fintype.expect_prod, LocalTest.Passes, inputTest, selfCorrect,
    Matrix.cons_val, Sum.elim_inl, Sum.elim_inr]
  refine expect_congr rfl fun b _ ↦ expect_congr rfl fun r _ ↦ expect_congr rfl fun y _ ↦ ?_
  congr

/-- One step of a union bound: if `A` and `B` imply `F`, the indicator of the failure of `F` is at
most the sum of the indicators of the failures of `A` and of `B`. -/
private theorem one_sub_boole_le {A B F : Prop} [Decidable A] [Decidable B] [Decidable F]
    (h : A → B → F) :
    (if ¬ F then (1 : ℝ) else 0) ≤ (1 - if A then 1 else 0) + (1 - if B then 1 else 0) := by
  split_ifs <;> first | exact absurd (h ‹A› ‹B›) ‹¬F› | norm_num

/-- **Soundness of the input test**: if the linear table `f` is within relative distance `ε` of the
Hadamard encoding of `x`, then on average over the ends `b`, the table `T b` is within relative
distance `1 - p + 2ε` of `r ↦ hadamardCode x (endEmbed b r)`, where `p` is the acceptance
probability of the input test. -/
theorem expect_hammingDist_div_le_one_sub_acceptProb_inputTest {T : Fin 2 → BooleanFunction k}
    {f : BooleanFunction (2 * k)} {x : BitString (2 * k)} {ε : ℝ}
    (hf : (hammingDist f (hadamardCode x) : ℝ) / 2 ^ (2 * k) ≤ ε) :
    𝔼 b, (hammingDist (T b) (fun r ↦ hadamardCode x (endEmbed b r)) : ℝ) / 2 ^ k ≤
      1 - (inputTest k).acceptProb (Sum.elim (fun p ↦ T p.1 p.2) f) + 2 * ε := by
  -- Self-correction reads the encoding of `x` correctly with probability at least `1 - 2ε`.
  have hsc (b : Fin 2) (r : BitString k) : 𝔼 y, (1 - if selfCorrect f (endEmbed b r) y =
      hadamardCode x (endEmbed b r) then (1 : ℝ) else 0) ≤ 2 * ε := by
    have h := one_sub_two_mul_le_expect_selfCorrect_hadamardCode hf (endEmbed b r)
    rw [expect_sub_distrib, Fintype.expect_const]
    linarith
  calc 𝔼 b, (hammingDist (T b) (fun r ↦ hadamardCode x (endEmbed b r)) : ℝ) / 2 ^ k
      = 𝔼 b, 𝔼 r, 𝔼 _y : BitString (2 * k),
          if T b r ≠ hadamardCode x (endEmbed b r) then (1 : ℝ) else 0 := by
        simp only [hammingDist_div_eq_expect, Fintype.expect_const]
    _ ≤ 𝔼 b, 𝔼 r, 𝔼 y, ((1 - if T b r = selfCorrect f (endEmbed b r) y then (1 : ℝ) else 0) +
          (1 - if selfCorrect f (endEmbed b r) y = hadamardCode x (endEmbed b r) then (1 : ℝ)
            else 0)) := by
        gcongr with b _ r _ y _
        exact one_sub_boole_le fun h h' ↦ h.trans h'
    _ = 1 - (inputTest k).acceptProb (Sum.elim (fun p ↦ T p.1 p.2) f) + 𝔼 b, 𝔼 r, 𝔼 y,
          (1 - if selfCorrect f (endEmbed b r) y = hadamardCode x (endEmbed b r) then (1 : ℝ)
            else 0) := by
        rw [acceptProb_inputTest]
        simp only [expect_add_distrib]
        congr 1
        simp only [expect_sub_distrib, Fintype.expect_const]
    _ ≤ 1 - (inputTest k).acceptProb (Sum.elim (fun p ↦ T p.1 p.2) f) + 𝔼 _b : Fin 2,
          𝔼 _r : BitString k, 2 * ε := by
        gcongr with b _ r _
        exact hsc b r
    _ = 1 - (inputTest k).acceptProb (Sum.elim (fun p ↦ T p.1 p.2) f) + 2 * ε := by
        simp only [Fintype.expect_const]

/-! ### The tester -/

/-- The positions of the proofs read by the tester for constraints on labels in `Fin k`: the bit
`inl (b, r)` of the table of the end `b` at `r`, the bit `inr (inl y)` of the linear table at `y`,
and the bit `inr (inr z)` of the quadratic table at `z`. -/
abbrev Pos (k : ℕ) : Type :=
  (Fin 2 × BitString k) ⊕ (BitString (2 * k) ⊕ BitString (2 * k * (2 * k)))

/-- The random strings of the tester: those of its five checks. -/
abbrev Rand (k : ℕ) : Type :=
  (BitString (2 * k) × BitString (2 * k)) ×
    (BitString (2 * k * (2 * k)) × BitString (2 * k * (2 * k))) ×
    (BitString (2 * k) × BitString (2 * k) × BitString (2 * k) × BitString (2 * k) ×
      BitString (2 * k * (2 * k))) ×
    (BitString (2 * k * (2 * k) + 2) × BitString (2 * k * (2 * k))) ×
    (Fin 2 × BitString k × BitString (2 * k))

/-- The queries of the tester: three for each linearity test, six for the tensor test, two for the
equation test and three for the input test. -/
abbrev Query : Type :=
  Fin 3 ⊕ Fin 3 ⊕ Fin 6 ⊕ Fin 2 ⊕ Fin 3

/-- The tester makes `17` queries. -/
theorem card_query : Fintype.card Query = 17 :=
  rfl

/-- The tester uses `20 k² + 15 k + 3` random bits. -/
theorem card_rand : Fintype.card (Rand k) = 2 ^ (20 * k ^ 2 + 15 * k + 3) := by
  simp only [Fintype.card_prod, BitString.card_eq, Fintype.card_fin]
  ring

/-- The table of the end `b` carried by the proof `π`. -/
def inputTable (π : Pos k → Bool) (b : Fin 2) : BooleanFunction k :=
  fun r ↦ π (.inl (b, r))

/-- The linear table carried by the proof `π`. -/
def linTable (π : Pos k → Bool) : BooleanFunction (2 * k) :=
  fun y ↦ π (.inr (.inl y))

/-- The quadratic table carried by the proof `π`. -/
def quadTable (π : Pos k → Bool) : BooleanFunction (2 * k * (2 * k)) :=
  fun z ↦ π (.inr (.inr z))

end HadamardTester

open HadamardTester

/-- The **Hadamard assignment tester** of the constraint `C` on labels in `Fin k`
[Arora and Barak, Chapter 22][AroraBarak09]: on independent random strings, the linearity test on
the linear and on the quadratic table, the tensor test, the equation test for the quadratic
equations of `C`, and the input test; it accepts when all five accept. -/
noncomputable def hadamardTester (C : Fin k → Fin k → Prop) :
    LocalTest (Pos k) (Rand k) Query Bool :=
  ((blrTest _).map fun y ↦ .inr (.inl y)).and <|
    ((blrTest _).map fun z ↦ .inr (.inr z)).and <|
    ((tensorTest _).map (Sum.elim (fun y ↦ .inr (.inl y)) fun z ↦ .inr (.inr z))).and <|
    ((equationTest (equationCoeff C) equationRhs).map fun z ↦ .inr (.inr z)).and <|
    (inputTest k).map (Sum.elim .inl fun y ↦ .inr (.inl y))

namespace HadamardTester

variable {C : Fin k → Fin k → Prop}

/-- The tester accepts at most as often as each of its five checks. -/
theorem acceptProb_le (π : Pos k → Bool) :
    (hadamardTester C).acceptProb π ≤ blrAcceptance (linTable π) ∧
      (hadamardTester C).acceptProb π ≤ blrAcceptance (quadTable π) ∧
      (hadamardTester C).acceptProb π ≤ tensorTestAcceptance (linTable π) (quadTable π) ∧
      (hadamardTester C).acceptProb π ≤
        equationTestAcceptance (quadTable π) (equationCoeff C) equationRhs ∧
      (hadamardTester C).acceptProb π ≤
        (inputTest k).acceptProb (Sum.elim (fun p ↦ inputTable π p.1 p.2) (linTable π)) := by
  open LocalTest in
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine (acceptProb_and_le_left _ π).trans_eq ?_
    rw [acceptProb_map]
    exact acceptProb_blrTest _
  · refine (acceptProb_and_le_right _ π).trans <| (acceptProb_and_le_left _ π).trans_eq ?_
    rw [acceptProb_map]
    exact acceptProb_blrTest _
  · refine (acceptProb_and_le_right _ π).trans <| (acceptProb_and_le_right _ π).trans <|
      (acceptProb_and_le_left _ π).trans_eq ?_
    rw [acceptProb_map, Sum.comp_elim]
    exact acceptProb_tensorTest _ _
  · refine (acceptProb_and_le_right _ π).trans <| (acceptProb_and_le_right _ π).trans <|
      (acceptProb_and_le_right _ π).trans <| (acceptProb_and_le_left _ π).trans_eq ?_
    rw [acceptProb_map]
    exact acceptProb_equationTest _ _ _
  · refine (acceptProb_and_le_right _ π).trans <| (acceptProb_and_le_right _ π).trans <|
      (acceptProb_and_le_right _ π).trans <| (acceptProb_and_le_right _ π).trans_eq ?_
    rw [acceptProb_map, Sum.comp_elim]
    rfl

/-! ### Soundness -/

/-- The **distance of the tables** of the proof `π` from the long codes of the labels `σ`: the
relative Hamming distance of the table of an end from the long code of its label, averaged over the
two ends. It is the proportion of the positions of the two tables at which `π` differs from the
long codes. -/
noncomputable def inputDist (π : Pos k → Bool) (σ : Fin 2 → Fin k) : ℝ :=
  𝔼 b, (hammingDist (inputTable π b) (longCode (σ b)) : ℝ) / 2 ^ k

/-- The distance of the tables of `π` from the long codes of `σ` is the average of the distances
of the two tables. -/
theorem inputDist_eq (π : Pos k → Bool) (σ : Fin 2 → Fin k) :
    inputDist π σ = ((hammingDist (inputTable π 0) (longCode (σ 0)) : ℝ) / 2 ^ k +
      (hammingDist (inputTable π 1) (longCode (σ 1)) : ℝ) / 2 ^ k) / 2 := by
  rw [inputDist, Fintype.expect_eq_sum_div_card, Fin.sum_univ_two, Fintype.card_fin,
    Nat.cast_ofNat]

theorem inputDist_nonneg (π : Pos k → Bool) (σ : Fin 2 → Fin k) : 0 ≤ inputDist π σ := by
  rw [inputDist_eq]
  positivity

theorem inputDist_le_one (π : Pos k → Bool) (σ : Fin 2 → Fin k) : inputDist π σ ≤ 1 := by
  have h (b : Fin 2) : (hammingDist (inputTable π b) (longCode (σ b)) : ℝ) / 2 ^ k ≤ 1 := by
    rw [div_le_one (by positivity)]
    have := hammingDist_le_card_fintype (x := inputTable π b) (y := longCode (σ b))
    rw [BitString.card_eq] at this
    exact_mod_cast this
  rw [inputDist_eq]
  linarith [h 0, h 1]

/-- The distance of each table from the long code of its label is at most twice the distance of
the tables. -/
theorem hammingDist_inputTable_div_le (π : Pos k → Bool) (σ : Fin 2 → Fin k) (b : Fin 2) :
    (hammingDist (inputTable π b) (longCode (σ b)) : ℝ) / 2 ^ k ≤ 2 * inputDist π σ := by
  have h (b : Fin 2) : 0 ≤ (hammingDist (inputTable π b) (longCode (σ b)) : ℝ) / 2 ^ k := by
    positivity
  rw [inputDist_eq]
  fin_cases b <;> simp only [Fin.zero_eta, Fin.mk_one] <;> linarith [h 0, h 1]

/-- **Soundness of the Hadamard assignment tester**: if the tester of `C` accepts the proof `π`
with probability at least `1 - ρ` for some `ρ < 1/28`, then the tables of `π` are within distance
`3ρ` of the long codes of labels satisfying `C`. The linearity tests decode the linear and the
quadratic table to `x` and `w`; the tensor test forces `w` to be the tensor square of `x`, and the
equation test makes `x` a solution of the equations of `C`, hence the one-hot encoding of
satisfying labels; the input test then compares the tables with their long codes. -/
theorem exists_inputDist_le_of_le_acceptProb {π : Pos k → Bool} {ρ : ℝ} (hρ : ρ < 1 / 28)
    (h : 1 - ρ ≤ (hadamardTester C).acceptProb π) :
    ∃ σ : Fin 2 → Fin k, C (σ 0) (σ 1) ∧ inputDist π σ ≤ 3 * ρ := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := acceptProb_le (C := C) π
  obtain ⟨x, hx⟩ := exists_hammingDist_hadamardCode_le_of_le_blrAcceptance (h.trans h₁)
  obtain ⟨w, hw⟩ := exists_hammingDist_hadamardCode_le_of_le_blrAcceptance (h.trans h₂)
  obtain rfl := eq_tensor_of_lt_tensorTestAcceptance hx hw (by linarith)
  obtain ⟨σ, hσ, rfl⟩ := forall_hadamardCode_tensor_equationCoeff_iff.1
    (hadamardCode_eq_of_lt_equationTestAcceptance (A := equationCoeff C) (b := equationRhs) hw
      (by linarith))
  refine ⟨σ, hσ, ?_⟩
  have hin := expect_hammingDist_div_le_one_sub_acceptProb_inputTest (T := inputTable π) hx
  simp only [hadamardCode_oneHot_endEmbed] at hin
  rw [inputDist]
  linarith

/-- **Soundness of the Hadamard assignment tester** [Dinur, Definition 3.1][Dinur2007]: if the
constraint `C` is satisfiable, the tester of `C` rejects every proof with probability at least
`1/28` times the distance of its tables from the long codes of some labels satisfying `C`. -/
theorem exists_inputDist_div_le_one_sub_acceptProb (hC : ∃ a b, C a b) (π : Pos k → Bool) :
    ∃ σ : Fin 2 → Fin k, C (σ 0) (σ 1) ∧
      inputDist π σ / 28 ≤ 1 - (hadamardTester C).acceptProb π := by
  by_cases hρ : 1 - (hadamardTester C).acceptProb π < 1 / 28
  · obtain ⟨σ, hσ, hd⟩ := exists_inputDist_le_of_le_acceptProb hρ (by linarith)
    have := (hadamardTester C).acceptProb_le_one π
    exact ⟨σ, hσ, by linarith⟩
  · obtain ⟨a, b, hab⟩ := hC
    have := inputDist_le_one π ![a, b]
    exact ⟨![a, b], hab, by linarith⟩

/-- **Soundness of the Hadamard assignment tester** for an unsatisfiable constraint: the tester
rejects every proof with probability at least `1/28`. -/
theorem one_div_le_one_sub_acceptProb_of_forall_not (hC : ∀ a b, ¬ C a b)
    (π : Pos k → Bool) : 1 / 28 ≤ 1 - (hadamardTester C).acceptProb π := by
  by_contra! hρ
  obtain ⟨σ, hσ, -⟩ := exists_inputDist_le_of_le_acceptProb hρ (by linarith)
  exact hC _ _ hσ

/-! ### Completeness -/

/-- The **honest proof** for the labels `σ`: the long codes of the labels as the tables of the
ends, and the Hadamard encodings of their one-hot encoding and of its tensor square as the linear
and the quadratic table. -/
def honestProof (σ : Fin 2 → Fin k) : Pos k → Bool :=
  Sum.elim (fun p ↦ longCode (σ p.1) p.2)
    (Sum.elim (hadamardCode (oneHot σ)) (hadamardCode (tensor (oneHot σ) (oneHot σ))))

/-- The tables of the honest proof for `σ` are the long codes of `σ`. -/
@[simp]
theorem inputDist_honestProof (σ : Fin 2 → Fin k) : inputDist (honestProof σ) σ = 0 := by
  have h (b : Fin 2) : inputTable (honestProof σ) b = longCode (σ b) := rfl
  simp [inputDist, h]

/-- **Completeness of the Hadamard assignment tester**: the honest proof for labels satisfying the
constraint passes on every random string. -/
theorem passes_honestProof {σ : Fin 2 → Fin k} (hσ : C (σ 0) (σ 1))
    (ω : Rand k) : (hadamardTester C).Passes (honestProof σ) ω := by
  have h₁ (n : ℕ) (x : BitString n) := ((blrTest n).acceptProb_eq_one_iff
    (π := hadamardCode x)).1 (by rw [acceptProb_blrTest, blrAcceptance_hadamardCode])
  have h₃ := ((tensorTest (2 * k)).acceptProb_eq_one_iff (π := Sum.elim (hadamardCode (oneHot σ))
    (hadamardCode (tensor (oneHot σ) (oneHot σ))))).1
    (by rw [acceptProb_tensorTest, tensorTestAcceptance_hadamardCode])
  have h₄ := ((equationTest (equationCoeff C) equationRhs).acceptProb_eq_one_iff
    (π := hadamardCode (tensor (oneHot σ) (oneHot σ)))).1
    (by rw [acceptProb_equationTest, equationTestAcceptance_hadamardCode
      (forall_hadamardCode_tensor_equationCoeff_iff.2 ⟨σ, hσ, rfl⟩)])
  obtain ⟨ω₁, ω₂, ω₃, ω₄, b, r, y⟩ := ω
  simp only [hadamardTester, LocalTest.passes_and, LocalTest.passes_map]
  refine ⟨h₁ _ _ ω₁, h₁ _ _ ω₂, ?_, h₄ ω₄, ?_⟩
  · rw [Sum.comp_elim]
    exact h₃ ω₃
  · rw [Sum.comp_elim]
    change longCode (σ b) r = selfCorrect (hadamardCode (oneHot σ)) (endEmbed b r) y
    rw [selfCorrect_hadamardCode, hadamardCode_oneHot_endEmbed]

/-- **Completeness of the Hadamard assignment tester**: the honest proof for labels satisfying the
constraint is accepted with probability one. -/
theorem acceptProb_honestProof {σ : Fin 2 → Fin k} (hσ : C (σ 0) (σ 1)) :
    (hadamardTester C).acceptProb (honestProof σ) = 1 :=
  ((hadamardTester C).acceptProb_eq_one_iff).2 (passes_honestProof hσ)

/-! ### The tester as a constraint graph -/

/-- **Completeness of the tester as a constraint graph** [Dinur, Definition 3.1][Dinur2007]: for
labels satisfying the constraint, the labelling of the constraint graph of the tester by the honest
proof, whose positions of the tables carry the long codes of the labels, satisfies every edge. -/
theorem satisfies_toConstraintGraph_honestProof {σ : Fin 2 → Fin k}
    (hσ : C (σ 0) (σ 1)) (γ : Bool) (x : Rand k × Query) :
    (hadamardTester C).toConstraintGraph.Satisfies
      ((hadamardTester C).labellingOf (honestProof σ) γ) x :=
  LocalTest.satisfies_labellingOf (passes_honestProof hσ x.1)

/-- **Soundness of the tester as a constraint graph** [Dinur, Definition 3.1][Dinur2007]: if the
constraint `C` is satisfiable, every labelling of the constraint graph of the tester violates a
proportion of the edges at least `1/476` times the distance of the tables it carries from the long
codes of some labels satisfying `C`. -/
theorem exists_inputDist_div_le_unsatFrac (hC : ∃ a b, C a b)
    (A : Pos k ⊕ Rand k → Bool × (Query → Bool)) :
    ∃ σ : Fin 2 → Fin k, C (σ 0) (σ 1) ∧
      inputDist (LocalTest.proofOf A) σ / 476 ≤
        (hadamardTester C).toConstraintGraph.unsatFrac A := by
  obtain ⟨σ, hσ, h⟩ := exists_inputDist_div_le_one_sub_acceptProb hC (LocalTest.proofOf A)
  have h' := LocalTest.one_sub_acceptProb_le_card_mul_unsatFrac (T := hadamardTester C) A
  rw [card_query, Nat.cast_ofNat] at h'
  exact ⟨σ, hσ, by linarith⟩

/-- **Soundness of the tester as a constraint graph** for an unsatisfiable constraint: every
labelling violates a proportion at least `1/476` of the edges. -/
theorem one_div_le_unsatFrac_of_forall_not (hC : ∀ a b, ¬ C a b)
    (A : Pos k ⊕ Rand k → Bool × (Query → Bool)) :
    1 / 476 ≤ (hadamardTester C).toConstraintGraph.unsatFrac A := by
  have h := one_div_le_one_sub_acceptProb_of_forall_not hC (LocalTest.proofOf A)
  have h' := LocalTest.one_sub_acceptProb_le_card_mul_unsatFrac (T := hadamardTester C) A
  rw [card_query, Nat.cast_ofNat] at h'
  linarith

end HadamardTester

end Cslib.PCP
