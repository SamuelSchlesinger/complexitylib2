/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.Determinant
public import Complexity.Computability.Circuit.Boolean.Encoding
public import Complexity.Computability.Circuit.Boolean.PPoly
public import Complexity.Computability.Complexity.Classes.EXP
public import Complexity.Computability.Complexity.Classes.PH
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.LinearAlgebra.Matrix.Permanent
import Complexity.Computability.Complexity.Classes.Inclusions
import Complexity.Computability.Complexity.Classes.PH.Kannan
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Polynomial identity testing, the Schwartz–Zippel lemma and Kabanets–Impagliazzo

*Polynomial identity testing* (`PIT`) asks whether a given arithmetic circuit computes the zero
formal polynomial. Over the integers, `Cslib.Circuits.Arithmetic.PITInt` is the set of pairs
`⟨n, c⟩ : Σ n, Circuit (arithSignature ℤ) n 1` with `c.polynomial 0 = 0` in
`MvPolynomial (Fin n) ℤ`, encoded as bit strings by `Cslib.Circuits.Arithmetic.encArithCircuitInt`
(number of inputs in unary, gate operations with binary integer constants via `encIntBin`, and
wire indices in binary).

This file develops three components connecting polynomial identity testing, randomized zero testing
and algebraic-to-Boolean circuit lower bounds:

1. **The multivariate Schwartz–Zippel lemma** [Schwartz][Schwartz1980], [Zippel][Zippel1979],
   [DeMillo and Lipton][DeMilloLipton1978], [Arora and Barak, Lemma 7.22][AroraBarak09]: over any
   integral domain `R`, a nonzero polynomial `P : MvPolynomial (Fin n) R` of total degree `d` has
   at most `d * #S ^ (n - 1)` roots in `S ^ n` (`MvPolynomial.card_roots_le`), and if `d < #S`
   then `P` evaluates to a nonzero element at some point of `S ^ n`
   (`MvPolynomial.exists_eval_ne_zero_of_totalDegree_lt_card`). Specializing to `c.polynomial 0`
   bounds the zero set of any arithmetic circuit outside `PITInt`
   (`Cslib.Circuits.Arithmetic.card_roots_eval_le_of_notMem_PITInt`,
   `Cslib.Circuits.Arithmetic.exists_eval_ne_zero_of_notMem_PITInt`).

2. **Laplace cofactor expansion of the permanent and downward self-reducibility to `PITInt`**
   [Kabanets and Impagliazzo, Lemma 4.2][KabanetsImpagliazzo2004],
   [Arora and Barak, Theorem 20.16][AroraBarak09]: for any `(n + 1) × (n + 1)` matrix `A`,
   `A.permanent = ∑ j, A 0 j * (A.submatrix Fin.succ j.succAbove).permanent`
   (`Matrix.permanent_succ_row_zero`). On the generic matrix `genericMatrix R (m + 1)`, each minor
   is a variable reindexing of `genericMatrix R m` (`permanent_genericMatrix_succ`). Using explicit
   arithmetic circuit combinators (`constCircuit`, `varCircuit`, `addCircuit`, `mulCircuit`,
   `negCircuit`, `subCircuit`, `reindexCircuit`, `finSumCircuit`), we construct the base test
   circuit `permBaseDiff` and the Laplace step test circuit `permStepDiff` with explicit polynomial
   gate-size bounds (`size_permBaseDiff`, `size_permStepDiff`). A candidate family
   `C : ∀ m, Circuit (arithSignature ℤ) (m * m) 1` computes `(genericMatrix ℤ m).permanent` for all
   `m ≤ n` if and only if `⟨0, permBaseDiff (C 0)⟩ ∈ PITInt` and
   `⟨(m + 1) * (m + 1), permStepDiff m (C m) (C (m + 1))⟩ ∈ PITInt` for all `m < n`
   (`forall_polynomial_eq_permanent_iff_mem_PITInt`). When `PITInt ∈ P encArithCircuitInt` and the
   integer permanent family `intPermFamily` lies in `VP ℤ`, a polynomial-time decider for `PITInt`
   soundly and completely certifies permanent circuit chains
   (`exists_certified_perm_family_of_PITInt_mem_P_of_mem_VP`).

3. **`NEXP` circuit lower bounds and the Kabanets–Impagliazzo theorem**
   [Kabanets and Impagliazzo, Theorem 4.1][KabanetsImpagliazzo2004],
   [Arora and Barak, Theorem 20.16][AroraBarak09]:
   - Unconditionally, combining Kannan's theorem (`exists_mem_SigmaP_two_notMem_SIZE`) with the
     inclusion `Σ₂ ⊆ PH ⊆ PSPACE ⊆ EXP ⊆ NEXP` (`SigmaP_subset_NEXP`) shows that for every fixed
     degree `k`, `NEXP` contains a language outside `SIZE (c (n + 1) ^ k)`
     (`exists_mem_NEXP_notMem_SIZE`).
   - Conditionally on `PITInt ∈ P encArithCircuitInt` and the Impagliazzo–Kabanets–Wigderson /
     Valiant–Toda collapse from a polynomial-time PIT-certified permanent circuit family under
     `NEXP ⊆ P/poly`, either `NEXP ⊄ P/poly` or `intPermFamily ∉ VP ℤ`
     (`kabanets_impagliazzo`, `kabanets_impagliazzo_of_EXP_subset_P`). The external collapse step
     (combining `#P`-completeness of the permanent with the easy-witness collapse
     `NEXP ⊆ P/poly ⇒ NEXP = MA`) is taken as an explicit hypothesis.

## Main definitions

* `Cslib.Circuits.Arithmetic.encArithOpInt`, `Cslib.Circuits.Arithmetic.encArithGateInt`,
  `Cslib.Circuits.Arithmetic.encArithCodeInt`, `Cslib.Circuits.Arithmetic.encArithCircuitInt`:
  injective bit-string encoding of single-output integer arithmetic circuits.
* `Cslib.Circuits.Arithmetic.PITInt`: the Polynomial Identity Testing problem over `ℤ`.
* `Cslib.Circuits.Arithmetic.permFamily`, `Cslib.Circuits.Arithmetic.intPermFamily`: the permanent
  family `n ↦ (genericMatrix R n).permanent` and its integer specialization.
* `Cslib.Circuits.Arithmetic.constCircuit`, `varCircuit`, `addCircuit`, `mulCircuit`, `negCircuit`,
  `subCircuit`, `reindexCircuit`, `finSumCircuit`: constructive arithmetic circuit combinators.
* `Cslib.Circuits.Arithmetic.minorVar`, `permBaseDiff`, `permStepDiff`, `laplacePermCircuit`,
  `IsLaplacePermChain`: the Laplace cofactor difference circuits, explicit recursive permanent
  circuit family, and Laplace permanent chain predicate reducing permanent verification to `PITInt`.
* `Cslib.Circuits.Arithmetic.PermPITCertified`: existence of a polynomial-time `PITInt` decider and
  a polynomially bounded arithmetic circuit family certified by it on all Laplace permanent
  identities.

## Main results

* `MvPolynomial.card_mul_card_roots_le`, `MvPolynomial.card_roots_le`,
  `MvPolynomial.exists_eval_ne_zero_of_totalDegree_lt_card`: the multivariate Schwartz–Zippel
  lemma and its non-vanishing corollary.
* `Cslib.Circuits.Arithmetic.card_roots_eval_le_of_notMem_PITInt`,
  `Cslib.Circuits.Arithmetic.exists_eval_ne_zero_of_notMem_PITInt`: Schwartz–Zippel zero bounds for
  arithmetic circuits outside `PITInt`.
* `Matrix.permanent_succ_column_zero`, `Matrix.permanent_succ_row_zero`: Laplace cofactor expansion
  of the permanent along column 0 and row 0.
* `Cslib.Circuits.Arithmetic.permanent_genericMatrix_zero`,
  `Cslib.Circuits.Arithmetic.permanent_genericMatrix_succ`: Laplace recurrence for the generic
  permanent polynomial.
* `Cslib.Circuits.Arithmetic.forall_polynomial_eq_permanent_iff_mem_PITInt`: Kabanets–Impagliazzo
  Lemma 4.2, characterizing permanent circuits up to dimension `n` via `n + 1` instances of
  `PITInt`.
* `Cslib.Circuits.Arithmetic.exists_certified_perm_family_of_PITInt_mem_P_of_mem_VP`:
  `PITInt ∈ P` and `intPermFamily ∈ VP ℤ` yield a `PermPITCertified` permanent tester.
* `Cslib.Complexity.exists_mem_NEXP_notMem_SIZE`: unconditional fixed-degree circuit lower bound
  in `NEXP`.
* `Cslib.Circuits.Arithmetic.kabanets_impagliazzo`,
  `Cslib.Circuits.Arithmetic.kabanets_impagliazzo_of_EXP_subset_P`: the Kabanets–Impagliazzo
  derandomization-to-lower-bounds theorem.

## References

* [V. Kabanets, R. Impagliazzo, *Derandomizing polynomial identity tests means proving circuit
  lower bounds*][KabanetsImpagliazzo2004]
* [J. T. Schwartz, *Fast probabilistic algorithms for verification of polynomial
  identities*][Schwartz1980]
* [R. Zippel, *Probabilistic algorithms for sparse polynomials*][Zippel1979]
* [R. A. DeMillo, R. J. Lipton, *A probabilistic remark on algebraic program
  testing*][DeMilloLipton1978]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Lemma 7.22 and
  Theorem 20.16][AroraBarak09]
-/

@[expose] public section

/-! ### The multivariate Schwartz–Zippel lemma -/

namespace MvPolynomial

open Finset Fintype

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **The Schwartz–Zippel lemma** (cleared-denominator form) [Schwartz][Schwartz1980],
[Zippel][Zippel1979], [DeMillo and Lipton][DeMilloLipton1978],
[Arora and Barak, Lemma 7.22][AroraBarak09]: for a nonzero polynomial `P` in `n` variables over an
integral domain `R` and a finite subset `S ⊆ R`, the number of roots of `P` in `S ^ n` multiplied
by `#S` is at most `P.totalDegree * #S ^ n`. -/
theorem card_mul_card_roots_le [DecidableEq R] {n : ℕ} {P : MvPolynomial (Fin n) R}
    (hP : P ≠ 0) (S : Finset R) :
    S.card * #(piFinset (fun _ : Fin n => S) |>.filter (fun x => eval x P = 0)) ≤
      P.totalDegree * S.card ^ n := by
  rcases Nat.eq_zero_or_pos S.card with hcard | hcard
  · simp [hcard]
  · have hq := schwartz_zippel_totalDegree hP S
    have hSpos : (0 : ℚ≥0) < S.card := Nat.cast_pos.mpr hcard
    have hSnpos : (0 : ℚ≥0) < (S.card : ℚ≥0) ^ n := pow_pos hSpos n
    rw [div_le_div_iff₀ hSnpos hSpos, mul_comm _ (S.card : ℚ≥0)] at hq
    exact_mod_cast hq

/-- **The Schwartz–Zippel lemma** [Schwartz][Schwartz1980], [Zippel][Zippel1979],
[DeMillo and Lipton][DeMilloLipton1978], [Arora and Barak, Lemma 7.22][AroraBarak09]: a nonzero
polynomial `P` in `n` variables over an integral domain `R` vanishes at at most
`P.totalDegree * #S ^ (n - 1)` points of `S ^ n`. -/
theorem card_roots_le [DecidableEq R] {n : ℕ} {P : MvPolynomial (Fin n) R}
    (hP : P ≠ 0) (S : Finset R) :
    #(piFinset (fun _ : Fin n => S) |>.filter (fun x => eval x P = 0)) ≤
      P.totalDegree * S.card ^ (n - 1) := by
  cases n with
  | zero =>
    rw [P.eq_C_of_isEmpty] at hP ⊢
    simp [C_ne_zero.mp hP]
  | succ m =>
    rcases Nat.eq_zero_or_pos S.card with hcard | hcard
    · have hemp : S = ∅ := card_eq_zero.mp hcard
      subst hemp
      simp
    · have hmul := card_mul_card_roots_le hP S
      rw [pow_succ', ← mul_left_comm] at hmul
      exact Nat.le_of_mul_le_mul_left hmul hcard

/-- **Non-vanishing corollary of Schwartz–Zippel**: if `P ≠ 0` and `P.totalDegree < #S`, then `P`
evaluates to a nonzero value at some point in `S ^ n`. -/
theorem exists_eval_ne_zero_of_totalDegree_lt_card {n : ℕ} {P : MvPolynomial (Fin n) R}
    (hP : P ≠ 0) {S : Finset R} (hdeg : P.totalDegree < S.card) :
    ∃ x : Fin n → R, (∀ i, x i ∈ S) ∧ eval x P ≠ 0 := by
  classical
  have hSpos : 0 < S.card := Nat.pos_of_ne_zero fun h => by omega
  have hSnpos : 0 < S.card ^ n := Nat.pow_pos hSpos
  have hmul := card_mul_card_roots_le hP S
  have hlt : P.totalDegree * S.card ^ n < S.card * S.card ^ n :=
    Nat.mul_lt_mul_of_pos_right hdeg hSnpos
  have hroots_lt :
      #(piFinset (fun _ : Fin n => S) |>.filter (fun x => eval x P = 0)) <
        #(piFinset (fun _ : Fin n => S)) := by
    rw [card_piFinset, prod_const, card_univ, Fintype.card_fin]
    exact lt_of_mul_lt_mul_left (hmul.trans_lt hlt) (Nat.zero_le _)
  by_contra! hall
  have heq : (piFinset (fun _ : Fin n => S) |>.filter (fun x => eval x P = 0)) =
      piFinset (fun _ : Fin n => S) :=
    filter_eq_self.mpr fun x hx => hall x fun i => mem_piFinset.mp hx i
  rw [heq] at hroots_lt
  exact lt_irrefl _ hroots_lt

end MvPolynomial

/-! ### Laplace expansion of the permanent -/

namespace Matrix

open Equiv Finset Fintype

variable {R : Type*} [CommSemiring R]

/-- **Laplace expansion of the permanent along column 0.** -/
theorem permanent_succ_column_zero {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    A.permanent = ∑ i : Fin (n + 1), A i 0 * (A.submatrix i.succAbove Fin.succ).permanent := by
  rw [Matrix.permanent, Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product, Matrix.submatrix]
  refine Finset.sum_congr rfl fun i _ => Fin.cases ?_ (fun i => ?_) i
  · simp [Fin.prod_univ_succ, Matrix.permanent, Finset.mul_sum]
  · rw [← permanent_permute_cols i.cycleRange, Matrix.permanent, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [Fin.prod_univ_succ, Fin.succAbove_cycleRange]

/-- **Laplace expansion of the permanent along row 0.** -/
theorem permanent_succ_row_zero {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    A.permanent = ∑ j : Fin (n + 1), A 0 j * (A.submatrix Fin.succ j.succAbove).permanent := by
  rw [← permanent_transpose A, permanent_succ_column_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← permanent_transpose]
  simp only [transpose_apply, transpose_submatrix, transpose_transpose]

end Matrix

/-! ### Arithmetic circuits, `PITℤ` and permanent self-reducibility -/

namespace Cslib.Circuits

open MvPolynomial

universe u

variable {K : Type u} [CommSemiring K] {n m : ℕ}

/-- Evaluating the formal polynomial computed by an arithmetic circuit at `x : Fin n → K` agrees
with evaluating the circuit under `arithInterpretation K`. -/
@[simp] theorem Circuit.eval_polynomial (c : Circuit (arithSignature K) n m) (x : Fin n → K)
    (j : Fin m) :
    MvPolynomial.eval x (c.polynomial j) = c.eval (arithInterpretation K) x j := by
  simpa [MvPolynomial.aeval_def, MvPolynomial.eval₂_id, arithInterpretation] using
    c.aeval_polynomial x j

namespace Arithmetic

open Finset Turing.MultiTapeTM

/-! #### Encoding of integer arithmetic circuits and `PITInt` -/

/-- Encoding of an operation of `arithSignature ℤ`: `.add` is `[false, false]`, `.mul` is
`[false, true]`, and `.const z` is `true :: encIntBin z`. -/
def encArithOpInt : ArithOp ℤ ↪ List Bool where
  toFun
    | .add => [false, false]
    | .mul => [false, true]
    | .const z => true :: encIntBin z
  inj' a b h := by
    cases a <;> cases b <;>
      simp only [List.cons.injEq, true_and, Bool.false_eq_true, Bool.true_eq_false, false_and] at h
    · rfl
    · rfl
    · exact congrArg ArithOp.const (encIntBin.injective h)

/-- Encoding of a gate of an integer arithmetic circuit: its operation paired with the list of its
argument wire codes in binary. -/
def encArithGateInt : ArithOp ℤ × List ℕ ↪ List Bool :=
  encPair encArithOpInt (encList encNat)

/-- Encoding of the code of an integer arithmetic circuit: the list of gates paired with the list
of designated output wire codes. -/
def encArithCodeInt : List (ArithOp ℤ × List ℕ) × List ℕ ↪ List Bool :=
  encPair (encList encArithGateInt) (encList encNat)

/-- Encoding of a single-output integer arithmetic circuit bundled with its input arity: the input
arity in unary paired with the circuit code. -/
def encArithCircuitInt : (Σ n, Circuit (arithSignature ℤ) n 1) ↪ List Bool where
  toFun c := encPair encUnary encArithCodeInt (c.1, c.2.code)
  inj' := by
    rintro ⟨n₁, c₁⟩ ⟨n₂, c₂⟩ h
    obtain ⟨rfl, hcode⟩ := Prod.mk.inj ((encPair encUnary encArithCodeInt).injective h)
    exact Sigma.mk.inj_iff.mpr ⟨rfl, heq_of_eq (Circuit.code_injective hcode)⟩

@[simp] theorem encArithCircuitInt_apply (c : Σ n, Circuit (arithSignature ℤ) n 1) :
    encArithCircuitInt c = encPair encUnary encArithCodeInt (c.1, c.2.code) := rfl

/-- The encoded length of a bundled integer arithmetic circuit is at least its number of input
variables. -/
theorem le_length_encArithCircuitInt (c : Σ n, Circuit (arithSignature ℤ) n 1) :
    c.1 ≤ (encArithCircuitInt c).length := by
  simpa [encArithCircuitInt] using length_le_encPair_left encUnary encArithCodeInt (c.1, c.2.code)

/-- **Polynomial Identity Testing (`PITInt`)**: the single-output arithmetic circuits over `ℤ` whose
designated output computes the zero formal polynomial. -/
def PITInt : Set (Σ n, Circuit (arithSignature ℤ) n 1) :=
  { c | c.2.polynomial 0 = 0 }

@[simp] theorem mem_PITInt_iff {c : Σ n, Circuit (arithSignature ℤ) n 1} :
    c ∈ PITInt ↔ c.2.polynomial 0 = 0 := Iff.rfl

/-- **Schwartz–Zippel root bound for arithmetic circuits**: if `⟨n, c⟩ ∉ PITInt`, the circuit
evaluates to zero at at most `(c.polynomial 0).totalDegree * #S ^ (n - 1)` points of `S ^ n`. -/
theorem card_roots_eval_le_of_notMem_PITInt {n : ℕ} {c : Circuit (arithSignature ℤ) n 1}
    (hc : (⟨n, c⟩ : Σ m, Circuit (arithSignature ℤ) m 1) ∉ PITInt) (S : Finset ℤ) :
    #(Fintype.piFinset (fun _ : Fin n => S) |>.filter
        (fun x => c.eval (arithInterpretation ℤ) x 0 = 0)) ≤
      (c.polynomial 0).totalDegree * S.card ^ (n - 1) := by
  simpa only [Circuit.eval_polynomial] using MvPolynomial.card_roots_le hc S

/-- **Schwartz–Zippel hitting property for arithmetic circuits**: if `⟨n, c⟩ ∉ PITInt` and
`(c.polynomial 0).totalDegree < #S`, then `c` evaluates to a nonzero integer at some point of
`S ^ n`. -/
theorem exists_eval_ne_zero_of_notMem_PITInt {n : ℕ} {c : Circuit (arithSignature ℤ) n 1}
    (hc : (⟨n, c⟩ : Σ m, Circuit (arithSignature ℤ) m 1) ∉ PITInt) {S : Finset ℤ}
    (hdeg : (c.polynomial 0).totalDegree < S.card) :
    ∃ x : Fin n → ℤ, (∀ i, x i ∈ S) ∧ c.eval (arithInterpretation ℤ) x 0 ≠ 0 := by
  obtain ⟨x, hxS, hx0⟩ := MvPolynomial.exists_eval_ne_zero_of_totalDegree_lt_card hc hdeg
  exact ⟨x, hxS, by rwa [← c.eval_polynomial x 0]⟩

/-! #### Constructive arithmetic circuit combinators -/

section Combinators

variable {R : Type u} [CommRing R]

/-- The 1-gate arithmetic circuit computing the constant `a`. -/
def constCircuit (a : R) : Circuit (arithSignature R) n 1 :=
  Circuit.oneGate (.const a) Fin.elim0

omit [CommRing R] in
@[simp] theorem size_constCircuit (a : R) : (constCircuit (n := n) a).size = 1 := rfl

@[simp] theorem polynomial_constCircuit (a : R) :
    (constCircuit (n := n) a).polynomial 0 = C a := rfl

/-- The 0-gate arithmetic circuit reading input variable `i`. -/
def varCircuit (i : Fin n) : Circuit (arithSignature R) n 1 :=
  Circuit.wiring (arithSignature R) fun _ => i

omit [CommRing R] in
@[simp] theorem size_varCircuit (i : Fin n) : (varCircuit (R := R) i).size = 0 := rfl

@[simp] theorem polynomial_varCircuit (i : Fin n) :
    (varCircuit (R := R) i).polynomial 0 = X i := rfl

/-- The arithmetic circuit adding the outputs of `c₁` and `c₂`. -/
def addCircuit (c₁ c₂ : Circuit (arithSignature R) n 1) : Circuit (arithSignature R) n 1 :=
  (Circuit.oneGate (σ := arithSignature R) .add ![0, 1]).comp (c₁.append c₂)

omit [CommRing R] in
@[simp] theorem size_addCircuit (c₁ c₂ : Circuit (arithSignature R) n 1) :
    (addCircuit c₁ c₂).size = c₁.size + c₂.size + 1 := rfl

@[simp] theorem polynomial_addCircuit (c₁ c₂ : Circuit (arithSignature R) n 1) :
    (addCircuit c₁ c₂).polynomial 0 = c₁.polynomial 0 + c₂.polynomial 0 := by
  simp only [addCircuit, Circuit.polynomial, Circuit.eval_comp, Circuit.eval_append,
    Circuit.eval_oneGate, arithInterpretationWith, Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

/-- The arithmetic circuit multiplying the outputs of `c₁` and `c₂`. -/
def mulCircuit (c₁ c₂ : Circuit (arithSignature R) n 1) : Circuit (arithSignature R) n 1 :=
  (Circuit.oneGate (σ := arithSignature R) .mul ![0, 1]).comp (c₁.append c₂)

omit [CommRing R] in
@[simp] theorem size_mulCircuit (c₁ c₂ : Circuit (arithSignature R) n 1) :
    (mulCircuit c₁ c₂).size = c₁.size + c₂.size + 1 := rfl

@[simp] theorem polynomial_mulCircuit (c₁ c₂ : Circuit (arithSignature R) n 1) :
    (mulCircuit c₁ c₂).polynomial 0 = c₁.polynomial 0 * c₂.polynomial 0 := by
  simp only [mulCircuit, Circuit.polynomial, Circuit.eval_comp, Circuit.eval_append,
    Circuit.eval_oneGate, arithInterpretationWith, Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

/-- The arithmetic circuit negating `c` by multiplying by `-1`. -/
def negCircuit (c : Circuit (arithSignature R) n 1) : Circuit (arithSignature R) n 1 :=
  mulCircuit (constCircuit (-1)) c

@[simp] theorem size_negCircuit (c : Circuit (arithSignature R) n 1) :
    (negCircuit c).size = 1 + c.size + 1 := rfl

@[simp] theorem polynomial_negCircuit (c : Circuit (arithSignature R) n 1) :
    (negCircuit c).polynomial 0 = -c.polynomial 0 := by
  simp [negCircuit]

/-- The arithmetic circuit subtracting `c₂` from `c₁`. -/
def subCircuit (c₁ c₂ : Circuit (arithSignature R) n 1) : Circuit (arithSignature R) n 1 :=
  addCircuit c₁ (negCircuit c₂)

@[simp] theorem size_subCircuit (c₁ c₂ : Circuit (arithSignature R) n 1) :
    (subCircuit c₁ c₂).size = c₁.size + (1 + c₂.size + 1) + 1 := rfl

@[simp] theorem polynomial_subCircuit (c₁ c₂ : Circuit (arithSignature R) n 1) :
    (subCircuit c₁ c₂).polynomial 0 = c₁.polynomial 0 - c₂.polynomial 0 := by
  simp [subCircuit, sub_eq_add_neg]

/-- Reindex the input variables of an arithmetic circuit along `ρ : Fin m → Fin n` with zero
additional gates. -/
def reindexCircuit (ρ : Fin m → Fin n) (c : Circuit (arithSignature R) m 1) :
    Circuit (arithSignature R) n 1 :=
  c.comp (Circuit.wiring (arithSignature R) ρ)

omit [CommRing R] in
@[simp] theorem size_reindexCircuit (ρ : Fin m → Fin n) (c : Circuit (arithSignature R) m 1) :
    (reindexCircuit ρ c).size = c.size :=
  Nat.zero_add c.size

@[simp] theorem polynomial_reindexCircuit (ρ : Fin m → Fin n)
    (c : Circuit (arithSignature R) m 1) :
    (reindexCircuit ρ c).polynomial 0 = MvPolynomial.rename ρ (c.polynomial 0) := by
  have hrename : MvPolynomial.rename ρ = aeval (X ∘ ρ : Fin m → MvPolynomial (Fin n) R) :=
    MvPolynomial.algHom_ext fun i => by simp
  rw [hrename, c.aeval_polynomial_mvPolynomial (X ∘ ρ) 0,
    reindexCircuit, Circuit.polynomial, Circuit.eval_comp, Circuit.eval_wiring]

/-- Sum a finite family of single-output arithmetic circuits. -/
def finSumCircuit : {k : ℕ} → (Fin k → Circuit (arithSignature R) n 1) →
    Circuit (arithSignature R) n 1
  | 0, _ => constCircuit 0
  | k + 1, cs => addCircuit (finSumCircuit fun j => cs j.castSucc) (cs (Fin.last k))

@[simp] theorem size_finSumCircuit :
    {k : ℕ} → (cs : Fin k → Circuit (arithSignature R) n 1) →
      (finSumCircuit cs).size = 1 + ∑ j : Fin k, ((cs j).size + 1)
  | 0, _ => by simp [finSumCircuit]
  | k + 1, cs => by
    rw [finSumCircuit, size_addCircuit, size_finSumCircuit, Fin.sum_univ_castSucc]
    omega

@[simp] theorem polynomial_finSumCircuit :
    {k : ℕ} → (cs : Fin k → Circuit (arithSignature R) n 1) →
      (finSumCircuit cs).polynomial 0 = ∑ j : Fin k, (cs j).polynomial 0
  | 0, _ => by simp [finSumCircuit]
  | k + 1, cs => by
    rw [finSumCircuit, polynomial_addCircuit, polynomial_finSumCircuit, Fin.sum_univ_castSucc]

end Combinators

/-- Two integer arithmetic circuits compute the same formal polynomial if and only if their
difference circuit `subCircuit c₁ c₂` belongs to `PITInt`. -/
theorem mem_PITInt_subCircuit_iff {n : ℕ} (c₁ c₂ : Circuit (arithSignature ℤ) n 1) :
    (⟨n, subCircuit c₁ c₂⟩ : Σ m, Circuit (arithSignature ℤ) m 1) ∈ PITInt ↔
      c₁.polynomial 0 = c₂.polynomial 0 := by
  rw [mem_PITInt_iff, polynomial_subCircuit, sub_eq_zero]

/-! #### The permanent family and Laplace self-reducibility via `PITInt` -/

section Permanent

variable {R : Type u} [CommRing R]

/-- The generic permanent has total degree at most `n`. -/
theorem totalDegree_permanent_genericMatrix_le (n : ℕ) :
    (genericMatrix R n).permanent.totalDegree ≤ n := by
  rw [Matrix.permanent]
  refine totalDegree_finsetSum_le fun σ _ => ?_
  refine (totalDegree_finsetProd _ _).trans ?_
  calc _ ≤ ∑ _i : Fin n, 1 :=
        Finset.sum_le_sum fun i _ => (totalDegree_monomial_le _ _).trans (by simp)
    _ = n := by simp

/-- The permanent family over `R`: its `n`-th member is the permanent of `genericMatrix R n`, a
polynomial in `n * n` variables. -/
noncomputable def permFamily (R : Type u) [CommSemiring R] : PolynomialFamily R where
  vars n := n * n
  poly n := (genericMatrix R n).permanent

/-- The permanent family over `R` is a p-family (`vars n = n ^ 2` and `totalDegree ≤ n`). -/
theorem isPFamily_permFamily : (permFamily R).IsPFamily :=
  ⟨PolynomiallyBounded.id.mul PolynomiallyBounded.id,
    PolynomiallyBounded.id.mono_of_le (totalDegree_permanent_genericMatrix_le (R := R))⟩

/-- The permanent family over `ℤ`: its `n`-th member is the permanent of `genericMatrix ℤ n`, a
polynomial in `n * n` variables. -/
noncomputable abbrev intPermFamily : PolynomialFamily ℤ :=
  permFamily ℤ

/-- The integer permanent family is a p-family (`vars n = n ^ 2` and `totalDegree ≤ n`). -/
theorem isPFamily_intPermFamily : intPermFamily.IsPFamily :=
  isPFamily_permFamily

/-- Reindexing map sending the `(i, k)` variable of an `m × m` matrix to the
`(i.succ, j.succAbove k)` variable of an `(m + 1) × (m + 1)` matrix (the `(0, j)`-minor). -/
def minorVar {m : ℕ} (j : Fin (m + 1)) (idx : Fin (m * m)) : Fin ((m + 1) * (m + 1)) :=
  let pq := finProdFinEquiv.symm idx
  finProdFinEquiv (pq.1.succ, j.succAbove pq.2)

/-- The `(0, j)`-submatrix of `genericMatrix R (m + 1)` is `genericMatrix R m` with variables
renamed along `minorVar j`. -/
theorem submatrix_genericMatrix_eq_map_rename {m : ℕ} (j : Fin (m + 1)) :
    (genericMatrix R (m + 1)).submatrix Fin.succ j.succAbove =
      (genericMatrix R m).map (MvPolynomial.rename (minorVar j)) := by
  ext i k
  simp [genericMatrix, minorVar]

/-- The permanent of the `(0, j)`-minor of `genericMatrix R (m + 1)` is the generic `m × m`
permanent with variables renamed along `minorVar j`. -/
theorem permanent_submatrix_genericMatrix {m : ℕ} (j : Fin (m + 1)) :
    ((genericMatrix R (m + 1)).submatrix Fin.succ j.succAbove).permanent =
      MvPolynomial.rename (minorVar j) (genericMatrix R m).permanent := by
  rw [submatrix_genericMatrix_eq_map_rename, Matrix.permanent, Matrix.permanent, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_prod]
  rfl

/-- The permanent of the `0 × 0` generic matrix is `1`. -/
@[simp] theorem permanent_genericMatrix_zero : (genericMatrix R 0).permanent = 1 :=
  Matrix.permanent_isEmpty

/-- **Laplace recurrence for the generic permanent polynomial**: the `(m + 1) × (m + 1)` generic
permanent expands along row 0 in terms of the `m × m` generic permanent renamed along `minorVar j`.
-/
theorem permanent_genericMatrix_succ (m : ℕ) :
    (genericMatrix R (m + 1)).permanent =
      ∑ j : Fin (m + 1),
        X (finProdFinEquiv (0, j)) *
          MvPolynomial.rename (minorVar j) (genericMatrix R m).permanent := by
  rw [Matrix.permanent_succ_row_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [permanent_submatrix_genericMatrix]
  rfl

/-- Base-case identity-test circuit for the `0 × 0` permanent: computes `c₀.polynomial 0 - 1`. -/
def permBaseDiff (c₀ : Circuit (arithSignature R) 0 1) : Circuit (arithSignature R) 0 1 :=
  subCircuit c₀ (constCircuit 1)

@[simp] theorem size_permBaseDiff (c₀ : Circuit (arithSignature R) 0 1) :
    (permBaseDiff c₀).size = c₀.size + 4 := by
  simp [permBaseDiff]

@[simp] theorem polynomial_permBaseDiff (c₀ : Circuit (arithSignature R) 0 1) :
    (permBaseDiff c₀).polynomial 0 = c₀.polynomial 0 - 1 := by
  simp [permBaseDiff]

/-- Inductive Laplace step identity-test circuit for the `(m + 1) × (m + 1)` permanent from a
candidate `m × m` permanent circuit `cm` and a candidate `(m + 1) × (m + 1)` permanent circuit
`cm1`: computes
`cm1.polynomial 0 - ∑ j : Fin (m + 1), X (0, j) * rename (minorVar j) (cm.polynomial 0)`. -/
def permStepDiff (m : ℕ) (cm : Circuit (arithSignature R) (m * m) 1)
    (cm1 : Circuit (arithSignature R) ((m + 1) * (m + 1)) 1) :
    Circuit (arithSignature R) ((m + 1) * (m + 1)) 1 :=
  subCircuit cm1 (finSumCircuit fun j : Fin (m + 1) =>
    mulCircuit (varCircuit (finProdFinEquiv (0, j))) (reindexCircuit (minorVar j) cm))

@[simp] theorem size_permStepDiff (m : ℕ) (cm : Circuit (arithSignature R) (m * m) 1)
    (cm1 : Circuit (arithSignature R) ((m + 1) * (m + 1)) 1) :
    (permStepDiff m cm cm1).size = cm1.size + (m + 1) * (cm.size + 2) + 4 := by
  simp only [permStepDiff, size_subCircuit, size_finSumCircuit, size_mulCircuit, size_varCircuit,
    size_reindexCircuit, zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  ring

@[simp] theorem polynomial_permStepDiff (m : ℕ) (cm : Circuit (arithSignature R) (m * m) 1)
    (cm1 : Circuit (arithSignature R) ((m + 1) * (m + 1)) 1) :
    (permStepDiff m cm cm1).polynomial 0 =
      cm1.polynomial 0 -
        ∑ j : Fin (m + 1),
          X (finProdFinEquiv (0, j)) * MvPolynomial.rename (minorVar j) (cm.polynomial 0) := by
  simp [permStepDiff]

/-- `permBaseDiff c₀` lies in `PITInt` if and only if `c₀` computes the `0 × 0` generic permanent.
-/
theorem mem_PITInt_permBaseDiff_iff (c₀ : Circuit (arithSignature ℤ) 0 1) :
    (⟨0, permBaseDiff c₀⟩ : Σ n, Circuit (arithSignature ℤ) n 1) ∈ PITInt ↔
      c₀.polynomial 0 = (genericMatrix ℤ 0).permanent := by
  rw [mem_PITInt_iff, polynomial_permBaseDiff, permanent_genericMatrix_zero, sub_eq_zero]

/-- Given that `cm` computes the `m × m` generic permanent, `permStepDiff m cm cm1` lies in `PITInt`
if and only if `cm1` computes the `(m + 1) × (m + 1)` generic permanent. -/
theorem mem_PITInt_permStepDiff_iff {m : ℕ} {cm : Circuit (arithSignature ℤ) (m * m) 1}
    (hcm : cm.polynomial 0 = (genericMatrix ℤ m).permanent)
    (cm1 : Circuit (arithSignature ℤ) ((m + 1) * (m + 1)) 1) :
    (⟨(m + 1) * (m + 1), permStepDiff m cm cm1⟩ :
        Σ n, Circuit (arithSignature ℤ) n 1) ∈ PITInt ↔
      cm1.polynomial 0 = (genericMatrix ℤ (m + 1)).permanent := by
  rw [mem_PITInt_iff, polynomial_permStepDiff, hcm, ← permanent_genericMatrix_succ, sub_eq_zero]

/-- **Downward self-reducibility of the permanent to `PITInt`**
([Kabanets and Impagliazzo, Lemma 4.2][KabanetsImpagliazzo2004];
[Arora and Barak, Theorem 20.16][AroraBarak09]): a family of arithmetic circuits
`C : ∀ m, Circuit (arithSignature ℤ) (m * m) 1` computes `(genericMatrix ℤ m).permanent` for every
`m ≤ n` if and only if `permBaseDiff (C 0)` and `permStepDiff m (C m) (C (m + 1))` for all `m < n`
belong to `PITInt`. -/
theorem forall_polynomial_eq_permanent_iff_mem_PITInt
    (C : ∀ m, Circuit (arithSignature ℤ) (m * m) 1) (n : ℕ) :
    (∀ m ≤ n, (C m).polynomial 0 = (genericMatrix ℤ m).permanent) ↔
      (⟨0, permBaseDiff (C 0)⟩ : Σ k, Circuit (arithSignature ℤ) k 1) ∈ PITInt ∧
        ∀ m < n,
          (⟨(m + 1) * (m + 1), permStepDiff m (C m) (C (m + 1))⟩ :
            Σ k, Circuit (arithSignature ℤ) k 1) ∈ PITInt := by
  induction n with
  | zero =>
    rw [mem_PITInt_permBaseDiff_iff]
    simp
  | succ n ih =>
    constructor
    · intro h
      have hn : ∀ m ≤ n, (C m).polynomial 0 = (genericMatrix ℤ m).permanent :=
        fun m hm => h m (Nat.le_succ_of_le hm)
      obtain ⟨h0, hstep⟩ := (ih).mp hn
      refine ⟨h0, fun m hm => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | rfl
      · exact hstep m hlt
      · exact (mem_PITInt_permStepDiff_iff (h m (Nat.le_succ m)) (C (m + 1))).mpr
          (h (m + 1) le_rfl)
    · rintro ⟨h0, hstep⟩
      have hn : ∀ m ≤ n, (C m).polynomial 0 = (genericMatrix ℤ m).permanent :=
        (ih).mpr ⟨h0, fun m hm => hstep m (Nat.lt_succ_of_lt hm)⟩
      intro m hm
      rcases Nat.le_iff_lt_or_eq.mp hm with hlt | rfl
      · exact hn m (Nat.le_of_lt_succ hlt)
      · exact (mem_PITInt_permStepDiff_iff (hn n le_rfl) (C (n + 1))).mp
          (hstep n (Nat.lt_succ_self n))

/-- A family of integer arithmetic circuits `C : ∀ m, Circuit (arithSignature ℤ) (m * m) 1` forms a
*Laplace permanent chain* up to dimension `n` when its base circuit `C 0` and its consecutive pairs
`(C m, C (m + 1))` for `m < n` satisfy the `PITInt` identities `permBaseDiff` and `permStepDiff`
([Kabanets and Impagliazzo, Lemma 4.2][KabanetsImpagliazzo2004]). -/
structure IsLaplacePermChain (C : ∀ m, Circuit (arithSignature ℤ) (m * m) 1) (n : ℕ) : Prop where
  /-- The `0 × 0` circuit satisfies `permBaseDiff (C 0) ∈ PITInt`. -/
  base_mem : (⟨0, permBaseDiff (C 0)⟩ : Σ k, Circuit (arithSignature ℤ) k 1) ∈ PITInt
  /-- Every step `m < n` satisfies `permStepDiff m (C m) (C (m + 1)) ∈ PITInt`. -/
  step_mem : ∀ m < n,
    (⟨(m + 1) * (m + 1), permStepDiff m (C m) (C (m + 1))⟩ :
      Σ k, Circuit (arithSignature ℤ) k 1) ∈ PITInt

/-- A candidate integer arithmetic circuit family `C` computes `(genericMatrix ℤ m).permanent` for
all `m ≤ n` if and only if `IsLaplacePermChain C n` holds. -/
theorem forall_polynomial_eq_permanent_iff_isLaplacePermChain
    (C : ∀ m, Circuit (arithSignature ℤ) (m * m) 1) (n : ℕ) :
    (∀ m ≤ n, (C m).polynomial 0 = (genericMatrix ℤ m).permanent) ↔
      IsLaplacePermChain C n := by
  rw [forall_polynomial_eq_permanent_iff_mem_PITInt]
  exact ⟨fun ⟨h0, hs⟩ => ⟨h0, hs⟩, fun ⟨h0, hs⟩ => ⟨h0, hs⟩⟩

/-- Explicit arithmetic circuit family computing the `m × m` generic permanent by recursive Laplace
expansion along row 0. Its gate count grows factorially, witnessing unconditionally that the
Laplace `PITInt` identities `permBaseDiff` and `permStepDiff` are satisfiable at every dimension
`m`. -/
def laplacePermCircuit : ∀ m : ℕ, Circuit (arithSignature R) (m * m) 1
  | 0 => constCircuit 1
  | m + 1 =>
    finSumCircuit fun j : Fin (m + 1) =>
      mulCircuit (varCircuit (finProdFinEquiv (0, j)))
        (reindexCircuit (minorVar j) (laplacePermCircuit m))

@[simp] theorem polynomial_laplacePermCircuit :
    ∀ m : ℕ, (laplacePermCircuit (R := R) m).polynomial 0 = (genericMatrix R m).permanent
  | 0 => by
    rw [laplacePermCircuit, polynomial_constCircuit, map_one, permanent_genericMatrix_zero]
  | m + 1 => by
    rw [laplacePermCircuit, polynomial_finSumCircuit, permanent_genericMatrix_succ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [polynomial_mulCircuit, polynomial_varCircuit, polynomial_reindexCircuit,
      polynomial_laplacePermCircuit m]

/-- `laplacePermCircuit` forms a valid Laplace permanent chain up to every dimension `n`. -/
theorem isLaplacePermChain_laplacePermCircuit (n : ℕ) :
    IsLaplacePermChain (laplacePermCircuit (R := ℤ)) n :=
  (forall_polynomial_eq_permanent_iff_isLaplacePermChain _ n).mp
    fun m _ => polynomial_laplacePermCircuit m

end Permanent

/-! #### Certified permanent circuit families from `PITInt ∈ P` and `intPermFamily ∈ VP ℤ` -/

/-- Existence of a polynomial-time `PITInt` certification package for the integer permanent: a
polynomial-time decider `decidePIT` for `PITInt` together with a polynomially bounded arithmetic
circuit family `C` whose Laplace expansion identities `permBaseDiff` and `permStepDiff` are accepted
by `decidePIT`, and such that any candidate family `C'` accepted by `decidePIT` on those identities
up to dimension `n` computes `(genericMatrix ℤ m).permanent` for all `m ≤ n`. -/
structure PermPITCertified : Prop where
  /-- Existence of a polynomial-time decider and certified polynomially bounded circuit family. -/
  exists_tester :
    ∃ (decidePIT : (Σ n, Circuit (arithSignature ℤ) n 1) → Bool)
      (C : ∀ m, Circuit (arithSignature ℤ) (m * m) 1),
      ComputableTidilyInPolyTime decidePIT encArithCircuitInt encBool ∧
      PolynomiallyBounded (fun m => (C m).size) ∧
      PolynomiallyBounded (fun m => (permStepDiff m (C m) (C (m + 1))).size) ∧
      (∀ c, c ∈ PITInt ↔ decidePIT c = true) ∧
      decidePIT ⟨0, permBaseDiff (C 0)⟩ = true ∧
      (∀ m, decidePIT ⟨(m + 1) * (m + 1), permStepDiff m (C m) (C (m + 1))⟩ = true) ∧
      ∀ (C' : ∀ m, Circuit (arithSignature ℤ) (m * m) 1) (n : ℕ),
        (∀ m ≤ n, (C' m).polynomial 0 = (genericMatrix ℤ m).permanent) ↔
          decidePIT ⟨0, permBaseDiff (C' 0)⟩ = true ∧
            ∀ m < n, decidePIT ⟨(m + 1) * (m + 1), permStepDiff m (C' m) (C' (m + 1))⟩ = true

/-- **If `PITInt ∈ P` and `intPermFamily ∈ VP ℤ`, then the integer permanent has a polynomial-time
PIT-certified circuit family** (`PermPITCertified`)
[Kabanets and Impagliazzo, Lemma 4.2][KabanetsImpagliazzo2004]. -/
theorem exists_certified_perm_family_of_PITInt_mem_P_of_mem_VP
    (hPIT : PITInt ∈ Cslib.Complexity.P encArithCircuitInt) (hPerm : intPermFamily ∈ VP ℤ) :
    PermPITCertified := by
  obtain ⟨decidePIT, hdec_poly, hdec_iff⟩ := hPIT
  obtain ⟨_, C, hC_size, hC_poly⟩ := hPerm
  change ∀ m, Circuit (arithSignature ℤ) (m * m) 1 at C
  change ∀ m, (C m).polynomial 0 = (genericMatrix ℤ m).permanent at hC_poly
  have hstep_size : PolynomiallyBounded (fun m => (permStepDiff m (C m) (C (m + 1))).size) := by
    have hC1 : PolynomiallyBounded (fun m => (C (m + 1)).size) :=
      hC_size.comp (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))
    have hmul : PolynomiallyBounded
        (fun m => (C (m + 1)).size + (m + 1) * ((C m).size + 2) + 4) := by
      fun_prop
    exact hmul.mono_of_le fun m => (size_permStepDiff m (C m) (C (m + 1))).le
  have hsound (C' : ∀ m, Circuit (arithSignature ℤ) (m * m) 1) (n : ℕ) :
      (∀ m ≤ n, (C' m).polynomial 0 = (genericMatrix ℤ m).permanent) ↔
        decidePIT ⟨0, permBaseDiff (C' 0)⟩ = true ∧
          ∀ m < n, decidePIT ⟨(m + 1) * (m + 1), permStepDiff m (C' m) (C' (m + 1))⟩ = true := by
    rw [forall_polynomial_eq_permanent_iff_mem_PITInt]
    simp only [hdec_iff]
  have hC_all (n : ℕ) : ∀ m ≤ n, (C m).polynomial 0 = (genericMatrix ℤ m).permanent :=
    fun m _ => hC_poly m
  have hC0 : decidePIT ⟨0, permBaseDiff (C 0)⟩ = true :=
    ((hsound C 0).mp (hC_all 0)).1
  have hCm (m : ℕ) : decidePIT ⟨(m + 1) * (m + 1), permStepDiff m (C m) (C (m + 1))⟩ = true :=
    ((hsound C (m + 1)).mp (hC_all (m + 1))).2 m (Nat.lt_succ_self m)
  exact ⟨⟨decidePIT, C, hdec_poly, hC_size, hstep_size, hdec_iff, hC0, hCm, hsound⟩⟩

end Arithmetic

end Cslib.Circuits

/-! ### `NEXP` circuit lower bounds and the Kabanets–Impagliazzo theorem -/

namespace Cslib.Complexity

open Turing.MultiTapeTM Circuits Circuits.Boolean

variable {α : Type} {enc : α ↪ List Bool}

/-- **Every level of the polynomial hierarchy lies in `EXP`**, via `Σₖ ⊆ PSPACE ⊆ EXP`. -/
theorem SigmaP_subset_EXP (k : ℕ) : SigmaP k enc ⊆ EXP enc :=
  (SigmaP_subset_PSPACE k).trans PSPACE_subset_EXP

/-- **Every level of the polynomial hierarchy lies in `NEXP`**, via `Σₖ ⊆ EXP ⊆ NEXP`. -/
theorem SigmaP_subset_NEXP (k : ℕ) : SigmaP k enc ⊆ NEXP enc :=
  (SigmaP_subset_EXP k).trans EXP_subset_NEXP

/-- If `NEXP` collapses into `Σₖ`, then `NEXP = EXP`. -/
theorem NEXP_eq_EXP_of_NEXP_subset_SigmaP {k : ℕ} (h : NEXP enc ⊆ SigmaP k enc) :
    NEXP enc = EXP enc :=
  Set.Subset.antisymm (h.trans (SigmaP_subset_EXP k)) EXP_subset_NEXP

/-- **Unconditional fixed-exponent circuit lower bound in `NEXP`**: for every `k : ℕ`, some
language in `NEXP` (in fact in `Σ₂`) has no Boolean circuits of size `O(n ^ k)`
([Kannan][Kannan1982]). -/
theorem exists_mem_NEXP_notMem_SIZE (k : ℕ) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits ∧
      ∀ c, L ∉ SIZE fun n => c * (n + 1) ^ k := by
  obtain ⟨L, hL₂, hLsize⟩ := exists_mem_SigmaP_two_notMem_SIZE k
  exact ⟨L, SigmaP_subset_NEXP 2 hL₂, hLsize⟩

end Cslib.Complexity

namespace Cslib.Circuits.Arithmetic

open Turing.MultiTapeTM Cslib.Complexity Cslib.Circuits.Boolean

/-- **The Kabanets–Impagliazzo derandomization-to-lower-bounds theorem**
([Kabanets and Impagliazzo, Theorem 4.1][KabanetsImpagliazzo2004];
[Arora and Barak, Theorem 20.16][AroraBarak09]): if Polynomial Identity Testing over `ℤ` is in `P`
(`PITInt ∈ P encArithCircuitInt`), then under the Impagliazzo–Kabanets–Wigderson / Valiant–Toda
collapse (stating that if `NEXP ⊆ P/poly` and `PermPITCertified` holds, then `Σ₂` has Boolean
circuits of some fixed polynomial degree `O(n ^ k)`), either `NEXP ⊄ P/poly` or the integer
permanent family `intPermFamily` is not in `VP ℤ`.

The downward self-reducibility of the permanent to `PITInt`
(`forall_polynomial_eq_permanent_iff_mem_PITInt` and
`exists_certified_perm_family_of_PITInt_mem_P_of_mem_VP`) and the `Σ₂` fixed-degree circuit lower
bound (`exists_mem_SigmaP_two_notMem_SIZE`) are proved unconditionally; `hCollapse` supplies the
external collapse from `NEXP ⊆ P/poly` and the PIT-certified permanent circuit family. -/
theorem kabanets_impagliazzo
    (hPIT : PITInt ∈ Cslib.Complexity.P encArithCircuitInt)
    (hCollapse :
      (∀ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits → L ∈ PPoly) →
      PermPITCertified →
      ∃ k : ℕ, ∀ L : Language Bool,
        (L : Set (List Bool)) ∈ SigmaP 2 encBits → ∃ c, L ∈ SIZE fun n => c * (n + 1) ^ k) :
    (∃ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits ∧ L ∉ PPoly) ∨
      intPermFamily ∉ VP ℤ := by
  by_cases hNEXP : ∃ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits ∧ L ∉ PPoly
  · exact Or.inl hNEXP
  · refine Or.inr fun hPerm => ?_
    push Not at hNEXP
    have hCert : PermPITCertified :=
      exists_certified_perm_family_of_PITInt_mem_P_of_mem_VP hPIT hPerm
    obtain ⟨k, hSigmaSize⟩ := hCollapse hNEXP hCert
    obtain ⟨L, hL₂, hLnot⟩ := exists_mem_SigmaP_two_notMem_SIZE k
    obtain ⟨c, hc⟩ := hSigmaSize L hL₂
    exact hLnot c hc

/-- **The Kabanets–Impagliazzo theorem via time-hierarchy collapse (`EXP ⊆ P`)**
([Kabanets and Impagliazzo, Theorem 4.1][KabanetsImpagliazzo2004];
[Arora and Barak, Theorem 20.16][AroraBarak09]): if `PITInt ∈ P encArithCircuitInt`, then under the
collapse from `NEXP ⊆ P/poly` and `PermPITCertified` to `EXP ⊆ P`, either `NEXP ⊄ P/poly` or
`intPermFamily ∉ VP ℤ`, refuting `EXP ⊆ P` by the time hierarchy theorem (`P_ssubset_EXP`). -/
theorem kabanets_impagliazzo_of_EXP_subset_P
    (hPIT : PITInt ∈ Cslib.Complexity.P encArithCircuitInt)
    (hCollapse :
      (∀ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits → L ∈ PPoly) →
      PermPITCertified →
      EXP encBits ⊆ Cslib.Complexity.P encBits) :
    (∃ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits ∧ L ∉ PPoly) ∨
      intPermFamily ∉ VP ℤ := by
  by_cases hNEXP : ∃ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits ∧ L ∉ PPoly
  · exact Or.inl hNEXP
  · refine Or.inr fun hPerm => ?_
    push Not at hNEXP
    have hCert : PermPITCertified :=
      exists_certified_perm_family_of_PITInt_mem_P_of_mem_VP hPIT hPerm
    exact P_ssubset_EXP.not_subset (hCollapse hNEXP hCert)

end Cslib.Circuits.Arithmetic
