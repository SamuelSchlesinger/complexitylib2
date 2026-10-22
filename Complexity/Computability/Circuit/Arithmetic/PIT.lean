/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.Determinant
public import Complexity.Computability.Circuit.Boolean.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import Complexity.Init
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-!
# Polynomial identity testing (`PITInt`), Schwartz–Zippel, and arithmetic circuit combinators

*Polynomial identity testing* (`PIT`) asks whether a given arithmetic circuit computes the zero
formal polynomial. Over the integers, `Cslib.Circuits.Arithmetic.PITInt` is the set of pairs
`⟨n, c⟩ : Σ n, Circuit (arithSignature ℤ) n 1` with `c.polynomial 0 = 0` in
`MvPolynomial (Fin n) ℤ`, encoded as bit strings by `Cslib.Circuits.Arithmetic.encArithCircuitInt`
(number of inputs in unary, gate operations with binary integer constants via `encIntBin`, and
wire indices in binary).

This module establishes:

1. **The multivariate Schwartz–Zippel lemma** [Schwartz][Schwartz1980], [Zippel][Zippel1979],
   [DeMillo and Lipton][DeMilloLipton1978], [Arora and Barak, Lemma 7.22][AroraBarak09]: over any
   integral domain `R`, a nonzero polynomial `P : MvPolynomial (Fin n) R` of total degree `d` has
   at most `d * #S ^ (n - 1)` roots in `S ^ n` (`MvPolynomial.card_roots_le`), and if `d < #S`
   then `P` evaluates to a nonzero element at some point of `S ^ n`
   (`MvPolynomial.exists_eval_ne_zero_of_totalDegree_lt_card`), derived as natural-number
   cardinality corollaries of Mathlib's rational-bound theorem
   `MvPolynomial.schwartz_zippel_totalDegree`. Specializing to `c.polynomial 0` bounds the zero set
   of any arithmetic circuit outside `PITInt`
   (`Cslib.Circuits.Arithmetic.card_roots_eval_le_of_notMem_PITInt`,
   `Cslib.Circuits.Arithmetic.exists_eval_ne_zero_of_notMem_PITInt`).
2. **Constructive arithmetic circuit combinators** (`constCircuit`, `varCircuit`, `addCircuit`,
   `mulCircuit`, `negCircuit`, `subCircuit`, `reindexCircuit`, `finSumCircuit`) with exact gate-size
   and formal-polynomial evaluation lemmas, reducing circuit polynomial equivalence to membership
   of `subCircuit c₁ c₂` in `PITInt` (`mem_PITInt_subCircuit_iff`).

## Main definitions

* `Cslib.Circuits.Arithmetic.encArithOpInt`, `Cslib.Circuits.Arithmetic.encArithGateInt`,
  `Cslib.Circuits.Arithmetic.encArithCodeInt`, `Cslib.Circuits.Arithmetic.encArithCircuitInt`:
  injective bit-string encoding of single-output integer arithmetic circuits.
* `Cslib.Circuits.Arithmetic.PITInt`: the Polynomial Identity Testing problem over `ℤ`.
* `Cslib.Circuits.Arithmetic.constCircuit`, `varCircuit`, `addCircuit`, `mulCircuit`, `negCircuit`,
  `subCircuit`, `reindexCircuit`, `finSumCircuit`: constructive arithmetic circuit combinators.

## Main results

* `MvPolynomial.card_mul_card_roots_le`, `MvPolynomial.card_roots_le`,
  `MvPolynomial.exists_eval_ne_zero_of_totalDegree_lt_card`: natural-number cardinality and
  non-vanishing corollaries of Mathlib's `MvPolynomial.schwartz_zippel_totalDegree`.
* `Cslib.Circuits.Circuit.eval_polynomial`: evaluating `c.polynomial j` agrees with
  `c.eval (arithInterpretation K) x j`.
* `Cslib.Circuits.Arithmetic.card_roots_eval_le_of_notMem_PITInt`,
  `Cslib.Circuits.Arithmetic.exists_eval_ne_zero_of_notMem_PITInt`: Schwartz–Zippel zero bounds for
  arithmetic circuits outside `PITInt`.
* `Cslib.Circuits.Arithmetic.mem_PITInt_subCircuit_iff`: two integer arithmetic circuits compute the
  same formal polynomial iff `subCircuit c₁ c₂ ∈ PITInt`.

## References

* [J. T. Schwartz, *Fast probabilistic algorithms for verification of polynomial
  identities*][Schwartz1980]
* [R. Zippel, *Probabilistic algorithms for sparse polynomials*][Zippel1979]
* [R. A. DeMillo, R. J. Lipton, *A probabilistic remark on algebraic program
  testing*][DeMilloLipton1978]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Lemma 7.22][AroraBarak09]
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
by `#S` is at most `P.totalDegree * #S ^ n`. Derived by clearing denominators in Mathlib's
`MvPolynomial.schwartz_zippel_totalDegree`. -/
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

/-! ### Arithmetic circuits, `PITℤ`, and circuit combinators -/

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

end Arithmetic

end Cslib.Circuits
