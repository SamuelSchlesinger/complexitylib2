/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.PIT
public import Complexity.Computability.Circuit.Boolean.PPoly
public import Complexity.Computability.Complexity.Classes.EXP
public import Complexity.Computability.Complexity.Classes.Inclusions
public import Complexity.Computability.Complexity.Classes.PH
public import Complexity.Init
public import Mathlib.LinearAlgebra.Matrix.Permanent

import Complexity.Computability.Complexity.Classes.PH.Kannan
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Permanent self-reducibility to `PITInt` and fixed-degree circuit lower bounds in `NEXP`

Building on `Complexity.Computability.Circuit.Arithmetic.PIT` (`PITInt`, the multivariate
Schwartz–Zippel lemma, and constructive arithmetic circuit combinators), this module develops:

1. **Laplace cofactor expansion of the permanent and downward self-reducibility to `PITInt`**
   [Kabanets and Impagliazzo, Lemma 4.2][KabanetsImpagliazzo2004],
   [Arora and Barak, Theorem 20.16][AroraBarak09]: for any `(n + 1) × (n + 1)` matrix `A`,
   `A.permanent = ∑ j, A 0 j * (A.submatrix Fin.succ j.succAbove).permanent`
   (`Matrix.permanent_succ_row_zero`). On the generic matrix `genericMatrix R (m + 1)`, each minor
   is a variable reindexing of `genericMatrix R m` (`permanent_genericMatrix_succ`). Using explicit
   arithmetic circuit combinators, we construct the base test circuit `permBaseDiff` and the Laplace
   step test circuit `permStepDiff` with explicit polynomial gate-size bounds (`size_permBaseDiff`,
   `size_permStepDiff`). A candidate family `C : ∀ m, Circuit (arithSignature ℤ) (m * m) 1` computes
   `(genericMatrix ℤ m).permanent` for all `m ≤ n` if and only if
   `⟨0, permBaseDiff (C 0)⟩ ∈ PITInt` and
   `⟨(m + 1) * (m + 1), permStepDiff m (C m) (C (m + 1))⟩ ∈ PITInt` for all `m < n`
   (`forall_polynomial_eq_permanent_iff_mem_PITInt`).
   **Scope limitation:** this reduces permanent verification to `n + 1` instances of `PITInt` at the
   level of mathematical circuits, but does not formalize the polynomial-time Turing-machine
   construction of the encoded test circuits `permBaseDiff (C 0)` and
   `permStepDiff m (C m) (C (m + 1))` from encoded candidate circuits.

2. **Unconditional fixed-degree circuit lower bounds in `NEXP`**:
   combining Kannan's theorem (`exists_mem_SigmaP_two_notMem_SIZE`) with the inclusion
   `Σ₂ ⊆ PH ⊆ PSPACE ⊆ EXP ⊆ NEXP` (`SigmaP_subset_NEXP`) shows that for every fixed degree `k`,
   `NEXP` contains a language outside `SIZE (c (n + 1) ^ k)` (`exists_mem_NEXP_notMem_SIZE`).
   The Kabanets–Impagliazzo derandomization-to-lower-bounds theorem itself (which additionally
   requires Toda's theorem `P^#P ⊆ P^PH`, `#P`-completeness of the permanent, and the
   Impagliazzo–Kabanets–Wigderson easy-witness collapse `NEXP ⊆ P/poly ⇒ NEXP = MA`) is not
   formalized here.

## Main definitions

* `Cslib.Circuits.Arithmetic.permFamily`, `Cslib.Circuits.Arithmetic.intPermFamily`: the permanent
  family `n ↦ (genericMatrix R n).permanent` and its integer specialization.
* `Cslib.Circuits.Arithmetic.minorVar`, `permBaseDiff`, `permStepDiff`, `laplacePermCircuit`,
  `IsLaplacePermChain`: the Laplace cofactor difference circuits, explicit recursive permanent
  circuit family, and Laplace permanent chain predicate reducing permanent verification to `PITInt`.

## Main results

* `Matrix.permanent_succ_column_zero`, `Matrix.permanent_succ_row_zero`: Laplace cofactor expansion
  of the permanent along column 0 and row 0.
* `Cslib.Circuits.Arithmetic.permanent_genericMatrix_zero`,
  `Cslib.Circuits.Arithmetic.permanent_genericMatrix_succ`: Laplace recurrence for the generic
  permanent polynomial.
* `Cslib.Circuits.Arithmetic.forall_polynomial_eq_permanent_iff_mem_PITInt`: Kabanets–Impagliazzo
  Lemma 4.2, characterizing permanent circuits up to dimension `n` via `n + 1` instances of
  `PITInt`.
* `Cslib.Complexity.exists_mem_NEXP_notMem_SIZE`: unconditional fixed-degree circuit lower bound
  in `NEXP`.

## References

* [V. Kabanets, R. Impagliazzo, *Derandomizing polynomial identity tests means proving circuit
  lower bounds*][KabanetsImpagliazzo2004]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Theorem 20.16][AroraBarak09]
-/

@[expose] public section

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

/-! ### The permanent family and Laplace self-reducibility via `PITInt` -/

namespace Cslib.Circuits.Arithmetic

open Finset MvPolynomial Turing.MultiTapeTM

universe u

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

end Cslib.Circuits.Arithmetic

/-! ### Fixed-degree circuit lower bounds in `NEXP` -/

namespace Cslib.Complexity

open Turing.MultiTapeTM Circuits Circuits.Boolean

/-- **Unconditional fixed-exponent circuit lower bound in `NEXP`**: for every `k : ℕ`, some
language in `NEXP` (in fact in `Σ₂`) has no Boolean circuits of size `O(n ^ k)`
([Kannan][Kannan1982]). -/
theorem exists_mem_NEXP_notMem_SIZE (k : ℕ) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits ∧
      ∀ c, L ∉ SIZE fun n => c * (n + 1) ^ k := by
  obtain ⟨L, hL₂, hLsize⟩ := exists_mem_SigmaP_two_notMem_SIZE k
  exact ⟨L, SigmaP_subset_NEXP 2 hL₂, hLsize⟩

end Cslib.Complexity
