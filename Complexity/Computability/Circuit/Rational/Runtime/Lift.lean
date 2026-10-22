/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Rational.Executable
public import Complexity.Computability.Circuit.Rational.Runtime.Determinant
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Mathlib.Data.List.GetD

/-!
# A list program for the integer lift tables

At every grid point the executable generator materializes the integer lift matrices
`Rational.Generator.integralLift`, built from the integer Taylor test matrices
`Rational.IntegralTest.padded` and the signed-monomial formula `Rational.IntegralLift.entry`.
Those definitions are indexed by `Fin` and `ZMod` with a type-level modulus, and use `Nat.choose`.
This file restates them as ordinary programs on natural numbers, integers and lists of rows, and
certifies that they run in polynomial time on a multi-tape machine:

* the coefficients of `(X + c) ^ k` are computed by `k` shift-and-add steps, with no division;
* the Taylor test matrix is a list of rows of sums over `List.range M`;
* every lift entry is a double sum over `List.range M` of `M ^ 2` terms. The original formula sums
  over three residues; the residue `β` is forced to be `u - v`, so that sum is dropped.

It proves that the programs compute the landed definitions, and bounds the bit length of every
value they compute: each coefficient, each shift-and-add intermediate, each power, each partial
product and term, every prefix sum and every entry. For `n + 1` matrices, `M` residues and grid
coordinates at most `H`, all of them have at most `Rational.liftBits n M H` bits, which at the
generator's parameters is `Rational.PolynomialBounds.logarithmic n s + 2`.

## Main definitions

* `Rational.coeffRow`: the coefficients of `(X + c) ^ k`, by repeated shift-and-add.
* `Rational.testRows`: the integer Taylor test matrix as a list of rows.
* `Rational.signedCoeff`, `Rational.liftTerm`, `Rational.liftEntry`: the signed coefficient of
  the cyclotomic regular representation, and the terms and entries of the integer lift.
* `Rational.liftTable`, `Rational.liftRows`: one integer lift matrix, and all of them at a grid
  point.
* `Rational.liftBits`: the bit-length budget of the program.

## Main results

* `Rational.getD_coeffRow`: `coeffRow` computes the coefficients of `(X + C c) ^ k`.
* `Rational.testRows_eq`: `testRows M N a t = rowsOf (IntegralTest.padded M N a t)`.
* `Rational.liftEntry_eq`: the double sum computes `IntegralLift.entry`.
* `Rational.liftTable_eq`, `Rational.liftRows_eq_inputTables`: the lift tables are the rows of
  `Generator.integralLift`, and of the executable generator's `inputTables`.
* `Rational.intBits_coeffRow_le`, `Rational.intBits_test_le`, `Rational.intBits_lift_le`,
  `Rational.intBits_le_of_mem_liftRows`: the bit-length bounds.
* `Rational.intBits_le_of_mem_liftRows_parameters`: at the generator's parameters, every entry
  has at most `logConstant * (n + s + 1) ^ 22 + 2` bits.
* `Rational.length_encList_coeffRow_le`: encoded length bound on intermediate coefficient rows.
* `Rational.computableTidilyInPolyTime_coeffRow`, `Rational.computableTidilyInPolyTime_testRows`,
  `Rational.computableTidilyInPolyTime_liftTable`, `Rational.computableTidilyInPolyTime_liftRows`,
  `Rational.liftRows_polytime`: polynomial-time certificates for the coefficient rows, the Taylor
  test matrix and the integer lift tables.

## References

* The index bridges and the forms of `signedCoeff`, `testTerm` and the lift sum are adapted from
  OpenAI's formalization [OpenAI2026RationalHitting] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (files
  lean/OAI/Computability/RationalHitting/TaylorComputation.lean and LiftComputation.lean), via
  the complexitylib port [Schlesinger2026RationalHitting] at revision
  add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.Circuits

namespace Rational

open Polynomial

/-! ### Index bridges -/

lemma val_finEquiv {m : ℕ} [NeZero m] (i : Fin m) : (ZMod.finEquiv m i).val = i.val := by
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m => rfl

lemma val_finEquiv_symm {m : ℕ} [NeZero m] (z : ZMod m) :
    ((ZMod.finEquiv m).symm z).val = z.val := by
  rw [← val_finEquiv, RingEquiv.apply_symm_apply]

/-- A sum over `List.range m` is a sum over `Fin m`. -/
lemma sum_range_eq_sum_fin {A : Type*} [AddCommMonoid A] (m : ℕ) (f : ℕ → A) :
    ((List.range m).map f).sum = ∑ i : Fin m, f i := by
  rw [← List.map_coe_finRange_eq_range, List.map_map, ← List.ofFn_eq_map, List.sum_ofFn]
  rfl

/-- A sum over `List.range m` is a sum over the residues modulo `m`. -/
lemma sum_range_eq_sum_zmod {A : Type*} [AddCommMonoid A] (m : ℕ) [NeZero m] (f : ℕ → A) :
    ((List.range m).map f).sum = ∑ z : ZMod m, f z.val := by
  rw [sum_range_eq_sum_fin]
  exact Fintype.sum_equiv (ZMod.finEquiv m).toEquiv _ _ fun i => by
    change f i.val = f (ZMod.finEquiv m i).val
    rw [val_finEquiv]

/-- Residue subtraction on values, without truncated subtraction below zero. -/
lemma val_sub_eq_mod {m : ℕ} [NeZero m] (u v : ZMod m) :
    (u - v).val = (u.val + m - v.val) % m := by
  have hv := v.val_lt
  rw [← ZMod.val_natCast, Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, add_zero]

/-- The residue `-a * k + a * u` of the lift formula, on values. -/
lemma val_neg_mul_add_mul_eq_mod {m : ℕ} [NeZero m] (a u k : ZMod m) :
    (-a * k + a * u).val = a.val * (u.val + m - k.val) % m := by
  have hk := k.val_lt
  rw [← ZMod.val_natCast, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  congr 1
  ring

/-- The residue of the row-major block coordinate is the quotient by the degree. -/
lemma val_coordinate_symm_fst (e : ℕ) (i : Fin (Generator.matrixDimension e)) :
    ((Generator.coordinate e).symm i).1.val = i.val / CyclotomicRing.degree e := by
  change (ZMod.finEquiv _ (finProdFinEquiv.symm i).1).val = _
  rw [val_finEquiv]
  rfl

/-- The position inside the block of the row-major block coordinate is the remainder. -/
lemma val_coordinate_symm_snd (e : ℕ) (i : Fin (Generator.matrixDimension e)) :
    ((Generator.coordinate e).symm i).2.val = i.val % CyclotomicRing.degree e :=
  rfl

/-! ### Lists of rows -/

/-- A tabulated list of rows is the list of rows of a matrix it agrees with. -/
lemma tabulateRows_eq_rowsOf {d : ℕ} (g : ℕ → ℕ → ℤ) (A : Matrix (Fin d) (Fin d) ℤ)
    (h : ∀ i j : Fin d, g i j = A i j) : tabulateRows d g = rowsOf A := by
  simp only [tabulateRows, rowsOf, ← List.map_coe_finRange_eq_range, List.map_map]
  exact List.map_congr_left fun i _ => List.map_congr_left fun j _ => h i j

/-- Every stored entry is bounded once every indexed entry is. -/
lemma natAbs_le_of_mem_rows {rows : List (List ℤ)} {C : ℕ}
    (h : ∀ i j, (rowEntry rows i j).natAbs ≤ C) {row : List ℤ} (hrow : row ∈ rows) {z : ℤ}
    (hz : z ∈ row) : z.natAbs ≤ C := by
  obtain ⟨i, j, rfl⟩ := exists_rowEntry_eq hrow hz
  exact h i j

/-- Every prefix sum and the sum of a list of terms bounded by `C` are bounded by
`m * C`, where `m` bounds the length. -/
lemma natAbs_take_sum_le_of_length {l : List ℤ} {C m : ℕ} (hl : l.length ≤ m)
    (h : ∀ x ∈ l, x.natAbs ≤ C) (k : ℕ) : (l.take k).sum.natAbs ≤ m * C :=
  (natAbs_take_sum_le h k).trans (Nat.mul_le_mul_right C hl)

/-! ### Coefficient rows -/

/-- Multiply a polynomial by `X + c`. The polynomial is given by its list of coefficients,
constant coefficient first; coefficient `i` of the product is `l[i - 1] + c * l[i]`. -/
def shiftAddRow (c : ℤ) (l : List ℤ) : List ℤ :=
  (List.range (l.length + 1)).map fun i => (0 :: l).getD i 0 + c * l.getD i 0

/-- The coefficients of `(X + c) ^ k`, constant coefficient first, computed by `k` shift-and-add
steps from `[1]`. -/
def coeffRow (c : ℤ) (k : ℕ) : List ℤ :=
  (shiftAddRow c)^[k] [1]

/-- The coefficient rows `coeffRow c k` for `k < M`. -/
def coeffRows (c : ℤ) (M : ℕ) : List (List ℤ) :=
  (List.range M).map (coeffRow c)

@[simp] lemma length_shiftAddRow (c : ℤ) (l : List ℤ) :
    (shiftAddRow c l).length = l.length + 1 := by
  simp [shiftAddRow]

lemma getD_shiftAddRow (c : ℤ) (l : List ℤ) (i : ℕ) :
    (shiftAddRow c l).getD i 0 = (0 :: l).getD i 0 + c * l.getD i 0 := by
  rcases Nat.lt_or_ge i (l.length + 1) with h | h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp [shiftAddRow]
  · rw [List.getD_eq_default _ _ (by simpa using h), List.getD_eq_default _ _ (by simpa using h),
      List.getD_eq_default _ _ (by omega)]
    simp

@[simp] lemma coeffRow_zero (c : ℤ) : coeffRow c 0 = [1] := rfl

lemma coeffRow_succ (c : ℤ) (k : ℕ) : coeffRow c (k + 1) = shiftAddRow c (coeffRow c k) :=
  Function.iterate_succ_apply' _ _ _

@[simp] lemma length_coeffRow (c : ℤ) (k : ℕ) : (coeffRow c k).length = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [coeffRow_succ, length_shiftAddRow, ih]

/-- `coeffRow` computes the coefficients of `(X + C c) ^ k`. -/
theorem getD_coeffRow (c : ℤ) (k i : ℕ) :
    (coeffRow c k).getD i 0 = ((X + C c) ^ k).coeff i := by
  induction k generalizing i with
  | zero => cases i <;> simp [coeff_one]
  | succ k ih =>
    rw [coeffRow_succ, getD_shiftAddRow, pow_succ, mul_add, coeff_add, coeff_mul_C, ih]
    cases i with
    | zero => simp [mul_comm]
    | succ i => rw [List.getD_cons_succ, ih, coeff_mul_X, mul_comm c]

/-- The closed form of the coefficient rows, as in `IntegralTest.full`. -/
theorem getD_coeffRow_eq (c : ℤ) (k i : ℕ) :
    (coeffRow c k).getD i 0 = c ^ (k - i) * (k.choose i : ℤ) := by
  rw [getD_coeffRow, coeff_X_add_C_pow]

lemma rowEntry_coeffRows (c : ℤ) (M k i : ℕ) :
    rowEntry (coeffRows c M) k i = if k < M then (coeffRow c k).getD i 0 else 0 := by
  unfold rowEntry coeffRows
  split_ifs with h
  · rw [List.getD_eq_getElem ((List.range M).map (coeffRow c)) _ (by simpa using h),
      List.getElem_map, List.getElem_range]
  · rw [List.getD_eq_default ((List.range M).map (coeffRow c)) _ (by simpa using h)]
    rfl

/-! ### The integer Taylor test matrix -/

/-- The summand `q` of entry `(u, v)` of the integer Taylor test matrix: coefficient `u` of
`(X - a) ^ (M - 1 - q)` times coefficient `q` of `(X + a) ^ v` times `t ^ q`, read from the
coefficient rows `minus` and `plus`. -/
def testTerm (M : ℕ) (minus plus : List (List ℤ)) (t : ℤ) (u v q : ℕ) : ℤ :=
  rowEntry minus (M - 1 - q) u * rowEntry plus v q * t ^ q

/-- The summands of entry `(u, v)` of the integer Taylor test matrix. -/
def testTerms (M : ℕ) (minus plus : List (List ℤ)) (t : ℤ) (u v : ℕ) : List ℤ :=
  (List.range M).map (testTerm M minus plus t u v)

/-- Entry `(u, v)` of the integer Taylor test matrix; the columns from `N` on are zero. -/
def testEntry (M N : ℕ) (minus plus : List (List ℤ)) (t : ℤ) (u v : ℕ) : ℤ :=
  if v < N then (testTerms M minus plus t u v).sum else 0

/-- The integer Taylor test matrix `IntegralTest.padded M N a t` as a list of rows. -/
def testRows (M N : ℕ) (a t : ℤ) : List (List ℤ) :=
  tabulateRows M (testEntry M N (coeffRows (-a) M) (coeffRows a M) t)

theorem testEntry_eq (M N : ℕ) (a t : ℤ) (u v : Fin M) :
    testEntry M N (coeffRows (-a) M) (coeffRows a M) t u v = IntegralTest.padded M N a t u v := by
  unfold testEntry IntegralTest.padded IntegralTest.full
  split_ifs
  · rw [testTerms, sum_range_eq_sum_fin]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hq := q.isLt
    rw [testTerm, rowEntry_coeffRows, rowEntry_coeffRows, ite_eq_left (by omega),
      ite_eq_left v.isLt, getD_coeffRow_eq, getD_coeffRow_eq, Fin.val_rev,
      show M - (q.val + 1) = M - 1 - q by omega]
  · rfl

theorem rowEntry_testRows (M N : ℕ) (a t : ℤ) (u v : Fin M) :
    rowEntry (testRows M N a t) u v = IntegralTest.padded M N a t u v := by
  rw [testRows, rowEntry_tabulateRows, ite_eq_left ⟨u.isLt, v.isLt⟩, testEntry_eq]

/-- The list program computes the integer Taylor test matrix. -/
theorem testRows_eq (M N : ℕ) (a t : ℤ) :
    testRows M N a t = rowsOf (IntegralTest.padded M N a t) :=
  tabulateRows_eq_rowsOf _ _ (testEntry_eq M N a t)

/-- The Taylor rows, read at residues, are the residue-indexed `Generator.integerTest`. -/
theorem rowEntry_testRows_integerTest (N e : ℕ) (a t : ℤ)
    (u v : ZMod (CyclotomicRing.dimension e)) :
    rowEntry (testRows (CyclotomicRing.dimension e) N a t) u.val v.val =
      Generator.integerTest N e a t u v := by
  rw [← val_finEquiv_symm u, ← val_finEquiv_symm v, rowEntry_testRows]
  rfl

@[simp] lemma length_testRows (M N : ℕ) (a t : ℤ) : (testRows M N a t).length = M :=
  length_tabulateRows _ _

/-! ### The integer lift -/

/-- The signed coefficient of the cyclotomic regular representation on natural numbers:
`CyclotomicRing.signedEntry` with the residue replaced by its value. -/
def signedCoeff (Dg z i j : ℕ) : ℤ :=
  if (z + j) % Dg = i then (-1) ^ ((z + j) / Dg) else 0

/-- The term `(α, κ)` of entry `((u, i), (v, j))` of the integer lift with test matrix `T`, with
`M` residues and cyclotomic degree `Dg`. The residue `β` of `IntegralLift.entry` is forced to be
`u - v`, which is `(u + M - v) % M`; `κ - β` and `α * (u - κ)` are computed likewise. -/
def liftTerm (M Dg : ℕ) (T : List (List ℤ)) (p r : ℤ) (u v i j α κ : ℕ) : ℤ :=
  rowEntry T κ ((κ + M - (u + M - v) % M) % M) * signedCoeff Dg (α * (u + M - κ) % M) i j *
    p ^ α * r ^ ((u + M - v) % M)

/-- The terms `κ < M` of the inner sum, for the residue `α`. -/
def liftTerms (M Dg : ℕ) (T : List (List ℤ)) (p r : ℤ) (u v i j α : ℕ) : List ℤ :=
  (List.range M).map (liftTerm M Dg T p r u v i j α)

/-- The inner sums `α < M` of an integer lift entry. -/
def liftSums (M Dg : ℕ) (T : List (List ℤ)) (p r : ℤ) (u v i j : ℕ) : List ℤ :=
  (List.range M).map fun α => (liftTerms M Dg T p r u v i j α).sum

/-- Entry `((u, i), (v, j))` of the integer lift: a double sum of `M ^ 2` terms. -/
def liftEntry (M Dg : ℕ) (T : List (List ℤ)) (p r : ℤ) (u v i j : ℕ) : ℤ :=
  (liftSums M Dg T p r u v i j).sum

/-- The integer lift matrix with test matrix `T`, in the row-major block order: index `i` is the
pair `(i / Dg, i % Dg)`. -/
def liftTable (M Dg : ℕ) (T : List (List ℤ)) (p r : ℤ) : List (List ℤ) :=
  tabulateRows (M * Dg) fun i j => liftEntry M Dg T p r (i / Dg) (j / Dg) (i % Dg) (j % Dg)

/-- The `n + 1` integer lift matrices at the grid point `(t, p, r)`, with truncation `N`, `M`
residues and cyclotomic degree `Dg`. -/
def liftRows (n N M Dg t p r : ℕ) : List (List (List ℤ)) :=
  (List.range (n + 1)).map fun a : ℕ => liftTable M Dg (testRows M N a t) p r

lemma signedCoeff_eq (e : ℕ) (z : ZMod (CyclotomicRing.dimension e))
    (i j : Fin (CyclotomicRing.degree e)) :
    signedCoeff (CyclotomicRing.degree e) z.val i j = CyclotomicRing.signedEntry e z i j :=
  rfl

/-- The double sum computes the integer lift formula, for any list of rows that agrees with the
test matrix at residues. -/
theorem liftEntry_eq (e : ℕ) {T : List (List ℤ)}
    {T' : Matrix (ZMod (CyclotomicRing.dimension e)) (ZMod (CyclotomicRing.dimension e)) ℤ}
    (hT : ∀ k l, rowEntry T (ZMod.val k) (ZMod.val l) = T' k l) (p r : ℤ)
    (u v : ZMod (CyclotomicRing.dimension e)) (i j : Fin (CyclotomicRing.degree e)) :
    liftEntry (CyclotomicRing.dimension e) (CyclotomicRing.degree e) T p r u.val v.val i j =
      IntegralLift.entry e T' p r u v i j := by
  have hβ (b : ZMod (CyclotomicRing.dimension e)) : u = v + b ↔ b = u - v := by
    constructor <;> intro h <;> subst h <;> ring
  unfold IntegralLift.entry liftEntry liftSums
  rw [sum_range_eq_sum_zmod]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, hβ, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [liftTerms, sum_range_eq_sum_zmod]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [liftTerm, ← val_sub_eq_mod u v, ← val_sub_eq_mod κ (u - v),
    ← val_neg_mul_add_mul_eq_mod α u κ, hT, signedCoeff_eq]

/-- The integer lift entry of `Generator.integralLift`, on the residues of the test rows. -/
theorem liftEntry_testRows (N e : ℕ) (a t p r : ℤ) (u v : ZMod (CyclotomicRing.dimension e))
    (i j : Fin (CyclotomicRing.degree e)) :
    liftEntry (CyclotomicRing.dimension e) (CyclotomicRing.degree e)
        (testRows (CyclotomicRing.dimension e) N a t) p r u.val v.val i j =
      IntegralLift.entry e (Generator.integerTest N e a t) p r u v i j :=
  liftEntry_eq e (rowEntry_testRows_integerTest N e a t) p r u v i j

/-- The entries of a lift table are the entries of `Generator.integralLift`. -/
theorem liftEntry_coordinate (n N e : ℕ) (x : Fin 3 → ℕ) (a : Fin (n + 1))
    (i j : Fin (Generator.matrixDimension e)) :
    liftEntry (CyclotomicRing.dimension e) (CyclotomicRing.degree e)
        (testRows (CyclotomicRing.dimension e) N a (x 0)) (x 1) (x 2)
        (i / CyclotomicRing.degree e) (j / CyclotomicRing.degree e)
        (i % CyclotomicRing.degree e) (j % CyclotomicRing.degree e) =
      Generator.integralLift n N e x a i j := by
  rw [← val_coordinate_symm_fst, ← val_coordinate_symm_fst, ← val_coordinate_symm_snd,
    ← val_coordinate_symm_snd, liftEntry_testRows]
  rfl

/-- The list program computes `Generator.integralLift`. -/
theorem liftTable_eq (n N e : ℕ) (x : Fin 3 → ℕ) (a : Fin (n + 1)) :
    liftTable (CyclotomicRing.dimension e) (CyclotomicRing.degree e)
        (testRows (CyclotomicRing.dimension e) N a (x 0)) (x 1) (x 2) =
      rowsOf (Generator.integralLift n N e x a) :=
  tabulateRows_eq_rowsOf _ _ (liftEntry_coordinate n N e x a)

theorem rowEntry_liftTable (n N e : ℕ) (x : Fin 3 → ℕ) (a : Fin (n + 1))
    (i j : Fin (Generator.matrixDimension e)) :
    rowEntry (liftTable (CyclotomicRing.dimension e) (CyclotomicRing.degree e)
        (testRows (CyclotomicRing.dimension e) N a (x 0)) (x 1) (x 2)) i j =
      Generator.integralLift n N e x a i j := by
  rw [liftTable_eq, rowEntry_rowsOf]

/-- The list program computes all integer lift matrices at a grid point. -/
theorem liftRows_eq (n N e : ℕ) (x : Fin 3 → ℕ) :
    liftRows n N (CyclotomicRing.dimension e) (CyclotomicRing.degree e) (x 0) (x 1) (x 2) =
      (List.finRange (n + 1)).map fun a => rowsOf (Generator.integralLift n N e x a) := by
  rw [liftRows, ← List.map_coe_finRange_eq_range, List.map_map]
  exact List.map_congr_left fun a _ => liftTable_eq n N e x a

/-- The list program computes the executable generator's dense input tables. -/
theorem liftRows_eq_inputTables (n N e : ℕ) (x : Fin 3 → ℕ) :
    liftRows n N (CyclotomicRing.dimension e) (CyclotomicRing.degree e) (x 0) (x 1) (x 2) =
      (ExecutableGenerator.inputTables n N e x).toList.map
        fun A => rowsOf (DeterminantAlgorithm.denote A) := by
  rw [liftRows_eq, ExecutableGenerator.inputTables, Vector.toList_ofFn, List.map_ofFn,
    List.ofFn_eq_map]
  exact List.map_congr_left fun a _ => by simp

@[simp] lemma length_liftTable (M Dg : ℕ) (T : List (List ℤ)) (p r : ℤ) :
    (liftTable M Dg T p r).length = M * Dg :=
  length_tabulateRows _ _

@[simp] lemma length_liftRows (n N M Dg t p r : ℕ) :
    (liftRows n N M Dg t p r).length = n + 1 := by
  simp [liftRows]

/-! ### Magnitude bounds -/

lemma natAbs_pow_le {z : ℤ} {H : ℕ} (hH : 1 ≤ H) (hz : z.natAbs ≤ H) {q M : ℕ} (hq : q ≤ M) :
    (z ^ q).natAbs ≤ H ^ M := by
  rw [Int.natAbs_pow]
  exact (Nat.pow_le_pow_left hz q).trans (Nat.pow_le_pow_right hH hq)

section CoeffBounds

variable {c : ℤ} {w : ℕ} (hw : 1 ≤ w) (hc : c.natAbs ≤ w)
include hw hc

/-- The coefficients of `(X + c) ^ k` are at most `(2 * w) ^ k` in absolute value, by
`IntegralTest.coeff_bound`. -/
theorem natAbs_getD_coeffRow_le (k i : ℕ) : ((coeffRow c k).getD i 0).natAbs ≤ (2 * w) ^ k := by
  have h := IntegralTest.coeff_bound c w k k i hw
    (by rw [Int.abs_eq_natAbs]; exact_mod_cast hc) le_rfl
  rw [← getD_coeffRow, Int.abs_eq_natAbs] at h
  exact_mod_cast h

/-- The values computed by the shift-and-add step from `coeffRow c k`: the shifted coefficient,
the scaled coefficient and their sum. -/
theorem natAbs_shiftAdd_le (k i : ℕ) :
    ((0 :: coeffRow c k).getD i 0).natAbs ≤ (2 * w) ^ (k + 1) ∧
      (c * (coeffRow c k).getD i 0).natAbs ≤ (2 * w) ^ (k + 1) ∧
      ((0 :: coeffRow c k).getD i 0 + c * (coeffRow c k).getD i 0).natAbs ≤
        (2 * w) ^ (k + 1) := by
  have hrow := natAbs_getD_coeffRow_le hw hc k
  refine ⟨?_, ?_, ?_⟩
  · cases i with
    | zero => simp
    | succ i =>
      rw [List.getD_cons_succ]
      exact (hrow i).trans (Nat.pow_le_pow_right (by omega) (by omega))
  · rw [Int.natAbs_mul, pow_succ, Nat.mul_comm c.natAbs]
    exact Nat.mul_le_mul (hrow i) (by omega)
  · rw [← getD_shiftAddRow, ← coeffRow_succ]
    exact natAbs_getD_coeffRow_le hw hc (k + 1) i

theorem natAbs_rowEntry_coeffRows_le (M k i : ℕ) :
    (rowEntry (coeffRows c M) k i).natAbs ≤ (2 * w) ^ M := by
  rw [rowEntry_coeffRows]
  split_ifs with h
  · exact (natAbs_getD_coeffRow_le hw hc k i).trans (Nat.pow_le_pow_right (by omega) h.le)
  · simp

end CoeffBounds

section TestBounds

variable {M : ℕ} {a t : ℤ} {w H : ℕ} (hw : 1 ≤ w) (ha : a.natAbs ≤ w) (hH : 1 ≤ H)
  (ht : t.natAbs ≤ H)

include hw ha in
theorem natAbs_coeffProduct_le (k u v q : ℕ) :
    (rowEntry (coeffRows (-a) M) k u * rowEntry (coeffRows a M) v q).natAbs ≤
      (2 * w) ^ (2 * M) := by
  rw [Int.natAbs_mul, show 2 * M = M + M by omega, pow_add]
  exact Nat.mul_le_mul (natAbs_rowEntry_coeffRows_le hw (by simpa using ha) M k u)
    (natAbs_rowEntry_coeffRows_le hw ha M v q)

include hw ha hH ht

theorem natAbs_testTerm_le {q : ℕ} (hq : q ≤ M) (u v : ℕ) :
    (testTerm M (coeffRows (-a) M) (coeffRows a M) t u v q).natAbs ≤
      (2 * w) ^ (2 * M) * H ^ M := by
  rw [testTerm, Int.natAbs_mul]
  exact Nat.mul_le_mul (natAbs_coeffProduct_le hw ha ..) (natAbs_pow_le hH ht hq)

/-- Every prefix sum of the summands of a Taylor entry. -/
theorem natAbs_testTerms_take_sum_le (u v m : ℕ) :
    ((testTerms M (coeffRows (-a) M) (coeffRows a M) t u v).take m).sum.natAbs ≤
      M * ((2 * w) ^ (2 * M) * H ^ M) := by
  refine natAbs_take_sum_le_of_length (by simp [testTerms]) (fun z hz => ?_) m
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
  exact natAbs_testTerm_le hw ha hH ht (List.mem_range.mp hq).le u v

theorem natAbs_rowEntry_testRows_le (N u v : ℕ) :
    (rowEntry (testRows M N a t) u v).natAbs ≤ M * ((2 * w) ^ (2 * M) * H ^ M) := by
  rw [testRows, rowEntry_tabulateRows]
  split_ifs
  · rw [testEntry]
    split_ifs
    · have h := natAbs_testTerms_take_sum_le (M := M) hw ha hH ht u v M
      rwa [List.take_of_length_le (by simp [testTerms])] at h
    · simp
  · simp

end TestBounds

lemma natAbs_signedCoeff_le (Dg z i j : ℕ) : (signedCoeff Dg z i j).natAbs ≤ 1 := by
  unfold signedCoeff
  split_ifs <;> simp [Int.natAbs_pow]

section LiftBounds

variable {M Dg : ℕ} {T : List (List ℤ)} {p r : ℤ} {A H : ℕ}
  (hT : ∀ k l, (rowEntry T k l).natAbs ≤ A) (hH : 1 ≤ H) (hp : p.natAbs ≤ H) (hr : r.natAbs ≤ H)
include hT

/-- The partial products of a lift term, for any indices. -/
theorem natAbs_liftPartial_le (k l z i j : ℕ) :
    (rowEntry T k l * signedCoeff Dg z i j).natAbs ≤ A := by
  rw [Int.natAbs_mul]
  simpa using Nat.mul_le_mul (hT k l) (natAbs_signedCoeff_le Dg z i j)

include hH hp

theorem natAbs_liftPartial_pow_le (k l z i j : ℕ) {α : ℕ} (hα : α ≤ M) :
    (rowEntry T k l * signedCoeff Dg z i j * p ^ α).natAbs ≤ A * H ^ M := by
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul (natAbs_liftPartial_le hT ..) (natAbs_pow_le hH hp hα)

include hr

theorem natAbs_liftTerm_le {α : ℕ} (hα : α < M) (u v i j κ : ℕ) :
    (liftTerm M Dg T p r u v i j α κ).natAbs ≤ A * H ^ (2 * M) := by
  rw [liftTerm, Int.natAbs_mul, show 2 * M = M + M by omega, pow_add, ← Nat.mul_assoc]
  exact Nat.mul_le_mul (natAbs_liftPartial_pow_le hT hH hp _ _ _ _ _ hα.le)
    (natAbs_pow_le hH hr (Nat.mod_lt _ (by omega)).le)

/-- Every prefix sum of an inner sum of a lift entry. -/
theorem natAbs_liftTerms_take_sum_le {α : ℕ} (hα : α < M) (u v i j m : ℕ) :
    ((liftTerms M Dg T p r u v i j α).take m).sum.natAbs ≤ M * (A * H ^ (2 * M)) := by
  refine natAbs_take_sum_le_of_length (by simp [liftTerms]) (fun z hz => ?_) m
  obtain ⟨κ, -, rfl⟩ := List.mem_map.mp hz
  exact natAbs_liftTerm_le hT hH hp hr hα u v i j κ

/-- Every prefix sum of the outer sum of a lift entry. -/
theorem natAbs_liftSums_take_sum_le (u v i j m : ℕ) :
    ((liftSums M Dg T p r u v i j).take m).sum.natAbs ≤ M * (M * (A * H ^ (2 * M))) := by
  refine natAbs_take_sum_le_of_length (by simp [liftSums]) (fun z hz => ?_) m
  obtain ⟨α, hα, rfl⟩ := List.mem_map.mp hz
  have h := natAbs_liftTerms_take_sum_le (Dg := Dg) hT hH hp hr (List.mem_range.mp hα) u v i j M
  rwa [List.take_of_length_le (by simp [liftTerms])] at h

theorem natAbs_liftEntry_le (u v i j : ℕ) :
    (liftEntry M Dg T p r u v i j).natAbs ≤ M * (M * (A * H ^ (2 * M))) := by
  have h := natAbs_liftSums_take_sum_le (M := M) (Dg := Dg) hT hH hp hr u v i j M
  rwa [List.take_of_length_le (by simp [liftSums])] at h

theorem natAbs_rowEntry_liftTable_le (i j : ℕ) :
    (rowEntry (liftTable M Dg T p r) i j).natAbs ≤ M * (M * (A * H ^ (2 * M))) := by
  rw [liftTable, rowEntry_tabulateRows]
  split_ifs
  · exact natAbs_liftEntry_le hT hH hp hr ..
  · simp

end LiftBounds

/-! ### Bit lengths -/

/-- The bit-length budget of the lift program, for `n + 1` matrices, `M` residues and grid
coordinates at most `H`. At the generator's parameters it is
`PolynomialBounds.logarithmic n s + 2` (`liftBits_parameters`). -/
def liftBits (n M H : ℕ) : ℕ :=
  4 * M + 4 * M * (n + 1) + 3 * M * H + 2

lemma liftBits_parameters (n s : ℕ) :
    liftBits n (Parameters.ambientDimension n s) (Parameters.gridSize n s) =
      PolynomialBounds.logarithmic n s + 2 :=
  rfl

/-- At the generator's parameters, the bit-length budget is polynomial in `n + s + 1`. -/
theorem liftBits_bound (n s : ℕ) :
    liftBits n (Parameters.ambientDimension n s) (Parameters.gridSize n s) ≤
      PolynomialBounds.logConstant * (n + s + 1) ^ 22 + 2 := by
  rw [liftBits_parameters]
  exact Nat.add_le_add_right (PolynomialBounds.logarithmic_bound n s) 2

/-- Every value of magnitude at most `M ^ 3 * (2 * (n + 1)) ^ (2 * M) * H ^ (3 * M)` fits in the
budget. -/
theorem intBits_le_liftBits {n M H : ℕ} {z : ℤ}
    (hz : z.natAbs ≤ M ^ 3 * (2 * (n + 1)) ^ (2 * M) * H ^ (3 * M)) :
    intBits z ≤ liftBits n M H := by
  have hM : M ^ 3 ≤ 2 ^ (3 * M) := by
    rw [Nat.mul_comm, pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le 3
  have hw : (2 * (n + 1)) ^ (2 * M) ≤ 2 ^ (2 * (n + 1) * (2 * M)) := by
    rw [pow_mul 2]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
  have hH : H ^ (3 * M) ≤ 2 ^ (H * (3 * M)) := by
    rw [pow_mul 2]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
  have hprod : M ^ 3 * (2 * (n + 1)) ^ (2 * M) * H ^ (3 * M) ≤
      2 ^ (4 * M + 4 * M * (n + 1) + 3 * M * H) :=
    calc _ ≤ 2 ^ (3 * M) * 2 ^ (2 * (n + 1) * (2 * M)) * 2 ^ (H * (3 * M)) := by gcongr
      _ = 2 ^ (3 * M + 4 * M * (n + 1) + 3 * M * H) := by
          rw [← pow_add, ← pow_add]
          congr 1
          ring
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlt : z.natAbs < 2 ^ (4 * M + 4 * M * (n + 1) + 3 * M * H + 1) :=
    (hz.trans hprod).trans_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _))
  exact (intBits_le_iff _ _).mpr hlt

/-- Each factor of the magnitude bound can be weakened. -/
lemma le_liftMagnitude {M w H i j k : ℕ} (hM : 1 ≤ M) (hw : 1 ≤ w) (hH : 1 ≤ H) (hi : i ≤ 3)
    (hj : j ≤ 2 * M) (hk : k ≤ 3 * M) :
    M ^ i * (2 * w) ^ j * H ^ k ≤ M ^ 3 * (2 * w) ^ (2 * M) * H ^ (3 * M) := by
  gcongr

section Bits

variable {n M H : ℕ} (hM : 1 ≤ M) (hH : 1 ≤ H)
include hM hH

/-- The bit lengths of the coefficients of `(X + c) ^ k` for `k < M`, and of the values computed
by the shift-and-add step from them. -/
theorem intBits_coeffRow_le {c : ℤ} (hc : c.natAbs ≤ n) {k : ℕ} (hk : k < M) (i : ℕ) :
    intBits ((coeffRow c k).getD i 0) ≤ liftBits n M H ∧
      intBits ((0 :: coeffRow c k).getD i 0) ≤ liftBits n M H ∧
      intBits (c * (coeffRow c k).getD i 0) ≤ liftBits n M H ∧
      intBits ((0 :: coeffRow c k).getD i 0 + c * (coeffRow c k).getD i 0) ≤ liftBits n M H := by
  have hw : 1 ≤ n + 1 := by omega
  have hc' : c.natAbs ≤ n + 1 := by omega
  have hB (z : ℤ) (h : z.natAbs ≤ (2 * (n + 1)) ^ (k + 1)) : intBits z ≤ liftBits n M H := by
    refine intBits_le_liftBits (h.trans ?_)
    calc (2 * (n + 1)) ^ (k + 1) = M ^ 0 * (2 * (n + 1)) ^ (k + 1) * H ^ 0 := by simp
      _ ≤ _ := le_liftMagnitude hM hw hH (by omega) (by omega) (by omega)
  obtain ⟨h₁, h₂, h₃⟩ := natAbs_shiftAdd_le hw hc' k i
  exact ⟨hB _ ((natAbs_getD_coeffRow_le hw hc' k i).trans
    (Nat.pow_le_pow_right (by omega) (by omega))), hB _ h₁, hB _ h₂, hB _ h₃⟩

/-- The bit lengths of the powers `z ^ q` for `q ≤ M`; computing a power by repeated
multiplication passes only through smaller powers. -/
theorem intBits_pow_le {z : ℤ} (hz : z.natAbs ≤ H) {q : ℕ} (hq : q ≤ M) :
    intBits (z ^ q) ≤ liftBits n M H := by
  refine intBits_le_liftBits ((natAbs_pow_le hH hz hq).trans ?_)
  calc H ^ M = M ^ 0 * (2 * (n + 1)) ^ 0 * H ^ M := by simp
    _ ≤ _ := le_liftMagnitude hM (by omega) hH (by omega) (by omega) (by omega)

/-- The bit lengths of the values computed for the Taylor test matrix `testRows M N a t`: the
products of coefficients, the terms, every prefix sum of the terms of an entry, and the
entries. -/
theorem intBits_test_le {a t : ℤ} (ha : a.natAbs ≤ n) (ht : t.natAbs ≤ H) (N k u v q m : ℕ)
    (hq : q < M) :
    intBits (rowEntry (coeffRows (-a) M) k u * rowEntry (coeffRows a M) v q) ≤ liftBits n M H ∧
      intBits (testTerm M (coeffRows (-a) M) (coeffRows a M) t u v q) ≤ liftBits n M H ∧
      intBits ((testTerms M (coeffRows (-a) M) (coeffRows a M) t u v).take m).sum ≤
        liftBits n M H ∧
      intBits (rowEntry (testRows M N a t) u v) ≤ liftBits n M H := by
  have hw : 1 ≤ n + 1 := by omega
  have ha' : a.natAbs ≤ n + 1 := by omega
  have hB (i j k' : ℕ) (hi : i ≤ 3) (hj : j ≤ 2 * M) (hk : k' ≤ 3 * M) {z : ℤ}
      (h : z.natAbs ≤ M ^ i * (2 * (n + 1)) ^ j * H ^ k') : intBits z ≤ liftBits n M H :=
    intBits_le_liftBits (h.trans (le_liftMagnitude hM hw hH hi hj hk))
  refine ⟨hB 0 (2 * M) 0 (by omega) le_rfl (by omega) ?_, hB 0 (2 * M) M (by omega) le_rfl
    (by omega) ?_, hB 1 (2 * M) M (by omega) le_rfl (by omega) ?_,
    hB 1 (2 * M) M (by omega) le_rfl (by omega) ?_⟩
  · exact (natAbs_coeffProduct_le hw ha' k u v q).trans_eq (by ring)
  · exact (natAbs_testTerm_le hw ha' hH ht hq.le u v).trans_eq (by ring)
  · exact (natAbs_testTerms_take_sum_le hw ha' hH ht u v m).trans_eq (by ring)
  · exact (natAbs_rowEntry_testRows_le hw ha' hH ht N u v).trans_eq (by ring)

/-- The bit lengths of the values computed for the integer lift with the Taylor test matrix
`testRows M N a t`: the partial products and the terms, every prefix sum of an inner sum and of
the outer sum, the entries and the entries of the lift table. -/
theorem intBits_lift_le {a t p r : ℤ} (ha : a.natAbs ≤ n) (ht : t.natAbs ≤ H)
    (hp : p.natAbs ≤ H) (hr : r.natAbs ≤ H) (N Dg u v i j k l z m : ℕ) {α κ : ℕ} (hα : α < M) :
    intBits (rowEntry (testRows M N a t) k l * signedCoeff Dg z i j) ≤ liftBits n M H ∧
      intBits (rowEntry (testRows M N a t) k l * signedCoeff Dg z i j * p ^ α) ≤
        liftBits n M H ∧
      intBits (liftTerm M Dg (testRows M N a t) p r u v i j α κ) ≤ liftBits n M H ∧
      intBits ((liftTerms M Dg (testRows M N a t) p r u v i j α).take m).sum ≤
        liftBits n M H ∧
      intBits ((liftSums M Dg (testRows M N a t) p r u v i j).take m).sum ≤ liftBits n M H ∧
      intBits (liftEntry M Dg (testRows M N a t) p r u v i j) ≤ liftBits n M H ∧
      intBits (rowEntry (liftTable M Dg (testRows M N a t) p r) k l) ≤ liftBits n M H := by
  have hw : 1 ≤ n + 1 := by omega
  have ha' : a.natAbs ≤ n + 1 := by omega
  have hT := natAbs_rowEntry_testRows_le hw ha' hH ht (M := M) N
  have hB (i j k' : ℕ) (hi : i ≤ 3) (hj : j ≤ 2 * M) (hk : k' ≤ 3 * M) {z : ℤ}
      (h : z.natAbs ≤ M ^ i * (2 * (n + 1)) ^ j * H ^ k') : intBits z ≤ liftBits n M H :=
    intBits_le_liftBits (h.trans (le_liftMagnitude hM hw hH hi hj hk))
  refine ⟨hB 1 (2 * M) M (by omega) le_rfl (by omega) ?_,
    hB 1 (2 * M) (2 * M) (by omega) le_rfl (by omega) ?_,
    hB 1 (2 * M) (3 * M) (by omega) le_rfl le_rfl ?_,
    hB 2 (2 * M) (3 * M) (by omega) le_rfl le_rfl ?_,
    hB 3 (2 * M) (3 * M) le_rfl le_rfl le_rfl ?_,
    hB 3 (2 * M) (3 * M) le_rfl le_rfl le_rfl ?_,
    hB 3 (2 * M) (3 * M) le_rfl le_rfl le_rfl ?_⟩
  · exact (natAbs_liftPartial_le hT k l z i j).trans_eq (by ring)
  · exact (natAbs_liftPartial_pow_le hT hH hp k l z i j hα.le).trans_eq (by ring)
  · exact (natAbs_liftTerm_le hT hH hp hr hα u v i j κ).trans_eq (by ring)
  · exact (natAbs_liftTerms_take_sum_le (Dg := Dg) hT hH hp hr hα u v i j m).trans_eq (by ring)
  · exact (natAbs_liftSums_take_sum_le (Dg := Dg) hT hH hp hr u v i j m).trans_eq (by ring)
  · exact (natAbs_liftEntry_le (Dg := Dg) hT hH hp hr u v i j).trans_eq (by ring)
  · exact (natAbs_rowEntry_liftTable_le (Dg := Dg) hT hH hp hr k l).trans_eq (by ring)

/-- Every entry of every integer lift table at a grid point with coordinates at most `H` has
at most `liftBits n M H` bits. -/
theorem intBits_le_of_mem_liftRows {N Dg t p r : ℕ} (ht : t ≤ H) (hp : p ≤ H) (hr : r ≤ H)
    {table : List (List ℤ)} (htable : table ∈ liftRows n N M Dg t p r) {row : List ℤ}
    (hrow : row ∈ table) {z : ℤ} (hz : z ∈ row) : intBits z ≤ liftBits n M H := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp htable
  obtain ⟨k, l, rfl⟩ := exists_rowEntry_eq hrow hz
  have ha' : ((a : ℕ) : ℤ).natAbs ≤ n := by
    simpa using Nat.lt_succ_iff.mp (List.mem_range.mp ha)
  exact (intBits_lift_le hM hH ha' (by simpa using ht) (by simpa using hp) (by simpa using hr)
    N Dg 0 0 0 0 k l 0 0 (α := 0) (κ := 0) hM).2.2.2.2.2.2

end Bits

/-- At the generator's parameters, every entry of every integer lift table at a grid point has
at most `logConstant * (n + s + 1) ^ 22 + 2` bits. -/
theorem intBits_le_of_mem_liftRows_parameters {n s t p r : ℕ} (ht : t ≤ Parameters.gridSize n s)
    (hp : p ≤ Parameters.gridSize n s) (hr : r ≤ Parameters.gridSize n s) {table : List (List ℤ)}
    (htable : table ∈ liftRows n (Parameters.truncation n s) (Parameters.ambientDimension n s)
      (CyclotomicRing.degree (Parameters.exponent n s)) t p r)
    {row : List ℤ} (hrow : row ∈ table) {z : ℤ} (hz : z ∈ row) :
    intBits z ≤ PolynomialBounds.logConstant * (n + s + 1) ^ 22 + 2 :=
  (intBits_le_of_mem_liftRows (by unfold Parameters.ambientDimension; exact Nat.one_le_two_pow)
    (by unfold Parameters.gridSize; omega) ht hp hr htable hrow hz).trans (liftBits_bound n s)

/-! ### Polynomial-time certificates -/

open Turing MultiTapeTM MultiTapeTM.ComputableTidilyInPolyTime

/-- Upper bound on the bit length of any entry of `coeffRow c i` for `i ≤ k`, where `L` is the
encoded length of `c`. -/
def coeffEntryBound (L k : ℕ) : ℕ := (L + 1) * k + 2

/-- Upper bound on the encoded length of `coeffRow c i` for `i ≤ k`, where `L` is the encoded
length of `c`. -/
def coeffRowBound (L k : ℕ) : ℕ := (k + 1) * (2 * coeffEntryBound L k + 1)

/-- Every intermediate coefficient row up to stage `k` has encoded length bounded by
`coeffRowBound`. -/
theorem length_encList_coeffRow_le (c : ℤ) {i k : ℕ} (hik : i ≤ k) :
    (encList encIntBin (coeffRow c i)).length ≤ coeffRowBound (encIntBin c).length k := by
  set L := (encIntBin c).length
  have hc_lt : c.natAbs < 2 ^ L := by
    rw [← intBits_le_iff, intBits_eq_length_encIntBin]
    exact Nat.le_succ L
  have h2w : 2 * (c.natAbs + 1) ≤ 2 ^ (L + 1) := by
    rw [pow_succ']
    exact Nat.mul_le_mul_left 2 hc_lt
  have hentry {z : ℤ} (hz : z ∈ coeffRow c i) :
      (encIntBin z).length ≤ coeffEntryBound L k := by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hz
    rw [← intBits_eq_length_encIntBin, coeffEntryBound, intBits_le_iff,
      ← List.getD_eq_getElem _ 0 hj]
    calc ((coeffRow c i).getD j 0).natAbs
        ≤ (2 * (c.natAbs + 1)) ^ i := natAbs_getD_coeffRow_le (by omega) (by omega) i j
      _ ≤ (2 ^ (L + 1)) ^ i := Nat.pow_le_pow_left h2w i
      _ = 2 ^ ((L + 1) * i) := (pow_mul 2 (L + 1) i).symm
      _ ≤ 2 ^ ((L + 1) * k) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hik)
      _ < 2 ^ ((L + 1) * k + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)
  refine (length_encList_le encIntBin (coeffRow c i) fun z hz => hentry hz).trans ?_
  rw [length_coeffRow]
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_right hik 1)

private lemma polyBounded_coeffRowBound {α : Type} {size L k : α → ℕ}
    (hL : PolyBounded size L) (hk : PolyBounded size k) :
    PolyBounded size (fun x => coeffRowBound (L x) (k x)) := by
  have hentry : PolyBounded size (fun x => coeffEntryBound (L x) (k x)) :=
    ((hL.add (.const 1)).mul hk).add (.const 2)
  exact (hk.add (.const 1)).mul (((PolyBounded.const 2).mul hentry).add (.const 1))

variable {α : Type} {encIn : α ↪ List Bool}

@[local fun_prop]
private theorem listGetD_intBin {l : α → List ℤ} {i : α → ℕ}
    (hl : ComputableTidilyInPolyTime l encIn (encList encIntBin))
    (hi : ComputableTidilyInPolyTime i encIn encUnary) (d : ℤ) :
    ComputableTidilyInPolyTime (fun x => (l x).getD (i x) d) encIn encIntBin :=
  (listGetD (encA := encIntBin) d).comp (hl.prod hi)

@[local fun_prop]
private theorem intBin_of_unary {n : α → ℕ}
    (hn : ComputableTidilyInPolyTime n encIn encUnary) :
    ComputableTidilyInPolyTime (fun x => (n x : ℤ)) encIn encIntBin :=
  intBin_natCast.comp (unary_to_binary.comp hn)

@[fun_prop]
theorem unary_decide_eq {a b : α → ℕ}
    (ha : ComputableTidilyInPolyTime a encIn encUnary)
    (hb : ComputableTidilyInPolyTime b encIn encUnary) :
    ComputableTidilyInPolyTime (fun x => decide (a x = b x)) encIn encBool :=
  (decide_eq encUnary).comp (ha.prod hb)

/-- One shift-and-add step of the coefficient recurrence is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_shiftAddRow {c : α → ℤ} {l : α → List ℤ}
    (hc : ComputableTidilyInPolyTime c encIn encIntBin)
    (hl : ComputableTidilyInPolyTime l encIn (encList encIntBin)) :
    ComputableTidilyInPolyTime (fun x => shiftAddRow (c x) (l x)) encIn (encList encIntBin) := by
  unfold shiftAddRow
  fun_prop

/-- Computing the coefficient row `coeffRow c k` is polynomial-time for a binary integer `c` and a
unary degree `k`. -/
@[fun_prop]
theorem computableTidilyInPolyTime_coeffRow {c : α → ℤ} {k : α → ℕ}
    (hc : ComputableTidilyInPolyTime c encIn encIntBin)
    (hk : ComputableTidilyInPolyTime k encIn encUnary) :
    ComputableTidilyInPolyTime (fun x => coeffRow (c x) (k x)) encIn (encList encIntBin) :=
  iterateWith hc hk (const [1])
    (computableTidilyInPolyTime_shiftAddRow (fst _ _) (snd _ _))
    (polyBounded_coeffRowBound hc.polyBounded_length hk.polyBounded)
    fun x _ hi => length_encList_coeffRow_le (c x) hi

/-- Computing the table of coefficient rows `coeffRows c M` is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_coeffRows {c : α → ℤ} {M : α → ℕ}
    (hc : ComputableTidilyInPolyTime c encIn encIntBin)
    (hM : ComputableTidilyInPolyTime M encIn encUnary) :
    ComputableTidilyInPolyTime (fun x => coeffRows (c x) (M x))
      encIn (encList (encList encIntBin)) := by
  unfold coeffRows
  fun_prop

/-- Computing one summand of a Taylor test matrix entry is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_testTerm {M u v q : α → ℕ} {minus plus : α → List (List ℤ)}
    {t : α → ℤ}
    (hM : ComputableTidilyInPolyTime M encIn encUnary)
    (hminus : ComputableTidilyInPolyTime minus encIn (encList (encList encIntBin)))
    (hplus : ComputableTidilyInPolyTime plus encIn (encList (encList encIntBin)))
    (ht : ComputableTidilyInPolyTime t encIn encIntBin)
    (hu : ComputableTidilyInPolyTime u encIn encUnary)
    (hv : ComputableTidilyInPolyTime v encIn encUnary)
    (hq : ComputableTidilyInPolyTime q encIn encUnary) :
    ComputableTidilyInPolyTime
      (fun x => testTerm (M x) (minus x) (plus x) (t x) (u x) (v x) (q x))
      encIn encIntBin := by
  unfold testTerm
  fun_prop

/-- Computing the list of summands of a Taylor test matrix entry is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_testTerms {M u v : α → ℕ} {minus plus : α → List (List ℤ)}
    {t : α → ℤ}
    (hM : ComputableTidilyInPolyTime M encIn encUnary)
    (hminus : ComputableTidilyInPolyTime minus encIn (encList (encList encIntBin)))
    (hplus : ComputableTidilyInPolyTime plus encIn (encList (encList encIntBin)))
    (ht : ComputableTidilyInPolyTime t encIn encIntBin)
    (hu : ComputableTidilyInPolyTime u encIn encUnary)
    (hv : ComputableTidilyInPolyTime v encIn encUnary) :
    ComputableTidilyInPolyTime
      (fun x => testTerms (M x) (minus x) (plus x) (t x) (u x) (v x))
      encIn (encList encIntBin) := by
  unfold testTerms
  fun_prop

/-- Computing one entry of the integer Taylor test matrix is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_testEntry {M N u v : α → ℕ} {minus plus : α → List (List ℤ)}
    {t : α → ℤ}
    (hM : ComputableTidilyInPolyTime M encIn encUnary)
    (hN : ComputableTidilyInPolyTime N encIn encUnary)
    (hminus : ComputableTidilyInPolyTime minus encIn (encList (encList encIntBin)))
    (hplus : ComputableTidilyInPolyTime plus encIn (encList (encList encIntBin)))
    (ht : ComputableTidilyInPolyTime t encIn encIntBin)
    (hu : ComputableTidilyInPolyTime u encIn encUnary)
    (hv : ComputableTidilyInPolyTime v encIn encUnary) :
    ComputableTidilyInPolyTime
      (fun x => testEntry (M x) (N x) (minus x) (plus x) (t x) (u x) (v x))
      encIn encIntBin := by
  unfold testEntry
  fun_prop

/-- Computing the integer Taylor test matrix `testRows M N a t` is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_testRows {M N : α → ℕ} {a t : α → ℤ}
    (hM : ComputableTidilyInPolyTime M encIn encUnary)
    (hN : ComputableTidilyInPolyTime N encIn encUnary)
    (ha : ComputableTidilyInPolyTime a encIn encIntBin)
    (ht : ComputableTidilyInPolyTime t encIn encIntBin) :
    ComputableTidilyInPolyTime (fun x => testRows (M x) (N x) (a x) (t x))
      encIn (encList (encList encIntBin)) := by
  unfold testRows
  fun_prop

/-- Computing the signed cyclotomic regular-representation coefficient is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_signedCoeff {Dg z i j : α → ℕ}
    (hDg : ComputableTidilyInPolyTime Dg encIn encUnary)
    (hz : ComputableTidilyInPolyTime z encIn encUnary)
    (hi : ComputableTidilyInPolyTime i encIn encUnary)
    (hj : ComputableTidilyInPolyTime j encIn encUnary) :
    ComputableTidilyInPolyTime (fun x => signedCoeff (Dg x) (z x) (i x) (j x))
      encIn encIntBin := by
  unfold signedCoeff
  fun_prop

/-- Computing one summand of an integer lift entry is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_liftTerm {M Dg u v i j a k : α → ℕ}
    {T : α → List (List ℤ)} {p r : α → ℤ}
    (hM : ComputableTidilyInPolyTime M encIn encUnary)
    (hDg : ComputableTidilyInPolyTime Dg encIn encUnary)
    (hT : ComputableTidilyInPolyTime T encIn (encList (encList encIntBin)))
    (hp : ComputableTidilyInPolyTime p encIn encIntBin)
    (hr : ComputableTidilyInPolyTime r encIn encIntBin)
    (hu : ComputableTidilyInPolyTime u encIn encUnary)
    (hv : ComputableTidilyInPolyTime v encIn encUnary)
    (hi : ComputableTidilyInPolyTime i encIn encUnary)
    (hj : ComputableTidilyInPolyTime j encIn encUnary)
    (ha : ComputableTidilyInPolyTime a encIn encUnary)
    (hk : ComputableTidilyInPolyTime k encIn encUnary) :
    ComputableTidilyInPolyTime
      (fun x => liftTerm (M x) (Dg x) (T x) (p x) (r x) (u x) (v x) (i x) (j x) (a x) (k x))
      encIn encIntBin := by
  unfold liftTerm
  fun_prop

/-- Computing the inner list of summands of an integer lift entry is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_liftTerms {M Dg u v i j a : α → ℕ}
    {T : α → List (List ℤ)} {p r : α → ℤ}
    (hM : ComputableTidilyInPolyTime M encIn encUnary)
    (hDg : ComputableTidilyInPolyTime Dg encIn encUnary)
    (hT : ComputableTidilyInPolyTime T encIn (encList (encList encIntBin)))
    (hp : ComputableTidilyInPolyTime p encIn encIntBin)
    (hr : ComputableTidilyInPolyTime r encIn encIntBin)
    (hu : ComputableTidilyInPolyTime u encIn encUnary)
    (hv : ComputableTidilyInPolyTime v encIn encUnary)
    (hi : ComputableTidilyInPolyTime i encIn encUnary)
    (hj : ComputableTidilyInPolyTime j encIn encUnary)
    (ha : ComputableTidilyInPolyTime a encIn encUnary) :
    ComputableTidilyInPolyTime
      (fun x => liftTerms (M x) (Dg x) (T x) (p x) (r x) (u x) (v x) (i x) (j x) (a x))
      encIn (encList encIntBin) := by
  unfold liftTerms
  fun_prop

/-- Computing the list of inner sums of an integer lift entry is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_liftSums {M Dg u v i j : α → ℕ}
    {T : α → List (List ℤ)} {p r : α → ℤ}
    (hM : ComputableTidilyInPolyTime M encIn encUnary)
    (hDg : ComputableTidilyInPolyTime Dg encIn encUnary)
    (hT : ComputableTidilyInPolyTime T encIn (encList (encList encIntBin)))
    (hp : ComputableTidilyInPolyTime p encIn encIntBin)
    (hr : ComputableTidilyInPolyTime r encIn encIntBin)
    (hu : ComputableTidilyInPolyTime u encIn encUnary)
    (hv : ComputableTidilyInPolyTime v encIn encUnary)
    (hi : ComputableTidilyInPolyTime i encIn encUnary)
    (hj : ComputableTidilyInPolyTime j encIn encUnary) :
    ComputableTidilyInPolyTime
      (fun x => liftSums (M x) (Dg x) (T x) (p x) (r x) (u x) (v x) (i x) (j x))
      encIn (encList encIntBin) := by
  unfold liftSums
  fun_prop

/-- Computing one entry of the integer lift matrix is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_liftEntry {M Dg u v i j : α → ℕ}
    {T : α → List (List ℤ)} {p r : α → ℤ}
    (hM : ComputableTidilyInPolyTime M encIn encUnary)
    (hDg : ComputableTidilyInPolyTime Dg encIn encUnary)
    (hT : ComputableTidilyInPolyTime T encIn (encList (encList encIntBin)))
    (hp : ComputableTidilyInPolyTime p encIn encIntBin)
    (hr : ComputableTidilyInPolyTime r encIn encIntBin)
    (hu : ComputableTidilyInPolyTime u encIn encUnary)
    (hv : ComputableTidilyInPolyTime v encIn encUnary)
    (hi : ComputableTidilyInPolyTime i encIn encUnary)
    (hj : ComputableTidilyInPolyTime j encIn encUnary) :
    ComputableTidilyInPolyTime
      (fun x => liftEntry (M x) (Dg x) (T x) (p x) (r x) (u x) (v x) (i x) (j x))
      encIn encIntBin := by
  unfold liftEntry
  fun_prop

/-- Computing the integer lift matrix `liftTable M Dg T p r` is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_liftTable {M Dg : α → ℕ}
    {T : α → List (List ℤ)} {p r : α → ℤ}
    (hM : ComputableTidilyInPolyTime M encIn encUnary)
    (hDg : ComputableTidilyInPolyTime Dg encIn encUnary)
    (hT : ComputableTidilyInPolyTime T encIn (encList (encList encIntBin)))
    (hp : ComputableTidilyInPolyTime p encIn encIntBin)
    (hr : ComputableTidilyInPolyTime r encIn encIntBin) :
    ComputableTidilyInPolyTime
      (fun x => liftTable (M x) (Dg x) (T x) (p x) (r x))
      encIn (encList (encList encIntBin)) := by
  unfold liftTable
  fun_prop

/-- Computing all `n + 1` integer lift tables `liftRows n N M Dg t p r` at a grid point is
polynomial-time from unary parameters and coordinates. -/
@[fun_prop]
theorem computableTidilyInPolyTime_liftRows {n N M Dg t p r : α → ℕ}
    (hn : ComputableTidilyInPolyTime n encIn encUnary)
    (hN : ComputableTidilyInPolyTime N encIn encUnary)
    (hM : ComputableTidilyInPolyTime M encIn encUnary)
    (hDg : ComputableTidilyInPolyTime Dg encIn encUnary)
    (ht : ComputableTidilyInPolyTime t encIn encUnary)
    (hp : ComputableTidilyInPolyTime p encIn encUnary)
    (hr : ComputableTidilyInPolyTime r encIn encUnary) :
    ComputableTidilyInPolyTime
      (fun x => liftRows (n x) (N x) (M x) (Dg x) (t x) (p x) (r x))
      encIn (encList (encList (encList encIntBin))) := by
  unfold liftRows
  fun_prop

/-- Standalone polynomial-time certificate for `liftRows` on a 7-tuple of unary naturals. -/
@[fun_prop]
theorem liftRows_polytime :
    ComputableTidilyInPolyTime
      (fun q : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ =>
        liftRows q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2)
      (encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary
        (encPair encUnary (encPair encUnary encUnary))))))
      (encList (encList (encList encIntBin))) := by
  fun_prop

end Rational

end Cslib.Circuits
