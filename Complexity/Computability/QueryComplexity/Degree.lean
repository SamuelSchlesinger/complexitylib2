/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Basic
public import Complexity.Foundations.BooleanAnalysis.LowDegreeParity
public import Complexity.Foundations.Data.BitString.Weight

/-!
# The degree of a Boolean function

Every function `f` on the cube `ι → Bool` with values in a commutative ring `R` is a unique
`R`-linear combination of the monomials `∏_{i ∈ S} xᵢ`, its multilinear representation. Its
*total degree* `BitString.totalDegree f` is the least `D` such that `f` is a combination of
monomials of at most `D` coordinates, that is, the least `D` with `f ∈ BitString.lowDegree R ι D`
(`BitString.totalDegree_le_iff_mem_lowDegree`); by `BitString.lowDegree_eq_map_restrictTotalDegree`
it is also the least total degree of a polynomial that agrees with `f` on the cube. Over `ℝ` the
characters `χ_S` and the monomials of at most `D` coordinates span the same functions, so the
total degree is the largest size of a set with a nonzero Fourier coefficient
(`BitString.mem_lowDegree_iff_fourierCoeff_eq_zero`,
`BitString.exists_card_eq_totalDegree_fourierCoeff_ne_zero`).

The degree `deg(f)` of a Boolean function is the total degree of its values `0` and `1` read in
`ℝ` (`QueryComplexity.degree`) [NisanSzegedy1994], [BuhrmanDeWolf2002]; reading the values as the
signs `±1` gives the same degree (`QueryComplexity.degree_eq_totalDegree_signVal`), and so does
negating the output or the input bits. A decision tree of depth `d` computes a function of total
degree at most `d` over any commutative ring, since a node querying `i` computes
`(1 - xᵢ) f₀ + xᵢ f₁` from the functions `f₀` and `f₁` of its subtrees
(`DecisionTree.comp_eval_mem_lowDegree`), so `deg(f) ≤ D(f)`
(`DecisionTree.degree_le_complexity`). Parity, conjunction and disjunction of `n` bits have degree
`n`.

## Main definitions

* `Cslib.BitString.totalDegree`: the total degree of a function on the cube.
* `Cslib.QueryComplexity.degree`: the degree `deg(f)` of a Boolean function.

## Main results

* `Cslib.BitString.totalDegree_le_iff_mem_lowDegree`: the total degree is the least `D` with
  `f ∈ lowDegree R ι D`.
* `Cslib.BitString.mem_lowDegree_iff_fourierCoeff_eq_zero`: over `ℝ`, low degree is the vanishing
  of the Fourier coefficients on larger sets.
* `Cslib.BitString.exists_card_eq_totalDegree_fourierCoeff_ne_zero`: the total degree is attained
  by a nonzero Fourier coefficient.
* `Cslib.DecisionTree.comp_eval_mem_lowDegree`: decision trees of depth `d` compute functions of
  total degree at most `d`.
* `Cslib.QueryComplexity.degree_eq_totalDegree_signVal`: the degree of a Boolean function does not
  depend on reading its values as bits or as signs.
* `Cslib.DecisionTree.degree_le_complexity`: `deg(f) ≤ D(f)`.
* `Cslib.QueryComplexity.degree_parity`, `Cslib.QueryComplexity.degree_threshold_self`,
  `Cslib.QueryComplexity.degree_threshold_one_right`: parity, conjunction and disjunction of `n`
  bits have degree `n`.

## References

* [N. Nisan, M. Szegedy, *On the degree of Boolean functions as real polynomials*][NisanSzegedy1994]
* [H. Buhrman, R. de Wolf, *Complexity measures and decision tree complexity:
  a survey*][BuhrmanDeWolf2002]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib

open Finset

namespace BitString

section CommRing

variable {R : Type*} [CommRing R] {ι : Type*} {f : (ι → Bool) → R} {D : ℕ}

/-- The total degree of a function on the cube: the least `D` such that `f` is an `R`-linear
combination of monomials of at most `D` coordinates, the degree of its multilinear representation.
It is `0` when there is no such `D`, which can only happen over infinitely many coordinates. -/
noncomputable def totalDegree (f : (ι → Bool) → R) : ℕ :=
  sInf {D | f ∈ lowDegree R ι D}

theorem totalDegree_le_of_mem_lowDegree (h : f ∈ lowDegree R ι D) : totalDegree f ≤ D :=
  Nat.sInf_le h

variable [Finite ι]

/-- A function on finitely many coordinates is a combination of monomials of at most its total
degree coordinates. -/
theorem mem_lowDegree_totalDegree (f : (ι → Bool) → R) : f ∈ lowDegree R ι (totalDegree f) :=
  have := Fintype.ofFinite ι
  Nat.sInf_mem (s := {D | f ∈ lowDegree R ι D}) ⟨_, mem_lowDegree_self f⟩

/-- **Total degree as low degree**: the total degree is at most `D` exactly when `f` is a
combination of monomials of at most `D` coordinates. -/
theorem totalDegree_le_iff_mem_lowDegree : totalDegree f ≤ D ↔ f ∈ lowDegree R ι D :=
  ⟨fun h => lowDegree_mono h (mem_lowDegree_totalDegree f), totalDegree_le_of_mem_lowDegree⟩

omit [Finite ι] in
/-- The total degree is at most the number of coordinates. -/
theorem totalDegree_le_card [Fintype ι] (f : (ι → Bool) → R) : totalDegree f ≤ Fintype.card ι :=
  totalDegree_le_of_mem_lowDegree (mem_lowDegree_self f)

omit [Finite ι] in
/-- Negating every input bit preserves the total degree. -/
theorem totalDegree_comp_not (f : (ι → Bool) → R) :
    totalDegree (fun x => f fun i => !x i) = totalDegree f := by
  refine congrArg sInf (Set.ext fun D => ⟨fun h => ?_, comp_not_mem_lowDegree⟩)
  have h' := comp_not_mem_lowDegree h
  simp only [Bool.not_not] at h'
  exact h'

end CommRing

/-! ### Total degree and Fourier coefficients -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → Bool) → ℝ} {D : ℕ}

/-- Characters of at most `D` coordinates have no Fourier weight on sets of more than `D`
coordinates, and neither do their combinations. -/
private theorem signSpan_le_ker_fourierCoeffₗ {S : Finset ι} (hS : D < #S) :
    signSpan ℝ ι D ≤ LinearMap.ker (fourierCoeffₗ S) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨T, hT, rfl⟩
  have hTS : T ≠ S := by
    rintro rfl
    exact absurd hT (not_le.2 hS)
  change fourierCoeff (chi ℝ T) S = 0
  simp only [fourierCoeff, expect_chi_mul_chi, hTS, ↓reduceIte]

/-- A function of total degree at most `D` has no Fourier weight on sets of more than `D`
coordinates. -/
theorem fourierCoeff_eq_zero_of_mem_lowDegree (hf : f ∈ lowDegree ℝ ι D) {S : Finset ι}
    (hS : D < #S) : fourierCoeff f S = 0 :=
  letI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  signSpan_le_ker_fourierCoeffₗ hS (lowDegree_le_signSpan D hf)

/-- **Low degree is Fourier degree**: a real function is a combination of monomials of at most `D`
coordinates exactly when its Fourier coefficients on sets of more than `D` coordinates vanish. -/
theorem mem_lowDegree_iff_fourierCoeff_eq_zero :
    f ∈ lowDegree ℝ ι D ↔ ∀ S : Finset ι, D < #S → fourierCoeff f S = 0 := by
  refine ⟨fun hf S hS => fourierCoeff_eq_zero_of_mem_lowDegree hf hS, fun h => ?_⟩
  have hf : f = ∑ S, fourierCoeff f S • chi ℝ S := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact (sum_fourierCoeff_mul_chi f x).symm
  rw [hf]
  refine Submodule.sum_mem _ fun S _ => ?_
  by_cases hS : #S ≤ D
  · exact Submodule.smul_mem _ _ (lowDegree_mono hS (chi_mem_lowDegree S))
  · rw [h S (not_le.1 hS), zero_smul]
    exact Submodule.zero_mem _

/-- A nonzero Fourier coefficient bounds the total degree below. -/
theorem card_le_totalDegree_of_fourierCoeff_ne_zero {S : Finset ι} (h : fourierCoeff f S ≠ 0) :
    #S ≤ totalDegree f :=
  not_lt.1 fun hlt => h (fourierCoeff_eq_zero_of_mem_lowDegree (mem_lowDegree_totalDegree f) hlt)

/-- The total degree of a real function is at most `D` exactly when its Fourier coefficients vanish
on the sets of more than `D` coordinates. -/
theorem totalDegree_le_iff_fourierCoeff_eq_zero :
    totalDegree f ≤ D ↔ ∀ S : Finset ι, D < #S → fourierCoeff f S = 0 :=
  totalDegree_le_iff_mem_lowDegree.trans mem_lowDegree_iff_fourierCoeff_eq_zero

/-- **The total degree is attained**: a real function of positive total degree has a nonzero
Fourier coefficient on a set of exactly its total degree coordinates. -/
theorem exists_card_eq_totalDegree_fourierCoeff_ne_zero (h : totalDegree f ≠ 0) :
    ∃ S : Finset ι, #S = totalDegree f ∧ fourierCoeff f S ≠ 0 := by
  have hlt : ¬ totalDegree f ≤ totalDegree f - 1 := by omega
  rw [totalDegree_le_iff_fourierCoeff_eq_zero] at hlt
  push Not at hlt
  obtain ⟨S, hS, hne⟩ := hlt
  exact ⟨S, le_antisymm (card_le_totalDegree_of_fourierCoeff_ne_zero hne) (by omega), hne⟩

end BitString

namespace DecisionTree

open BitString

variable {R : Type*} [CommRing R] {ι β : Type*}

/-- **Decision trees compute low-degree functions**: a function of the output of a decision tree
of depth `d` is a combination of monomials of at most `d` coordinates, over any commutative
ring. -/
theorem comp_eval_mem_lowDegree (g : β → R) (t : DecisionTree ι β) :
    (fun x => g (t.eval x)) ∈ lowDegree R ι t.depth := by
  induction t with
  | leaf b => exact const_mem_lowDegree 0 (g b)
  | node i t₀ t₁ ih₀ ih₁ =>
    -- the node computes `(1 - xᵢ) f₀ + xᵢ f₁`
    have h : (fun x => g ((node i t₀ t₁).eval x)) =
        (1 - fun x : ι → Bool => bitVal R (x i)) * (fun x => g (t₀.eval x)) +
          (fun x : ι → Bool => bitVal R (x i)) * fun x => g (t₁.eval x) := by
      funext x
      cases hx : x i <;> simp [hx]
    rw [h, depth_node]
    refine Submodule.add_mem _ (lowDegree_mono ?_
      (mul_mem_lowDegree (one_sub_mem_lowDegree (bitVal_mem_lowDegree i)) ih₀))
      (lowDegree_mono ?_ (mul_mem_lowDegree (bitVal_mem_lowDegree i) ih₁)) <;> omega

/-- A function of the output of a decision tree has total degree at most the depth of the
tree. -/
theorem totalDegree_comp_eval_le (g : β → R) (t : DecisionTree ι β) :
    BitString.totalDegree (fun x => g (t.eval x)) ≤ t.depth :=
  totalDegree_le_of_mem_lowDegree (comp_eval_mem_lowDegree g t)

end DecisionTree

namespace QueryComplexity

open BitString

variable {n : ℕ}

/-- The degree `deg(f)` of a Boolean function: the degree of the unique multilinear real
polynomial that agrees with `f` on `{0,1}ⁿ`, reading the values of `f` as `0` and `1`. -/
noncomputable def degree (f : BooleanFunction n) : ℕ :=
  BitString.totalDegree fun x => bitVal ℝ (f x)

/-- `deg(f) ≤ D` exactly when `f`, read with values `0` and `1`, is a real combination of monomials
of at most `D` coordinates. -/
theorem degree_le_iff_mem_lowDegree {f : BooleanFunction n} {D : ℕ} :
    degree f ≤ D ↔ (fun x => bitVal ℝ (f x)) ∈ lowDegree ℝ (Fin n) D :=
  BitString.totalDegree_le_iff_mem_lowDegree

/-- Reading the values of a Boolean function as `0` and `1` or as the signs `±1` gives the same
degree: `signVal b = 1 - 2 bitVal b`. -/
theorem degree_eq_totalDegree_signVal (f : BooleanFunction n) :
    degree f = BitString.totalDegree fun x => signVal (f x) := by
  have hsign : (fun x => signVal (f x)) = 1 - (2 : ℝ) • fun x => bitVal ℝ (f x) := by
    funext x
    cases hx : f x <;> norm_num [hx]
  have hbit : (fun x => bitVal ℝ (f x)) = (2⁻¹ : ℝ) • (1 - fun x => signVal (f x)) := by
    funext x
    cases hx : f x <;> norm_num [hx]
  refine congrArg sInf (Set.ext fun D => ⟨fun h => ?_, fun h => ?_⟩)
  · change (fun x => signVal (f x)) ∈ lowDegree ℝ (Fin n) D
    rw [hsign]
    exact one_sub_mem_lowDegree (Submodule.smul_mem _ _ h)
  · change (fun x => bitVal ℝ (f x)) ∈ lowDegree ℝ (Fin n) D
    rw [hbit]
    exact Submodule.smul_mem _ _ (one_sub_mem_lowDegree h)

/-- `deg(f) ≤ n`. -/
theorem degree_le_card (f : BooleanFunction n) : degree f ≤ n :=
  (BitString.totalDegree_le_card _).trans_eq (Fintype.card_fin n)

/-- Negating a Boolean function preserves its degree: `bitVal (!b) = 1 - bitVal b`. -/
theorem degree_not (f : BooleanFunction n) : degree (fun x => !f x) = degree f := by
  have h (g : BooleanFunction n) :
      (fun x => bitVal ℝ (!g x)) = 1 - fun x => bitVal ℝ (g x) := by
    funext x
    simp [bitVal_not]
  refine congrArg sInf (Set.ext fun D => ⟨fun hD => ?_, fun hD => ?_⟩)
  · change (fun x => bitVal ℝ (f x)) ∈ lowDegree ℝ (Fin n) D
    simpa only [h, Bool.not_not, sub_sub_cancel] using one_sub_mem_lowDegree hD
  · change (fun x => bitVal ℝ (!f x)) ∈ lowDegree ℝ (Fin n) D
    rw [h]
    exact one_sub_mem_lowDegree hD

/-- Negating every input bit of a Boolean function preserves its degree. -/
theorem degree_comp_not (f : BooleanFunction n) : degree (fun x => f fun i => !x i) = degree f :=
  BitString.totalDegree_comp_not fun x => bitVal ℝ (f x)

/-- A nonzero Fourier coefficient of `f`, read as signs, bounds `deg(f)` below. -/
theorem card_le_degree_of_fourierCoeff_ne_zero {f : BooleanFunction n} {S : Finset (Fin n)}
    (h : fourierCoeff (fun x => signVal (f x)) S ≠ 0) : #S ≤ degree f :=
  (degree_eq_totalDegree_signVal f).symm ▸ BitString.card_le_totalDegree_of_fourierCoeff_ne_zero h

/-- Parity of `n` bits has degree `n`: read as signs, it is the character of all coordinates. -/
theorem degree_parity : degree (parity n) = n := by
  refine le_antisymm (degree_le_card _) ?_
  have h := card_le_degree_of_fourierCoeff_ne_zero (f := parity n) (S := univ) (by
    rw [parity, fourierCoeff_signVal_parityOn]
    simp)
  rwa [card_univ, Fintype.card_fin] at h

/-- The conjunction of `n` bits has degree `n`: read with values `0` and `1`, it is the monomial
of all coordinates, whose top Fourier coefficient is `(-1)ⁿ / 2ⁿ`. -/
theorem degree_threshold_self : degree (threshold n n) = n := by
  refine le_antisymm (degree_le_card _) ?_
  have hfun : (fun x => bitVal ℝ (threshold n n x)) =
      fun x => if x = fun _ => true then 1 else 0 := by
    funext x
    by_cases hx : x = fun _ => true
    · subst hx
      simp [threshold_self]
    · have : ¬∀ i, x i = true := fun h => hx (funext h)
      simp [threshold_self, hx, this]
  have hne : fourierCoeff (fun x => bitVal ℝ (threshold n n x)) univ ≠ 0 := by
    rw [hfun, fourierCoeff_eq_sum]
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte, chi_eq_prod_signVal,
      signVal_true, prod_const, card_univ]
    exact div_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (pow_ne_zero _ two_ne_zero)
  have h := BitString.card_le_totalDegree_of_fourierCoeff_ne_zero hne
  rwa [card_univ, Fintype.card_fin] at h

/-- The disjunction of `n` bits has degree `n`: it is the negation of the conjunction of the
negated bits. -/
theorem degree_threshold_one_right : degree (threshold n 1) = n := by
  have h : threshold n 1 = fun x => !threshold n n fun i => !x i := by
    funext x
    rw [threshold_one_right, threshold_self, ← decide_not]
    simp
  rw [h, degree_not, degree_comp_not, degree_threshold_self]

end QueryComplexity

namespace DecisionTree

/-- **Degree is at most decision tree complexity**: `deg(f) ≤ D(f)`. -/
theorem degree_le_complexity {n : ℕ} (f : BooleanFunction n) :
    QueryComplexity.degree f ≤ complexity f := by
  obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity f
  have h : (fun x => BitString.bitVal ℝ (f x)) = fun x => BitString.bitVal ℝ (t.eval x) :=
    funext fun x => by rw [ht x]
  exact (congrArg BitString.totalDegree h ▸ totalDegree_comp_eval_le _ t).trans hd.le

end DecisionTree

end Cslib
