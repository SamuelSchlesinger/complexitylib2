/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bernoulli coordinate sampling and transference

A Boolean mask `selected : ι → Bool` is a set of coordinates. Selecting each coordinate
independently with probability `p` gives it the weight `bernoulliWeight p selected`, and
`bernoulliAverage p f` is the expectation of `f` over the random mask, a finite sum. Increasing the
rate decreases the expectation of an antitone function (`bernoulliAverage_bias_antitone`), and the
union of independent masks of rates `p` and `q` has rate `p + q - p q` (`bernoulliAverage_union`).
For a lower set `A` of masks, so the probability of `A` at rate `q` is at most its probability at
rate `p` to the power `h` when `h p ≤ q` (`bernoulliAverage_lowerSet_pow_le`): this is the
transference principle of Section 4 of [Korten2026], which Korten attributes to Zhao
(*Probabilistic Methods in Combinatorics*, Lemma 4.3.7). In particular the probability at a small
rate `r` is at least the probability at rate `1 / 4` to the power `5 r`
(`bernoulliAverage_lowerSet_transfer`).

## Main definitions

* `Cslib.BooleanAnalysis.bernoulliWeight`: the probability of a mask.
* `Cslib.BooleanAnalysis.bernoulliAverage`: the expectation over a random mask.

## Main results

* `Cslib.BooleanAnalysis.bernoulliAverage_coordinate`,
  `Cslib.BooleanAnalysis.bernoulliAverage_nonempty`: the probability that a coordinate is
  selected, and that some coordinate is.
* `Cslib.BooleanAnalysis.bernoulliAverage_bias_antitone`: antitone functions have smaller
  expectations at larger rates.
* `Cslib.BooleanAnalysis.bernoulliAverage_union`: unions of independent masks.
* `Cslib.BooleanAnalysis.bernoulliAverage_lowerSet_pow_le`,
  `Cslib.BooleanAnalysis.bernoulliAverage_lowerSet_transfer`: transference for lower sets.

## References

* [O. Korten, *Top-Down Lower Bounds for All Depths*][Korten2026]
-/

@[expose] public section

namespace Cslib.BooleanAnalysis

open Finset
open scoped BigOperators

/-- The probability of the mask `selected` when each coordinate is selected independently with
probability `p`. -/
noncomputable def bernoulliWeight {ι : Type*} [Fintype ι] (p : ℝ) (selected : ι → Bool) : ℝ :=
  ∏ i, if selected i then p else 1 - p

/-- The expectation of `f` over a random mask selecting each coordinate independently with
probability `p`. It is a probability expectation when `0 ≤ p ≤ 1`. -/
noncomputable def bernoulliAverage {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ)
    (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ selected, bernoulliWeight p selected * f selected

private theorem sum_cons {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    (∑ x, f x) = (∑ x, f (Fin.cons false x)) + ∑ x, f (Fin.cons true x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp f]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  exact add_comm _ _

theorem bernoulliWeight_cons {n : ℕ} (p : ℝ) (b : Bool)
    (selected : Fin n → Bool) :
    bernoulliWeight p (Fin.cons b selected) =
      (if b then p else 1 - p) * bernoulliWeight p selected := by
  simp [bernoulliWeight, Fin.prod_univ_succ]

theorem bernoulliAverage_cons {n : ℕ} (p : ℝ)
    (f : (Fin (n + 1) → Bool) → ℝ) :
    bernoulliAverage p f =
      (1 - p) * bernoulliAverage p (fun x => f (Fin.cons false x)) +
        p * bernoulliAverage p (fun x => f (Fin.cons true x)) := by
  unfold bernoulliAverage
  rw [sum_cons]
  simp_rw [bernoulliWeight_cons]
  simp only [Bool.false_eq_true, ite_false, ite_true, mul_assoc, ← mul_sum]

/-- Bernoulli expectation preserves pointwise inequalities at probability rates. -/
theorem bernoulliAverage_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) {f g : (ι → Bool) → ℝ}
    (hfg : ∀ x, f x ≤ g x) : bernoulliAverage p f ≤ bernoulliAverage p g := by
  apply sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left (hfg x)
  apply prod_nonneg
  intro i _
  split_ifs
  · exact hp
  · exact sub_nonneg.mpr hp'

/-- Product Bernoulli weights sum to one. This identity holds algebraically
for every `p`; they are nonnegative when `p ∈ [0, 1]`. -/
theorem bernoulliAverage_const {ι : Type*} [Fintype ι] [DecidableEq ι] (p c : ℝ) :
    bernoulliAverage p (fun _ : ι → Bool => c) = c := by
  unfold bernoulliAverage bernoulliWeight
  rw [← sum_mul, ← Fintype.prod_sum (fun (_ : ι) (b : Bool) => if b then p else 1 - p)]
  simp

theorem bernoulliWeight_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (p : ℝ) (s : κ → Bool) :
    bernoulliWeight p (fun i => s (e i)) = bernoulliWeight p s := by
  exact e.prod_comp (fun i => if s i then p else 1 - p)

/-- An equivalence of coordinate types preserves Bernoulli expectations. -/
theorem bernoulliAverage_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (p : ℝ) (f : (κ → Bool) → ℝ) :
    bernoulliAverage p (fun x => f (fun j => x (e.symm j))) = bernoulliAverage p f := by
  let E := Equiv.arrowCongr e (Equiv.refl Bool)
  unfold bernoulliAverage
  rw [← E.sum_comp (fun x => bernoulliWeight p x * f x)]
  apply sum_congr rfl
  intro x _
  change bernoulliWeight p x * f (fun j => x (e.symm j)) =
    bernoulliWeight p (fun j => x (e.symm j)) * f (fun j => x (e.symm j))
  rw [bernoulliWeight_reindex]

theorem bernoulliWeight_split {ι : Type*} [Fintype ι]
    (p : ℝ) (s x : ι → Bool) :
    bernoulliWeight p x = bernoulliWeight p (fun i : {i // s i = true} => x i) *
      bernoulliWeight p (fun i : {i // s i ≠ true} => x i) := by
  exact (Fintype.prod_subtype_mul_prod_subtype (fun i => s i = true)
    (fun i => if x i then p else 1 - p)).symm

/-- Restricting a Bernoulli mask to fixed coordinates preserves its product law. -/
theorem bernoulliAverage_restrict {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (s : ι → Bool) (f : ({i // s i = true} → Bool) → ℝ) :
    bernoulliAverage p (fun x : ι → Bool => f (fun i => x i)) = bernoulliAverage p f := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => s i = true) (fun _ => Bool)
  unfold bernoulliAverage
  rw [← e.symm.sum_comp (fun x => bernoulliWeight p x * f (fun i => x i))]
  simp_rw [bernoulliWeight_split p s]
  have hleft (z : ({i // s i = true} → Bool) × ({i // s i ≠ true} → Bool)) :
      (fun i : {i // s i = true} => e.symm z i) = z.1 := by
    funext i
    simp [e, Equiv.piEquivPiSubtypeProd, i.property]
  have hright (z : ({i // s i = true} → Bool) × ({i // s i ≠ true} → Bool)) :
      (fun i : {i // s i ≠ true} => e.symm z i) = z.2 := by
    funext i
    simp [e, Equiv.piEquivPiSubtypeProd, i.property]
  simp_rw [hleft, hright]
  rw [Fintype.sum_prod_type]
  have htotal : (∑ y : {i // s i ≠ true} → Bool, bernoulliWeight p y) = 1 := by
    simpa [bernoulliAverage] using
      bernoulliAverage_const (ι := {i // s i ≠ true}) p 1
  simp only [mul_assoc, ← mul_sum, ← sum_mul, htotal, one_mul]

theorem bernoulliAverage_linear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p a b : ℝ) (f g : (ι → Bool) → ℝ) :
    bernoulliAverage p (fun x => a * f x + b * g x) =
      a * bernoulliAverage p f + b * bernoulliAverage p g := by
  unfold bernoulliAverage
  simp only [mul_add, sum_add_distrib]
  congr 1 <;> rw [mul_sum] <;> apply sum_congr rfl <;> intro x _ <;> ring

/-- Increasing the sampling rate decreases the expectation of an antitone function. -/
theorem bernoulliAverage_bias_antitone {n : ℕ} {f : (Fin n → Bool) → ℝ} (hf : Antitone f)
    {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) :
    bernoulliAverage q f ≤ bernoulliAverage p f := by
  induction n with
  | zero =>
    have he : f = fun _ => f (fun i => Fin.elim0 i) :=
      funext fun _ => congrArg f (Subsingleton.elim _ _)
    rw [he]
    simp only [bernoulliAverage_const]
    exact le_rfl
  | succ n ih =>
    have hs (b : Bool) : Antitone (fun x => f (Fin.cons b x)) := by
      intro x y hxy
      apply hf
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact le_rfl
      · exact hxy j
    have hl : bernoulliAverage p (fun x => f (Fin.cons true x)) ≤
        bernoulliAverage p (fun x => f (Fin.cons false x)) := by
      apply bernoulliAverage_mono hp (hpq.trans hq)
      intro x
      apply hf
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Bool.false_le _
      · exact le_rfl
    rw [bernoulliAverage_cons, bernoulliAverage_cons]
    have h0 := mul_le_mul_of_nonneg_left (ih (hs false)) (sub_nonneg.mpr hq)
    have h1 := mul_le_mul_of_nonneg_left (ih (hs true)) (hp.trans hpq)
    nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr hl)]

/-- The union of independent masks of rates `p` and `q` has rate `p + q - p * q`. -/
theorem bernoulliAverage_union {n : ℕ} (p q : ℝ) (f : (Fin n → Bool) → ℝ) :
    bernoulliAverage p (fun r => bernoulliAverage q (fun s =>
      f (fun i => r i || s i))) = bernoulliAverage (p + q - p * q) f := by
  induction n with
  | zero =>
    have he : f = fun _ => f (fun i => Fin.elim0 i) :=
      funext fun _ => congrArg f (Subsingleton.elim _ _)
    rw [he]
    simp only [bernoulliAverage_const]
  | succ n ih =>
    have hc (a b : Bool) (r s : Fin n → Bool) :
        (fun i => (Fin.cons a r : Fin (n + 1) → Bool) i ||
          (Fin.cons b s : Fin (n + 1) → Bool) i) =
          Fin.cons (a || b) (fun i => r i || s i) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    rw [bernoulliAverage_cons p]
    simp_rw [bernoulliAverage_cons (n := n) q, hc]
    simp only [Bool.or_false, Bool.or_true]
    rw [bernoulliAverage_linear, bernoulliAverage_linear,
      ih (fun x => f (Fin.cons false x)), ih (fun x => f (Fin.cons true x)),
      bernoulliAverage_cons]
    ring

theorem bernoulliAverage_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p a : ℝ) (f : (ι → Bool) → ℝ) :
    bernoulliAverage p (fun x => a * f x) = a * bernoulliAverage p f := by
  simpa using bernoulliAverage_linear p a 0 f f

/-- The probability of a set of masks is between zero and one. -/
theorem bernoulliAverage_indicator_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Set (ι → Bool)) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    0 ≤ bernoulliAverage p (A.indicator 1) ∧ bernoulliAverage p (A.indicator 1) ≤ 1 := by
  constructor
  · simpa only [bernoulliAverage_const] using bernoulliAverage_mono hp hp' (f := fun _ => 0)
      (g := A.indicator 1) fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  · simpa only [bernoulliAverage_const] using bernoulliAverage_mono hp hp' (f := A.indicator 1)
      (g := fun _ => 1) fun x => Set.indicator_le_self' (fun _ _ => zero_le_one) x

/-- The indicator of a lower set is antitone. -/
theorem _root_.IsLowerSet.antitone_indicator_one {α : Type*} [Preorder α] {A : Set α}
    (hA : IsLowerSet A) : Antitone (A.indicator (1 : α → ℝ)) := by
  intro r s hrs
  by_cases hs : s ∈ A
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (hA hrs hs)]
    exact le_rfl
  · rw [Set.indicator_of_notMem hs]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) r

/-- The union of independent masks of rates `p` and `q` lies in a lower set only if both masks do,
so the probability of a lower set at rate `p + q - p q` is at most the product of its
probabilities at rates `p` and `q`. -/
theorem bernoulliAverage_lowerSet_union {n : ℕ} {A : Set (Fin n → Bool)} (hA : IsLowerSet A)
    {p q : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (hq : 0 ≤ q) (hq' : q ≤ 1) :
    bernoulliAverage (p + q - p * q) (A.indicator 1) ≤
      bernoulliAverage p (A.indicator 1) * bernoulliAverage q (A.indicator 1) := by
  have hpoint (r s : Fin n → Bool) :
      A.indicator (1 : (Fin n → Bool) → ℝ) (fun i => r i || s i) ≤
        A.indicator 1 r * A.indicator 1 s := by
    by_cases hu : (fun i => r i || s i) ∈ A
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (hA (fun i => Bool.left_le_or _ _) hu),
        Set.indicator_of_mem (hA (fun i => Bool.right_le_or _ _) hu)]
      simp
    · rw [Set.indicator_of_notMem hu]
      exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) r)
        (Set.indicator_nonneg (fun _ _ => zero_le_one) s)
  rw [← bernoulliAverage_union]
  calc
    _ ≤ bernoulliAverage p (fun r => bernoulliAverage q (fun s =>
        A.indicator (1 : (Fin n → Bool) → ℝ) r * A.indicator 1 s)) :=
      bernoulliAverage_mono hp hp' fun r => bernoulliAverage_mono hq hq' (hpoint r)
    _ = _ := by
      simp_rw [bernoulliAverage_mul]
      simp only [bernoulliAverage, ← mul_assoc, sum_mul]

/-- **Transference for lower sets**, with an integer number of repetitions: if `h` independent
masks of rate `p` have a union of rate at most `q` (`h p ≤ q`), then the probability of a lower set
at rate `q` is at most the `h`-th power of its probability at rate `p`. -/
theorem bernoulliAverage_lowerSet_pow_le {n : ℕ} {A : Set (Fin n → Bool)} (hA : IsLowerSet A)
    {p q : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (hq : q ≤ 1) (h : ℕ) (hh : (h : ℝ) * p ≤ q) :
    bernoulliAverage q (A.indicator 1) ≤ bernoulliAverage p (A.indicator 1) ^ h := by
  let u (j : ℕ) : ℝ := 1 - (1 - p) ^ j
  have hu (j : ℕ) : 0 ≤ u j ∧ u j ≤ 1 := by
    constructor
    · exact sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr hp') (by linarith))
    · dsimp [u]
      linarith [pow_nonneg (sub_nonneg.mpr hp') j]
  have hs (j : ℕ) : u (j + 1) = p + u j - p * u j := by
    dsimp [u]
    rw [pow_succ]
    ring
  have hb (j : ℕ) : u j ≤ (j : ℝ) * p := by
    induction j with
    | zero => simp [u]
    | succ j ih =>
      rw [hs, Nat.cast_succ]
      nlinarith [mul_nonneg hp (hu j).1]
  have hi (j : ℕ) :
      bernoulliAverage (u j) (A.indicator 1) ≤ bernoulliAverage p (A.indicator 1) ^ j := by
    induction j with
    | zero =>
      simpa only [pow_zero] using (bernoulliAverage_indicator_bounds A (hu 0).1 (hu 0).2).2
    | succ j ih =>
      rw [hs, pow_succ']
      exact (bernoulliAverage_lowerSet_union hA hp hp' (hu j).1 (hu j).2).trans
        (mul_le_mul_of_nonneg_left ih (bernoulliAverage_indicator_bounds A hp hp').1)
  exact (bernoulliAverage_bias_antitone hA.antitone_indicator_one
    (hu h).1 ((hb h).trans hh) hq).trans (hi h)

/-- Sampling at rate zero selects the empty coordinate set. -/
theorem bernoulliAverage_zero {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    bernoulliAverage 0 f = f (fun _ => false) := by
  induction n with
  | zero =>
    have he : f = fun _ => f (fun _ => false) :=
      funext fun _ => congrArg f (Subsingleton.elim _ _)
    rw [he, bernoulliAverage_const]
  | succ n ih =>
    rw [bernoulliAverage_cons]
    simp only [sub_zero, one_mul, zero_mul, add_zero, ih]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- **Transference for lower sets** at a small rate `r ≤ 1 / 20`: the probability of a nonempty
lower set at rate `r` is at least its probability at rate `1 / 4` to the power `5 r`, as in the
proof of [Korten, Lemma 10][Korten2026]. Nonemptiness covers `r = 0`, where the right side is
one. -/
theorem bernoulliAverage_lowerSet_transfer {n : ℕ} {A : Set (Fin n → Bool)}
    (hA : IsLowerSet A) (hA' : A.Nonempty) {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1 / 20) :
    bernoulliAverage (1 / 4) (A.indicator 1) ^ (5 * r) ≤ bernoulliAverage r (A.indicator 1) := by
  rcases hr.eq_or_lt with rfl | hr
  · obtain ⟨s, hs⟩ := hA'
    have hz : (fun _ => false) ∈ A := hA (fun i => Bool.false_le (s i)) hs
    simp [bernoulliAverage_zero, Set.indicator_of_mem hz]
  let h := ⌊1 / (4 * r)⌋₊
  have hr1 : r ≤ 1 := by linarith
  have hmul : (1 / (4 * r)) * r = 1 / 4 := by field_simp
  have hupper : (h : ℝ) * r ≤ 1 / 4 := by
    have hf := mul_le_mul_of_nonneg_right (Nat.floor_le (show 0 ≤ 1 / (4 * r) by positivity)) hr.le
    rwa [hmul] at hf
  have hlower : 1 ≤ (h : ℝ) * (5 * r) := by
    have hf := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (1 / (4 * r))) hr
    rw [hmul] at hf
    dsimp [h]
    nlinarith
  have hpos : 0 < (h : ℝ) := by
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (by positivity : 0 ≤ 5 * r)
    linarith
  have hinv : (h : ℝ)⁻¹ ≤ 5 * r := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hpos).mpr (by nlinarith)
  have hbase := bernoulliAverage_indicator_bounds A
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)
  calc
    _ ≤ bernoulliAverage (1 / 4) (A.indicator 1) ^ (h : ℝ)⁻¹ :=
      Real.rpow_le_rpow_of_exponent_ge' hbase.1 hbase.2 (by positivity) hinv
    _ ≤ _ := by
      apply (Real.rpow_inv_le_iff_of_pos hbase.1
        (bernoulliAverage_indicator_bounds A hr.le hr1).1 hpos).mpr
      rw [Real.rpow_natCast]
      exact bernoulliAverage_lowerSet_pow_le hA hr.le hr1 (by norm_num) h hupper

theorem bernoulliAverage_expect_comm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : Type*} (A : Finset α)
    (p : ℝ) (f : (ι → Bool) → α → ℝ) :
    bernoulliAverage p (fun s => 𝔼 x ∈ A, f s x) =
      𝔼 x ∈ A, bernoulliAverage p (fun s => f s x) := by
  unfold bernoulliAverage
  simp_rw [mul_expect]
  exact (expect_sum_comm A univ _).symm

theorem bernoulliAverage_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (f g : (ι → Bool) → ℝ) :
    bernoulliAverage p (fun s => f s - g s) = bernoulliAverage p f - bernoulliAverage p g := by
  simpa only [one_mul, neg_one_mul, sub_eq_add_neg] using
    bernoulliAverage_linear p 1 (-1) f g

/-- A coordinate is selected with probability `p`. -/
theorem bernoulliAverage_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) (i : ι) :
    bernoulliAverage p (fun s : ι → Bool => if s i then (1 : ℝ) else 0) = p := by
  let e := Equiv.piSplitAt i (fun _ : ι => Bool)
  have hw (s : ι → Bool) : bernoulliWeight p s =
      (if s i then p else 1 - p) * bernoulliWeight p (fun j : {j // j ≠ i} => s j) := by
    exact Fintype.prod_eq_mul_prod_subtype_ne (fun j => if s j then p else 1 - p) i
  unfold bernoulliAverage
  rw [← e.symm.sum_comp (fun s => bernoulliWeight p s * (if s i then (1 : ℝ) else 0))]
  simp_rw [hw]
  have hleft (z : Bool × ({j // j ≠ i} → Bool)) : e.symm z i = z.1 := by
    simp [e, Equiv.piSplitAt]
  have hright (z : Bool × ({j // j ≠ i} → Bool)) :
      (fun j : {j // j ≠ i} => e.symm z j) = z.2 := by
    funext j
    simp [e, Equiv.piSplitAt, j.property]
  simp_rw [hleft, hright]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Bool.false_eq_true, ite_true, ite_false, mul_one, mul_zero,
    sum_const_zero, add_zero, ← mul_sum]
  have hs : (∑ s : {j // j ≠ i} → Bool, bernoulliWeight p s) = 1 := by
    simpa [bernoulliAverage] using bernoulliAverage_const (ι := {j // j ≠ i}) p 1
  rw [hs, mul_one]

/-- A mask is nonempty with probability `1 - (1 - p) ^ |ι|`. -/
theorem bernoulliAverage_nonempty {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) :
    bernoulliAverage p (fun P : ι → Bool => if ∃ i, P i = true then (1 : ℝ) else 0) =
      1 - (1 - p) ^ Fintype.card ι := by
  have he (P : ι → Bool) : (if ∃ i, P i = true then (1 : ℝ) else 0) =
      1 - (if P = (fun _ => false) then 1 else 0) := by
    by_cases h : ∃ i, P i = true
    · have hn : P ≠ fun _ => false := by
        intro hn
        obtain ⟨i, hi⟩ := h
        simp [hn] at hi
      simp [h, hn]
    · have hn : P = fun _ => false := by
        funext i
        have hi : P i ≠ true := fun hi => h ⟨i, hi⟩
        simpa using hi
      simp [hn]
  simp_rw [he, bernoulliAverage_sub, bernoulliAverage_const]
  congr 1
  simp [bernoulliAverage, bernoulliWeight]

/-- A form of Bernoulli's inequality: `(1 - p) ^ n (1 + n p) ≤ 1` for `p ≤ 1`. It bounds the
probability `(1 - p) ^ n` that a mask of rate `p` misses `n` coordinates. -/
theorem _root_.one_sub_pow_mul_one_add_mul_le_one {p : ℝ} (hp : p ≤ 1) (n : ℕ) :
    (1 - p) ^ n * (1 + (n : ℝ) * p) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ]
    have hnon := mul_nonneg (pow_nonneg (sub_nonneg.mpr hp) n)
      (mul_nonneg (show (0 : ℝ) ≤ n + 1 by positivity) (sq_nonneg p))
    nlinarith

end Cslib.BooleanAnalysis
