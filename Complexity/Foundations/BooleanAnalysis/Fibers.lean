/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.Bernoulli
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Logic.Equiv.Prod

/-!
# Korten's conditional-fiber entropy lemma

Lemma 4 of [Korten2026].

For a nonempty cube subset `X`, conditioning on the coordinates outside `s`
does not increase its average uniform min-entropy deficit. The fiber is
represented on the selected-coordinate cube, and `card_coordinateFiber`
identifies it with the full-cube set of points agreeing outside `s`.

`coordinateFiber_good_probability` is the `63/64` consequence used in the
mirror-set argument. The uniform-mass API connects a deficit bound to the
pointwise probability bound required by the light-patterns lemma.
-/

@[expose] public section

/-! ### Uniform entropy deficits and coordinate fibers

Definitions for Lemma 4 and the mirror-set argument in [Korten2026].

A fiber is a set of patterns on the free coordinates, so its deficit is
measured in that smaller cube. Logarithms in deficits are base two.
-/


namespace Cslib.BooleanAnalysis

open Finset
open scoped BigOperators

/-- Uniform probability mass on a nonempty finite set; zero off the set.
The empty set gives the zero mass function. -/
noncomputable def uniformMass {α : Type*} [DecidableEq α] (X : Finset α) (x : α) : ℝ :=
  if x ∈ X then 1 / X.card else 0

/-- Min-entropy deficit of the uniform distribution on a nonempty Boolean
cube subset. The real formula takes value `card ι` at the empty set because
`Real.logb 2 0 = 0`; entropy interpretations require nonemptiness. -/
noncomputable def uniformDeficit {ι : Type*} [Fintype ι]
    (X : Finset (ι → Bool)) : ℝ :=
  Fintype.card ι - Real.logb 2 X.card

/-- Insert a pattern on selected coordinates, retaining `x` elsewhere. -/
def completePattern {ι : Type*} (s x : ι → Bool)
    (z : {i // s i = true} → Bool) : ι → Bool :=
  fun i => if h : s i = true then z ⟨i, h⟩ else x i

/-- The fiber of `X` over the bits of `x` outside `s`, represented on the
selected-coordinate cube. This is Korten's `X_{x,S}` inside its own subcube. -/
noncomputable def coordinateFiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Finset (ι → Bool)) (s x : ι → Bool) : Finset ({i // s i = true} → Bool) :=
  univ.filter (fun z => completePattern s x z ∈ X)

/-- Replace selected coordinates of `x` by those of `y`. -/
def resample {ι : Type*} (s x y : ι → Bool) : ι → Bool :=
  fun i => if s i then y i else x i

/-- Fraction of the free-coordinate cube over `x` that belongs to `X`. -/
noncomputable def coordinateDensity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Finset (ι → Bool)) (s x : ι → Bool) : ℝ :=
  (coordinateFiber X s x).card / (2 : ℝ) ^ Fintype.card {i // s i = true}

/-- Density of uniform mass relative to the uniform Boolean cube. Its
uniform cube expectation is one when `X` is nonempty. -/
noncomputable def uniformDensity {ι : Type*} [Fintype ι]
    (X : Finset (ι → Bool)) (x : ι → Bool) : ℝ :=
  (2 : ℝ) ^ Fintype.card ι * uniformMass X x

end Cslib.BooleanAnalysis

/-! ### Conditional-fiber entropy estimates

A finite log-sum inequality proves Korten's entropy lemma (Lemma 4).
A bijection with the full-cube fiber verifies the dimension convention.
Markov's inequality gives the `63/64` good-fiber estimate needed in the
improved mirror-set argument.
-/


namespace Cslib.BooleanAnalysis

open Finset
open scoped BigOperators

theorem mul_log_tangent {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) :
    a * Real.log c + a - c ≤ a * Real.log a := by
  rcases ha.eq_or_lt with rfl | ha
  · simp only [zero_mul, zero_add, zero_sub]
    linarith
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hc ha)) ha.le
  rw [Real.log_div hc.ne' ha.ne'] at h
  have he : a * (c / a) = c := by field_simp
  nlinarith

theorem sum_mul_log_ge {β : Type*} [Fintype β] [Nonempty β]
    {m : β → ℝ} (hm : ∀ b, 0 ≤ m b) (hpos : 0 < ∑ b, m b) :
    (∑ b, m b) * Real.log ((∑ b, m b) / Fintype.card β) ≤
      ∑ b, m b * Real.log (m b) := by
  let c := (∑ b, m b) / Fintype.card β
  have hB : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have hc : 0 < c := div_pos hpos hB
  have h := sum_le_sum (s := univ) (fun b _ => mul_log_tangent (hm b) hc)
  simp only [sum_sub_distrib, sum_add_distrib, ← sum_mul, sum_const, card_univ,
    nsmul_eq_mul] at h
  have he : (Fintype.card β : ℝ) * c = ∑ b, m b := by dsimp [c]; field_simp
  rw [he] at h
  simpa only [add_sub_cancel_right] using h

open scoped Classical in
theorem expect_log_card_fiber {α β : Type*} [Fintype β] [Nonempty β]
    (X : Finset α) (hX : X.Nonempty) (g : α → β) :
    Real.log X.card - Real.log (Fintype.card β) ≤
      𝔼 x ∈ X, Real.log (X.filter (fun y => g y = g x)).card := by
  let m : β → ℝ := fun b => (X.filter fun x => g x = b).card
  have hsum : (∑ b, m b) = (X.card : ℝ) := by
    dsimp [m]
    exact_mod_cast (card_eq_sum_card_fiberwise (s := X) (t := univ)
      (f := g) (by intro x hx; exact mem_univ _) ).symm
  have hN : (0 : ℝ) < X.card := by exact_mod_cast card_pos.mpr hX
  have hB : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have h := sum_mul_log_ge (m := m) (by intro b; dsimp [m]; positivity) (by simpa [hsum])
  rw [hsum, Real.log_div hN.ne' hB.ne'] at h
  have he : (∑ x ∈ X, Real.log (X.filter (fun y => g y = g x)).card) =
      ∑ b, m b * Real.log (m b) := by
    rw [← sum_fiberwise' X g (fun b => Real.log (m b))]
    simp only [sum_const, nsmul_eq_mul]
    rfl
  rw [expect_eq_sum_div_card, he]
  exact (le_div_iff₀ hN).mpr (by nlinarith)

/-- The free-coordinate fiber counts exactly the full assignments in `X`
whose unselected coordinates agree with `x`. -/
theorem card_coordinateFiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Finset (ι → Bool)) (s x : ι → Bool) :
    (coordinateFiber X s x).card =
      (X.filter fun y => (fun i : {i // s i ≠ true} => y i) =
        (fun i : {i // s i ≠ true} => x i)).card := by
  refine card_bij (fun z _ => completePattern s x z) ?_ ?_ ?_
  · intro z hz
    refine mem_filter.mpr ⟨(mem_filter.mp hz).2, ?_⟩
    funext i
    simp [completePattern, i.property]
  · intro z hz w hw he
    funext i
    have h := congrFun he i
    simpa [completePattern, i.property] using h
  · intro y hy
    have he : completePattern s x (fun i => y i) = y := by
      funext i
      by_cases hi : s i = true
      · simp [completePattern, hi]
      · have h := congrFun (mem_filter.mp hy).2 ⟨i, hi⟩
        simpa [completePattern, hi] using h.symm
    refine ⟨fun i => y i, ?_, he⟩
    exact mem_filter.mpr ⟨mem_univ _, by rw [he]; exact (mem_filter.mp hy).1⟩

/-- Conditioning at a point of `X` leaves a nonempty fiber. -/
theorem coordinateFiber_nonempty {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Finset (ι → Bool)} (s : ι → Bool) {x : ι → Bool} (hx : x ∈ X) :
    (coordinateFiber X s x).Nonempty := by
  refine ⟨fun i => x i, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
  have he : completePattern s x (fun i => x i) = x := by
    funext i
    simp [completePattern]
  rwa [he]

/-- Uniform deficits are nonnegative. For the empty set this follows from
the documented real-logarithm convention. -/
theorem uniformDeficit_nonneg {ι : Type*} [Fintype ι]
    (X : Finset (ι → Bool)) : 0 ≤ uniformDeficit X := by
  classical
  by_cases hx : X.Nonempty
  · have hpos : (0 : ℝ) < X.card := by exact_mod_cast card_pos.mpr hx
    have hc : (X.card : ℝ) ≤ (2 : ℝ) ^ (Fintype.card ι : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast (show X.card ≤ 2 ^ Fintype.card ι by simpa using card_le_univ X)
    have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hpos).mpr hc
    exact sub_nonneg.mpr h
  · rw [not_nonempty_iff_eq_empty.mp hx]
    simp [uniformDeficit]

/-- Korten's entropy lemma (Lemma 4): conditioning on the unselected bits
does not increase the average deficit in the selected-coordinate cube. -/
theorem expect_uniformDeficit_coordinateFiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Finset (ι → Bool)) (hX : X.Nonempty) (s : ι → Bool) :
    (𝔼 x ∈ X, uniformDeficit (coordinateFiber X s x)) ≤ uniformDeficit X := by
  have h := expect_log_card_fiber X hX (fun x (i : {i // s i ≠ true}) => x i)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : (Fintype.card {i // s i = true} : ℝ) +
      Fintype.card {i // s i ≠ true} = Fintype.card ι := by
    have hle := Fintype.card_subtype_le (fun i => s i = true)
    have he : Fintype.card {i // s i = true} +
        Fintype.card {i // s i ≠ true} = Fintype.card ι := by
      rw [Fintype.card_subtype_compl]
      omega
    exact_mod_cast he
  have he : (𝔼 x ∈ X, uniformDeficit (coordinateFiber X s x)) =
      Fintype.card {i // s i = true} -
        (𝔼 x ∈ X, Real.log (X.filter fun y =>
          (fun i : {i // s i ≠ true} => y i) =
          (fun i : {i // s i ≠ true} => x i)).card) / Real.log 2 := by
    simp only [uniformDeficit, Real.logb, expect_sub_distrib, ← expect_div,
      expect_const hX, card_coordinateFiber]
  rw [he]
  have hcard : Real.log (Fintype.card ({i // s i ≠ true} → Bool)) =
      Fintype.card {i // s i ≠ true} * Real.log 2 := by
    simp
  rw [hcard] at h
  dsimp [uniformDeficit, Real.logb]
  have hd := div_le_div_of_nonneg_right h hl.le
  simp only [sub_div, mul_div_cancel_right₀ _ hl.ne', ne_eq] at hd
  linarith only [hc, hd]

/-- For every fixed set of free coordinates, a uniform point of `X` yields
a fiber of deficit at most `64*k` with probability at least `63/64`. -/
theorem coordinateFiber_good_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Finset (ι → Bool)) (hX : X.Nonempty) (s : ι → Bool)
    {k : ℝ} (hk : 0 < k) (hdef : uniformDeficit X ≤ k) :
    63 / 64 ≤ 𝔼 x ∈ X, if uniformDeficit (coordinateFiber X s x) ≤ 64 * k then
      (1 : ℝ) else 0 := by
  have hp : 0 < 64 * k := by positivity
  have hpoint (x : ι → Bool) :
      1 ≤ (if uniformDeficit (coordinateFiber X s x) ≤ 64 * k then (1 : ℝ) else 0) +
        uniformDeficit (coordinateFiber X s x) / (64 * k) := by
    by_cases hx : uniformDeficit (coordinateFiber X s x) ≤ 64 * k
    · rw [ite_eq_left hx]
      have := div_nonneg (uniformDeficit_nonneg (coordinateFiber X s x)) hp.le
      linarith
    · rw [ite_eq_right hx, zero_add]
      exact (le_div_iff₀ hp).mpr (by linarith)
  have h := expect_le_expect (s := X) (fun x _ => hpoint x)
  rw [expect_const hX, expect_add_distrib, ← expect_div] at h
  have hd := div_le_div_of_nonneg_right
    ((expect_uniformDeficit_coordinateFiber X hX s).trans hdef) hp.le
  have he : k / (64 * k) = 1 / 64 := by field_simp
  rw [he] at hd
  linarith

/-- Uniform mass on a nonempty finite set sums to one. -/
theorem sum_uniformMass {α : Type*} [Fintype α] [DecidableEq α]
    {X : Finset α} (hX : X.Nonempty) : (∑ x, uniformMass X x) = 1 := by
  have hp : (X.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hX).ne'
  simp [uniformMass, hp]

/-- Summing against uniform mass agrees with the finite-set expectation. -/
theorem sum_uniformMass_mul {α : Type*} [Fintype α] [DecidableEq α]
    (X : Finset α) (f : α → ℝ) : (∑ x, uniformMass X x * f x) = 𝔼 x ∈ X, f x := by
  simp only [uniformMass, ite_mul, zero_mul]
  rw [sum_ite, sum_const_zero, add_zero]
  simp only [filter_mem_eq_inter, univ_inter, ← mul_sum, expect_eq_sum_div_card]
  ring

/-- A nonempty subset has cardinality `2^(dimension - deficit)`. -/
theorem card_eq_rpow_sub_uniformDeficit {ι : Type*} [Fintype ι] {X : Finset (ι → Bool)}
    (hX : X.Nonempty) : (X.card : ℝ) = (2 : ℝ) ^ ((Fintype.card ι : ℝ) - uniformDeficit X) := by
  have hp : (0 : ℝ) < X.card := by exact_mod_cast card_pos.mpr hX
  dsimp [uniformDeficit]
  rw [sub_sub_cancel, Real.rpow_logb (by norm_num) (by norm_num) hp]

/-- A deficit bound is equivalent to the corresponding density lower bound
when the subset is nonempty. -/
theorem uniformDeficit_le_iff {ι : Type*} [Fintype ι] {X : Finset (ι → Bool)}
    (hX : X.Nonempty) {k : ℝ} : uniformDeficit X ≤ k ↔
      (2 : ℝ) ^ ((Fintype.card ι : ℝ) - k) ≤ X.card := by
  have he := Real.rpow_le_rpow_left_iff (x := (2 : ℝ))
    (y := (Fintype.card ι : ℝ) - k)
    (z := (Fintype.card ι : ℝ) - uniformDeficit X) (by norm_num)
  rw [← card_eq_rpow_sub_uniformDeficit hX] at he
  exact he.trans (by constructor <;> intro h <;> linarith) |>.symm

/-- A uniform deficit bound implies the light-patterns lemma's pointwise
probability-mass hypothesis. -/
theorem uniformMass_le_rpow {ι : Type*} [Fintype ι]
    {X : Finset (ι → Bool)} (hX : X.Nonempty) {k : ℝ} (hdef : uniformDeficit X ≤ k)
    (x : ι → Bool) : uniformMass X x ≤ (2 : ℝ) ^ (k - Fintype.card ι) := by
  calc
    _ ≤ 1 / (X.card : ℝ) := by
      unfold uniformMass
      split_ifs
      · exact le_rfl
      · positivity
    _ = (2 : ℝ) ^ (uniformDeficit X - Fintype.card ι) := by
      rw [card_eq_rpow_sub_uniformDeficit hX, one_div,
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

end Cslib.BooleanAnalysis

/-! ### Density and coordinate-resampling identities

Uniform cube densities normalize probability masses. Completing a selected
pattern identifies the fraction of a fiber with its resampling probability.
These identities connect Korten's entropy and light-patterns lemmas.
-/


namespace Cslib.BooleanAnalysis

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Uniform resampling on the whole cube restricts to uniform sampling on
any fixed selected-coordinate subtype. -/
theorem expect_restrict_coordinates (s : ι → Bool) (f : ({i // s i = true} → Bool) → ℝ) :
    (𝔼 x : ι → Bool, f (fun i => x i)) = 𝔼 x, f x := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => s i = true) (fun _ => Bool)
  rw [← Fintype.expect_equiv e.symm (fun z => f (fun i => e.symm z i)) _
    (fun _ => rfl)]
  rw [← univ_product_univ, expect_product]
  have he (a : {i // s i = true} → Bool) (b : {i // s i ≠ true} → Bool) :
      (fun i : {i // s i = true} => e.symm (a, b) i) = a := by
    funext i
    simp [e, Equiv.piEquivPiSubtypeProd, i.property]
  simp_rw [he, Fintype.expect_const]

omit [Fintype ι] [DecidableEq ι] in
/-- Whole-cube resampling completes the restriction of the sampled point. -/
theorem resample_eq_completePattern (s x y : ι → Bool) :
    resample s x y = completePattern s x (fun i => y i) := by
  funext i
  by_cases hi : s i = true <;> simp [resample, completePattern, hi]

/-- The fraction of a fiber is the probability that coordinate resampling
lands in the set. -/
theorem coordinateDensity_eq_expect (X : Finset (ι → Bool)) (s x : ι → Bool) :
    coordinateDensity X s x = 𝔼 y, if resample s x y ∈ X then (1 : ℝ) else 0 := by
  simp_rw [resample_eq_completePattern]
  rw [expect_restrict_coordinates s
    (fun z => if completePattern s x z ∈ X then (1 : ℝ) else 0)]
  simp [coordinateDensity, coordinateFiber, Fintype.expect_eq_sum_div_card]

/-- Normalization of the density of a nonempty finite cube subset. -/
theorem expect_uniformDensity {X : Finset (ι → Bool)} (hX : X.Nonempty) :
    (𝔼 x, uniformDensity X x) = 1 := by
  unfold uniformDensity
  rw [Fintype.expect_eq_sum_div_card, ← mul_sum, sum_uniformMass hX]
  simp

omit [DecidableEq ι] in
/-- Entropy deficit bounds the normalized density pointwise. -/
theorem uniformDensity_le_rpow {X : Finset (ι → Bool)} (hX : X.Nonempty)
    {k : ℝ} (hk : uniformDeficit X ≤ k) (x : ι → Bool) :
    uniformDensity X x ≤ (2 : ℝ) ^ k := by
  have hproduct : (2 : ℝ) ^ Fintype.card ι * (2 : ℝ) ^ (k - Fintype.card ι) =
      (2 : ℝ) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  exact (mul_le_mul_of_nonneg_left (uniformMass_le_rpow hX hk x) (by positivity)).trans_eq
    hproduct

omit [DecidableEq ι] in
/-- The density is `2^deficit` on the nonempty set and zero elsewhere. -/
theorem uniformDensity_eq_deficit {X : Finset (ι → Bool)} (hX : X.Nonempty)
    (z : ι → Bool) :
    uniformDensity X z = (2 : ℝ) ^ uniformDeficit X * (if z ∈ X then 1 else 0) := by
  by_cases hz : z ∈ X
  · simp only [uniformDensity, uniformMass, ite_eq_left hz, mul_one, mul_one_div]
    rw [card_eq_rpow_sub_uniformDeficit hX, ← Real.rpow_natCast,
      ← Real.rpow_sub (by norm_num)]
    congr 1
    ring
  · simp [uniformDensity, uniformMass, hz]

end Cslib.BooleanAnalysis



namespace Cslib.BooleanAnalysis

open Finset
open scoped BigOperators

/-- Uniform masses are nonnegative, including for the empty set. -/
theorem uniformMass_nonneg {α : Type*} [DecidableEq α] (X : Finset α) (x : α) :
    0 ≤ uniformMass X x := by
  unfold uniformMass
  split_ifs <;> positivity

/-- Fiber densities are nonnegative, including for empty fibers. -/
theorem coordinateDensity_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Finset (ι → Bool)) (s x : ι → Bool) : 0 ≤ coordinateDensity X s x := by
  unfold coordinateDensity
  positivity

/-- Uniform densities are nonnegative, including for the empty set. -/
theorem uniformDensity_nonneg {ι : Type*} [Fintype ι]
    (X : Finset (ι → Bool)) (x : ι → Bool) : 0 ≤ uniformDensity X x :=
  mul_nonneg (by positivity) (uniformMass_nonneg X x)

end Cslib.BooleanAnalysis
