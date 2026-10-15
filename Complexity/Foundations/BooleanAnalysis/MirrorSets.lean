/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.Fibers
public import Complexity.Foundations.BooleanAnalysis.CoordinateSampling
public import Complexity.Foundations.BooleanAnalysis.LightPatterns
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Korten's mirror sets

A point `x` is a `(p, k)`-limit of a set `Y` of masks (`IsDensityLimit`) when, with probability at
least `3 / 4` over a random mask `P` of rate `p`, the fiber of `Y` over the coordinates of `x`
outside `P` has density at least `2 ^ (-k)`. If every point of a set `X` of deficit at most `k`
is a `(p, k)`-limit of `Y`, then `Y` has a nonempty subset of deficit at most `2 k + 2` all of
whose points are `(32768 k p, 194 k)`-limits of `X` (`exists_mirror_set`). This is Korten's
mirror-set argument [Korten, Sections 3 and 4][Korten2026], with the light-patterns lemma, the
entropy lemma for fibers and the conditional sampling law, and with a guiding distribution in
place of fixed-size guiding sets.

## Main definitions

* `Cslib.BooleanAnalysis.IsDensityLimit`: density limits [Korten, Definition 2][Korten2026].
* `Cslib.BooleanAnalysis.guidingDensity`, `Cslib.BooleanAnalysis.guidedAverage`: the guiding
  distribution.

## Main results

* `Cslib.BooleanAnalysis.exists_mirror_set`: the mirror-set lemma.

## References

* [O. Korten, *Top-Down Lower Bounds for All Depths*][Korten2026]
-/

@[expose] public section

namespace Cslib.BooleanAnalysis

open Finset
open scoped BigOperators

/-- A `(p,k)`-limit point of `Y`: with probability at least `3/4`, the
rate-`p` coordinate fiber over `x` has density at least `2^(-k)` in `Y`. -/
def IsDensityLimit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : Finset (ι → Bool)) (p k : ℝ) (x : ι → Bool) : Prop :=
  3 / 4 ≤ bernoulliAverage p
    (fun P => if (2 : ℝ) ^ (-k) ≤ coordinateDensity Y P x then (1 : ℝ) else 0)

/-! ### Completion density in Korten's improved mirror-set argument

Apply the entropy lemma and improved light-patterns lemma inside the sampled
union fiber. The exact conditional sampling law yields the `31/32` estimate
for the fraction of first-stage modifications with low completion density.

Source: [Korten, Sections 3--4][Korten2026]. The explicit constants here are `q = 32768*k*p` and
completion deficit `194*k`. -/

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem projectionAverage_const_mul (a : ℝ) (f : (ι → Bool) → ℝ) (s x : ι → Bool) :
    projectionAverage (fun y => a * f y) s x = a * projectionAverage f s x := by
  exact (mul_expect _ _ _).symm

theorem projectionAverage_fiber (f : (ι → Bool) → ℝ) (s x : ι → Bool)
    (R u : {i // s i = true} → Bool) :
    projectionAverage (fun z => f (completePattern s x z)) R u =
      projectionAverage f (fun i => if h : s i = true then R ⟨i, h⟩ else true)
        (completePattern s x u) := by
  unfold projectionAverage
  rw [← expect_restrict_coordinates s]
  apply expect_congr rfl
  intro y _
  apply congrArg f
  funext i
  by_cases hs : s i = true
  · simp only [completePattern, dite_eq_left hs]
  · simp [completePattern, hs]

theorem coordinateDensity_eq_projection (X : Finset (ι → Bool)) (s x : ι → Bool) :
    coordinateDensity X s x =
      projectionAverage (fun y => if y ∈ X then 1 else 0) (fun i => !s i) x := by
  rw [coordinateDensity_eq_expect]
  unfold projectionAverage
  apply expect_congr rfl
  intro y _
  apply congrArg (fun t => if t ∈ X then (1 : ℝ) else 0)
  funext i
  cases hs : s i <;> simp [resample, hs]

theorem projectionAverage_uniformDensity_fiber (X : Finset (ι → Bool)) (s x : ι → Bool)
    (hX : (coordinateFiber X s x).Nonempty) (R u : {i // s i = true} → Bool) :
    projectionAverage (uniformDensity (coordinateFiber X s x)) R u =
      (2 : ℝ) ^ uniformDeficit (coordinateFiber X s x) *
        coordinateDensity X (fun i => if h : s i = true then !R ⟨i, h⟩ else false)
          (completePattern s x u) := by
  have he : uniformDensity (coordinateFiber X s x) = fun z =>
      (2 : ℝ) ^ uniformDeficit (coordinateFiber X s x) *
        (if completePattern s x z ∈ X then 1 else 0) := by
    funext z
    rw [uniformDensity_eq_deficit hX]
    simp only [coordinateFiber, mem_filter, mem_univ, true_and]
  rw [he, projectionAverage_const_mul,
    projectionAverage_fiber (fun y => if y ∈ X then 1 else 0),
    coordinateDensity_eq_projection]
  congr 2
  funext i
  by_cases hs : s i = true <;> simp [hs]

theorem expect_coordinateMarginal_comp (f : (ι → Bool) → ℝ) (s : ι → Bool) (g : ℝ → ℝ) :
    (𝔼 x, g (projectionAverage f s x)) = 𝔼 z, g (coordinateMarginal f s z) := by
  simp_rw [projectionAverage_eq_coordinateMarginal]
  exact expect_restrict_coordinates s (fun z => g (coordinateMarginal f s z))

theorem coordinateFiber_light_patterns (X : Finset (ι → Bool)) (hX : X.Nonempty)
    (s : ι → Bool) {k r : ℝ} (hk : 1 ≤ k) (hdef : uniformDeficit X ≤ k)
    (hr : 0 ≤ r) (hr' : r ≤ 1 / (32768 * k)) :
    31 / 32 ≤ 𝔼 x ∈ X, bernoulliAverage r (fun R =>
      if uniformDeficit (coordinateFiber X s x) ≤ 64 * k ∧
        (𝔼 z, if coordinateMarginal (uniformDensity (coordinateFiber X s x)) R z ≤
          (2 : ℝ) ^ (-128 * k - 2) then (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (-64 * k)
        then 1 else 0) := by
  have hpoint (x : ι → Bool) (hx : x ∈ X) :
      63 / 64 * (if uniformDeficit (coordinateFiber X s x) ≤ 64 * k then (1 : ℝ) else 0) ≤
        bernoulliAverage r (fun R =>
          if uniformDeficit (coordinateFiber X s x) ≤ 64 * k ∧
            (𝔼 z, if coordinateMarginal (uniformDensity (coordinateFiber X s x)) R z ≤
              (2 : ℝ) ^ (-128 * k - 2) then (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (-64 * k)
            then 1 else 0) := by
    by_cases hd : uniformDeficit (coordinateFiber X s x) ≤ 64 * k
    · simp only [hd, true_and, ite_true, mul_one]
      have hne := coordinateFiber_nonempty s hx
      have ht := bernoulliAverage_few_light_patterns_density
        (fun z => mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ Fintype.card {i // s i = true})
          (uniformMass_nonneg (coordinateFiber X s x) z))
        (expect_uniformDensity hne) (show (1 : ℝ) ≤ 64 * k by linarith)
        (uniformDensity_le_rpow hne hd) hr
        (show r ≤ 1 / (512 * (64 * k)) by convert hr' using 1; ring)
      rw [show (-2 : ℝ) * (64 * k) - 2 = -128 * k - 2 by ring,
        show -(64 * k) = -64 * k by ring] at ht
      exact ht
    · simp only [hd, false_and, ite_false, mul_zero, bernoulliAverage_const]
      exact le_rfl
  have hl := expect_le_expect (s := X) hpoint
  rw [← mul_expect] at hl
  have hg := coordinateFiber_good_probability X hX s (show 0 < k by linarith) hdef
  nlinarith

theorem fiber_completion_density (X : Finset (ι → Bool)) (s x : ι → Bool)
    (hX : (coordinateFiber X s x).Nonempty) (R : {i // s i = true} → Bool)
    {k : ℝ} (hk : 1 ≤ k) (hd : uniformDeficit (coordinateFiber X s x) ≤ 64 * k)
    (hl : (𝔼 z, if coordinateMarginal (uniformDensity (coordinateFiber X s x)) R z ≤
      (2 : ℝ) ^ (-128 * k - 2) then (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (-64 * k)) :
    (𝔼 u, if coordinateDensity X (fun i => if h : s i = true then !R ⟨i, h⟩ else false)
      (completePattern s x u) < (2 : ℝ) ^ (-194 * k) then (1 : ℝ) else 0) ≤
        (2 : ℝ) ^ (-k - 6) := by
  have hpoint (u : {i // s i = true} → Bool) :
      (if coordinateDensity X (fun i => if h : s i = true then !R ⟨i, h⟩ else false)
        (completePattern s x u) < (2 : ℝ) ^ (-194 * k) then (1 : ℝ) else 0) ≤
        if projectionAverage (uniformDensity (coordinateFiber X s x)) R u ≤
          (2 : ℝ) ^ (-128 * k - 2) then 1 else 0 := by
    split_ifs with hb hl
    · exact le_rfl
    · exfalso
      apply hl
      have he := projectionAverage_uniformDensity_fiber X s x hX R u
      rw [he]
      calc
        _ ≤ (2 : ℝ) ^ uniformDeficit (coordinateFiber X s x) * (2 : ℝ) ^ (-194 * k) :=
          mul_le_mul_of_nonneg_left hb.le (by positivity)
        _ = (2 : ℝ) ^ (uniformDeficit (coordinateFiber X s x) - 194 * k) := by
          rw [← Real.rpow_add (by norm_num)]
          congr 1
          ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    · positivity
    · exact le_rfl
  have he := expect_le_expect (s := univ) (fun u _ => hpoint u)
  rw [expect_coordinateMarginal_comp (uniformDensity (coordinateFiber X s x)) R
    (fun v => if v ≤ (2 : ℝ) ^ (-128 * k - 2) then (1 : ℝ) else 0)] at he
  exact (he.trans hl).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))

theorem coordinateDensity_resample_union (X : Finset (ι → Bool)) (P Q x y : ι → Bool) :
    coordinateDensity X Q (resample P x y) =
      coordinateDensity X Q (resample (fun i => P i || Q i) x y) := by
  rw [coordinateDensity_eq_expect, coordinateDensity_eq_expect]
  apply expect_congr rfl
  intro z _
  apply congrArg (fun t => if t ∈ X then (1 : ℝ) else 0)
  funext i
  cases hp : P i <;> cases hq : Q i <;> simp [resample, hp, hq]

theorem fiber_completion_density_union (X : Finset (ι → Bool)) (P Q x : ι → Bool)
    (hx : x ∈ X) {k : ℝ} (hk : 1 ≤ k)
    (hd : uniformDeficit (coordinateFiber X (fun i => P i || Q i) x) ≤ 64 * k)
    (hl : (𝔼 z, if coordinateMarginal
      (uniformDensity (coordinateFiber X (fun i => P i || Q i) x))
      (fun i => P i && !Q i) z ≤ (2 : ℝ) ^ (-128 * k - 2) then (1 : ℝ) else 0) ≤
        (2 : ℝ) ^ (-64 * k)) :
    (𝔼 y, if coordinateDensity X Q (resample P x y) < (2 : ℝ) ^ (-194 * k) then
      (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (-k - 6) := by
  let S := fun i => P i || Q i
  let R : {i // S i = true} → Bool := fun i => P i && !Q i
  have hq : (fun i => if h : S i = true then !R ⟨i, h⟩ else false) = Q := by
    funext i
    cases hp : P i <;> cases hq : Q i <;> simp [S, R, hp, hq]
  have ht := fiber_completion_density X S x (coordinateFiber_nonempty S hx) R hk hd hl
  rw [hq] at ht
  simp_rw [coordinateDensity_resample_union X P Q x, resample_eq_completePattern]
  rw [expect_restrict_coordinates S
    (fun u => if coordinateDensity X Q (completePattern S x u) <
      (2 : ℝ) ^ (-194 * k) then (1 : ℝ) else 0)]
  exact ht

private theorem bad_modifications_probability_of_rate (X : Finset (ι → Bool)) (hX : X.Nonempty)
    {k p q r : ℝ} (hk : 1 ≤ k) (hdef : uniformDeficit X ≤ k)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (hr : 0 ≤ r) (hr' : r ≤ 1 / (32768 * k))
    (hjoint : (p + q - p * q) * r = p * (1 - q)) :
    31 / 32 ≤ bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
      𝔼 x ∈ X, if (𝔼 y, if coordinateDensity X Q (resample P x y) <
        (2 : ℝ) ^ (-194 * k) then (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (-k - 6) then 1 else 0)) := by
  let good (S : ι → Bool) (R : {i // S i = true} → Bool) (x : ι → Bool) : Prop :=
    uniformDeficit (coordinateFiber X S x) ≤ 64 * k ∧
      (𝔼 z, if coordinateMarginal (uniformDensity (coordinateFiber X S x)) R z ≤
        (2 : ℝ) ^ (-128 * k - 2) then (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (-64 * k)
  have htheta : 0 ≤ p + q - p * q ∧ p + q - p * q ≤ 1 := by
    constructor
    · nlinarith [mul_nonneg hp (sub_nonneg.mpr hq')]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hp') (sub_nonneg.mpr hq')]
  have hg : 31 / 32 ≤ bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
      𝔼 x ∈ X, if good (fun i => P i || Q i) (fun i => P i && !Q i) x then
        (1 : ℝ) else 0)) := by
    rw [bernoulliAverage_union_difference_subtype p q r hjoint
      (fun S R => 𝔼 x ∈ X, if good S R x then (1 : ℝ) else 0)]
    have hs (S : ι → Bool) : 31 / 32 ≤ bernoulliAverage r (fun R =>
        𝔼 x ∈ X, if good S R x then (1 : ℝ) else 0) := by
      rw [bernoulliAverage_expect_comm]
      exact coordinateFiber_light_patterns X hX S hk hdef hr hr'
    simpa only [bernoulliAverage_const] using
      bernoulliAverage_mono htheta.1 htheta.2 hs
  refine hg.trans (bernoulliAverage_mono hp hp' fun P =>
    bernoulliAverage_mono hq hq' fun Q => expect_le_expect (s := X) fun x hx => ?_)
  by_cases hg : good (fun i => P i || Q i) (fun i => P i && !Q i) x
  · have hb := fiber_completion_density_union X P Q x hx hk hg.1 hg.2
    simp only [ite_eq_left hg, ite_eq_left hb, le_refl]
  · simp only [ite_eq_right hg]
    split_ifs <;> norm_num

/-- With probability at least `31/32` over `P`, `Q`, and a uniform `x ∈ X`,
at most a `2^(-k-6)` fraction of modifications to `x` on `P` have completion
density below `2^(-194*k)` when the coordinates in `Q` are subsequently modified. -/
theorem mirror_bad_modifications_probability (X : Finset (ι → Bool)) (hX : X.Nonempty)
    {k p q : ℝ} (hk : 1 ≤ k) (hdef : uniformDeficit X ≤ k) (hp : 0 < p)
    (hq : q = 32768 * k * p) (hq' : q ≤ 1 / 2) :
    31 / 32 ≤ bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
      𝔼 x ∈ X, if (𝔼 y, if coordinateDensity X Q (resample P x y) <
        (2 : ℝ) ^ (-194 * k) then (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (-k - 6) then 1 else 0)) := by
  have hqp : 0 < q := by rw [hq]; positivity
  have hq1 : q ≤ 1 := by linarith
  have hpq : p ≤ q := by rw [hq]; nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hk)]
  let r := p * (1 - q) / (p + q - p * q)
  have hb := conditionalSamplingRate_bounds hp.le hqp hq1
  have htheta : 0 < p + q - p * q := by
    nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hq1)]
  have hr : r ≤ 1 / (32768 * k) := by
    refine hb.2.1.trans_eq ?_
    rw [hq]
    field_simp
  exact bad_modifications_probability_of_rate X hX hk hdef hp.le (hpq.trans hq1) hqp.le hq1
    hb.1 hr (by field_simp)

end

/-! ### Guided distributions and the improved mirror set

On a sufficiently dense fiber, sample uniformly from its intersection with `Y`; on the remaining
fibers, sample uniformly from the whole fiber. The density of this sampling rule is at most `2^k`.
This is a distributional variant of the fixed-size guiding sets in Korten's proof [Korten2026],
avoiding a rounding operation.

The completion estimate bounds the guided failure probability by `1/16`.
Intersecting `Y` with the `(q,194*k)`-limits of `X` gives a nonempty mirror set
of deficit at most `2*k+2`, with `q = 32768*k*p`.

Source: [Korten, Sections 3--4][Korten2026]. -/

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Density of the guiding rule relative to uniform coordinate modifications.
Dense fibers are restricted to `Y`; the other fibers are left uniform. -/
noncomputable def guidingDensity (Y : Finset (ι → Bool)) (k : ℝ) (P x y : ι → Bool) : ℝ :=
  if (2 : ℝ) ^ (-k) ≤ coordinateDensity Y P x then
    (if resample P x y ∈ Y then 1 else 0) / coordinateDensity Y P x else 1

/-- Expectation of a test function after a guided modification of a uniform
point of `X`, using a rate-`p` coordinate mask and deficit parameter `k`. -/
noncomputable def guidedAverage (X Y : Finset (ι → Bool)) (p k : ℝ)
    (f : (ι → Bool) → ℝ) : ℝ :=
  𝔼 x ∈ X, bernoulliAverage p (fun P =>
    𝔼 y, guidingDensity Y k P x y * f (resample P x y))

theorem guidingDensity_nonneg (Y : Finset (ι → Bool)) (k : ℝ) (P x y : ι → Bool) :
    0 ≤ guidingDensity Y k P x y := by
  have hd := coordinateDensity_nonneg Y P x
  unfold guidingDensity
  split_ifs <;> positivity

theorem expect_guidingDensity (Y : Finset (ι → Bool)) (k : ℝ) (P x : ι → Bool) :
    (𝔼 y, guidingDensity Y k P x y) = 1 := by
  unfold guidingDensity
  split_ifs with h
  · rw [← expect_div, ← coordinateDensity_eq_expect]
    exact div_self (ne_of_gt (lt_of_lt_of_le (by positivity) h))
  · exact Fintype.expect_const _

theorem guidingDensity_le (Y : Finset (ι → Bool)) {k : ℝ} (hk : 0 ≤ k)
    (P x y : ι → Bool) : guidingDensity Y k P x y ≤ (2 : ℝ) ^ k := by
  unfold guidingDensity
  split_ifs with h hy
  · apply (div_le_iff₀ (lt_of_lt_of_le (by positivity) h)).mpr
    have he : (2 : ℝ) ^ (-k) * (2 : ℝ) ^ k = 1 := by
      rw [← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero]
    nlinarith [mul_le_mul_of_nonneg_right h (show (0 : ℝ) ≤ 2 ^ k by positivity)]
  · simp only [zero_div]
    positivity
  · exact Real.one_le_rpow (by norm_num) hk

theorem guidedAverage_const (X Y : Finset (ι → Bool)) (hX : X.Nonempty) (p k c : ℝ) :
    guidedAverage X Y p k (fun _ => c) = c := by
  unfold guidedAverage
  simp_rw [← expect_mul, expect_guidingDensity, one_mul, bernoulliAverage_const]
  exact expect_const hX c

theorem guidedAverage_mono (X Y : Finset (ι → Bool)) {p k : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    {f g : (ι → Bool) → ℝ} (hfg : ∀ z, f z ≤ g z) :
    guidedAverage X Y p k f ≤ guidedAverage X Y p k g := by
  apply expect_le_expect
  intro x _
  apply bernoulliAverage_mono hp hp'
  intro P
  exact expect_le_expect fun y _ =>
    mul_le_mul_of_nonneg_left (hfg _) (guidingDensity_nonneg Y k P x y)

theorem expect_resample (f : (ι → Bool) → ℝ) (P : ι → Bool) :
    (𝔼 x, 𝔼 y, f (resample P x y)) = 𝔼 z, f z := by
  have he (x : ι → Bool) : (𝔼 y, f (resample P x y)) =
      projectionAverage f (fun i => !P i) x := by
    unfold projectionAverage
    apply expect_congr rfl
    intro y _
    apply congrArg f
    funext i
    cases hp : P i <;> simp [resample, hp]
  simp_rw [he]
  exact (expect_coordinateMarginal_comp f (fun i => !P i) id).trans
    (expect_coordinateMarginal f _)

theorem sum_expect_resample (f : (ι → Bool) → ℝ) (P : ι → Bool) :
    (∑ x, 𝔼 y, f (resample P x y)) = ∑ z, f z := by
  rw [← Fintype.card_mul_expect, expect_resample, Fintype.card_mul_expect]

theorem expect_resample_subset_le (X : Finset (ι → Bool)) (f : (ι → Bool) → ℝ)
    (hf : ∀ x, 0 ≤ f x) (P : ι → Bool) :
    (𝔼 x ∈ X, 𝔼 y, f (resample P x y)) ≤ (∑ z, f z) / (X.card : ℝ) := by
  rw [expect_eq_sum_div_card]
  have hs : (∑ x ∈ X, 𝔼 y, f (resample P x y)) ≤ ∑ x, 𝔼 y, f (resample P x y) := by
    exact sum_le_sum_of_subset_of_nonneg (subset_univ X)
      (fun x _ _ => expect_nonneg (fun y _ => hf _))
  rw [sum_expect_resample] at hs
  exact div_le_div_of_nonneg_right hs (by positivity)

theorem guidedAverage_bound (X Y : Finset (ι → Bool)) {p k : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hk : 0 ≤ k) (f : (ι → Bool) → ℝ)
    (hf : ∀ z, 0 ≤ f z) :
    guidedAverage X Y p k f ≤ (2 : ℝ) ^ k * (∑ z, f z) / X.card := by
  have hm : guidedAverage X Y p k f ≤
      (2 : ℝ) ^ k * bernoulliAverage p (fun P => 𝔼 x ∈ X, 𝔼 y, f (resample P x y)) := by
    unfold guidedAverage
    rw [bernoulliAverage_expect_comm, mul_expect]
    apply expect_le_expect
    intro x _
    rw [← bernoulliAverage_mul]
    apply bernoulliAverage_mono hp hp'
    intro P
    rw [mul_expect]
    exact expect_le_expect fun y _ =>
      mul_le_mul_of_nonneg_right (guidingDensity_le Y hk P x y) (hf _)
  have hb := bernoulliAverage_mono hp hp' (expect_resample_subset_le X f hf)
  rw [bernoulliAverage_const] at hb
  exact hm.trans ((mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq
    (mul_div_assoc _ _ _).symm)

theorem guidingDensity_hits (Y : Finset (ι → Bool)) (k : ℝ) (P x : ι → Bool) :
    (if (2 : ℝ) ^ (-k) ≤ coordinateDensity Y P x then (1 : ℝ) else 0) ≤
      𝔼 y, guidingDensity Y k P x y * (if resample P x y ∈ Y then 1 else 0) := by
  by_cases h : (2 : ℝ) ^ (-k) ≤ coordinateDensity Y P x
  · have he (y : ι → Bool) : guidingDensity Y k P x y *
        (if resample P x y ∈ Y then 1 else 0) = guidingDensity Y k P x y := by
      unfold guidingDensity
      simp only [ite_eq_left h]
      split_ifs <;> simp
    simp_rw [he, expect_guidingDensity, ite_eq_left h]
    exact le_rfl
  · rw [ite_eq_right h]
    exact expect_nonneg fun y _ => mul_nonneg (guidingDensity_nonneg Y k P x y)
      (by split_ifs <;> norm_num)

theorem guidedAverage_hits (X Y : Finset (ι → Bool)) (hX : X.Nonempty) {p k : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hlim : ∀ x ∈ X, IsDensityLimit Y p k x) :
    3 / 4 ≤ guidedAverage X Y p k (fun z => if z ∈ Y then 1 else 0) := by
  have hpoint (x : ι → Bool) (hx : x ∈ X) : 3 / 4 ≤ bernoulliAverage p (fun P =>
      𝔼 y, guidingDensity Y k P x y * (if resample P x y ∈ Y then 1 else 0)) :=
    (hlim x hx).trans (bernoulliAverage_mono hp hp' (fun P => guidingDensity_hits Y k P x))
  simpa only [guidedAverage, expect_const hX] using expect_le_expect (s := X) hpoint

theorem guidedAverage_linear (X Y : Finset (ι → Bool)) (p k a b : ℝ)
    (f g : (ι → Bool) → ℝ) :
    guidedAverage X Y p k (fun z => a * f z + b * g z) =
      a * guidedAverage X Y p k f + b * guidedAverage X Y p k g := by
  unfold guidedAverage
  have he (x P y : ι → Bool) : guidingDensity Y k P x y *
      (a * f (resample P x y) + b * g (resample P x y)) =
        a * (guidingDensity Y k P x y * f (resample P x y)) +
        b * (guidingDensity Y k P x y * g (resample P x y)) := by ring
  simp_rw [he, expect_add_distrib, ← mul_expect, bernoulliAverage_linear]
  rw [expect_add_distrib, ← mul_expect, ← mul_expect]

theorem guidedAverage_bernoulli (X Y : Finset (ι → Bool)) (p q k : ℝ)
    (f : (ι → Bool) → (ι → Bool) → ℝ) :
    guidedAverage X Y p k (fun z => bernoulliAverage q (fun Q => f Q z)) =
      bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
        𝔼 x ∈ X, 𝔼 y, guidingDensity Y k P x y * f Q (resample P x y))) := by
  unfold guidedAverage
  simp_rw [← bernoulliAverage_mul, ← bernoulliAverage_expect_comm]

theorem guidingDensity_small_event (Y : Finset (ι → Bool)) {k : ℝ} (hk : 0 ≤ k)
    (P x : ι → Bool) (f : (ι → Bool) → ℝ) (hf : ∀ y, 0 ≤ f y) (hf' : ∀ y, f y ≤ 1) :
    (𝔼 y, guidingDensity Y k P x y * f y) ≤
      65 / 64 - (if (𝔼 y, f y) ≤ (2 : ℝ) ^ (-k - 6) then (1 : ℝ) else 0) := by
  have hone : (𝔼 y, guidingDensity Y k P x y * f y) ≤ 1 := by
    rw [← expect_guidingDensity Y k P x]
    exact expect_le_expect fun y _ => mul_le_of_le_one_right
      (guidingDensity_nonneg Y k P x y) (hf' y)
  by_cases hsmall : (𝔼 y, f y) ≤ (2 : ℝ) ^ (-k - 6)
  · have hcap : (𝔼 y, guidingDensity Y k P x y * f y) ≤
        (2 : ℝ) ^ k * (𝔼 y, f y) := by
      rw [mul_expect]
      exact expect_le_expect fun y _ =>
        mul_le_mul_of_nonneg_right (guidingDensity_le Y hk P x y) (hf y)
    have he : (2 : ℝ) ^ k * (2 : ℝ) ^ (-k - 6) = 1 / 64 := by
      rw [← Real.rpow_add (by norm_num), show k + (-k - 6) = (-6 : ℝ) by ring]
      norm_num
    have hh := hcap.trans ((mul_le_mul_of_nonneg_left hsmall (by positivity)).trans_eq he)
    rw [ite_eq_left hsmall]
    linarith
  · rw [ite_eq_right hsmall]
    linarith

theorem guidedAverage_bad_completion (X Y : Finset (ι → Bool)) (hX : X.Nonempty)
    {k p q : ℝ} (hk : 1 ≤ k) (hdef : uniformDeficit X ≤ k) (hp : 0 < p)
    (hq : q = 32768 * k * p) (hq' : q ≤ 1 / 2) :
    guidedAverage X Y p k (fun z => bernoulliAverage q (fun Q =>
      if coordinateDensity X Q z < (2 : ℝ) ^ (-194 * k) then (1 : ℝ) else 0)) ≤ 1 / 16 := by
  have hqp : 0 < q := by rw [hq]; positivity
  have hq1 : q ≤ 1 := by linarith
  have hpq : p ≤ q := by rw [hq]; nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hk)]
  let f (Q z : ι → Bool) : ℝ :=
    if coordinateDensity X Q z < (2 : ℝ) ^ (-194 * k) then 1 else 0
  have hm : guidedAverage X Y p k (fun z => bernoulliAverage q (fun Q => f Q z)) ≤
      bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
        𝔼 x ∈ X, (65 / 64 - (if (𝔼 y, f Q (resample P x y)) ≤ (2 : ℝ) ^ (-k - 6)
          then (1 : ℝ) else 0)))) := by
    rw [guidedAverage_bernoulli]
    apply bernoulliAverage_mono hp.le (hpq.trans hq1)
    intro P
    apply bernoulliAverage_mono hqp.le hq1
    intro Q
    apply expect_le_expect
    intro x _
    exact guidingDensity_small_event Y (by linarith) P x (fun y => f Q (resample P x y))
      (by intro y; dsimp [f]; split_ifs <;> norm_num)
      (by intro y; dsimp [f]; split_ifs <;> norm_num)
  simp_rw [expect_sub_distrib, expect_const hX, bernoulliAverage_sub,
    bernoulliAverage_const] at hm
  have hg := mirror_bad_modifications_probability X hX hk hdef hp hq hq'
  dsimp only [f] at hm
  linarith

theorem densityLimit_complement (X : Finset (ι → Bool)) (q t : ℝ) (z : ι → Bool) :
    bernoulliAverage q (fun Q => if coordinateDensity X Q z < (2 : ℝ) ^ (-t) then
      (1 : ℝ) else 0) = 1 - bernoulliAverage q
        (fun Q => if (2 : ℝ) ^ (-t) ≤ coordinateDensity X Q z then (1 : ℝ) else 0) := by
  have he (Q : ι → Bool) : (if coordinateDensity X Q z < (2 : ℝ) ^ (-t) then
      (1 : ℝ) else 0) = 1 - (if (2 : ℝ) ^ (-t) ≤ coordinateDensity X Q z then 1 else 0) := by
    split_ifs <;> linarith
  simp_rw [he, bernoulliAverage_sub, bernoulliAverage_const]

open scoped Classical in
theorem guidedAverage_mirror_mass (X Y : Finset (ι → Bool)) (hX : X.Nonempty)
    {k p q : ℝ} (hk : 1 ≤ k) (hdef : uniformDeficit X ≤ k) (hp : 0 < p)
    (hq : q = 32768 * k * p) (hq' : q ≤ 1 / 2)
    (hlim : ∀ x ∈ X, IsDensityLimit Y p k x) :
    1 / 4 ≤ guidedAverage X Y p k
      (fun z => if z ∈ Y ∧ IsDensityLimit X q (194 * k) z then (1 : ℝ) else 0) := by
  have hqp : 0 < q := by rw [hq]; positivity
  have hq1 : q ≤ 1 := by linarith
  have hpq : p ≤ q := by rw [hq]; nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hk)]
  let bad (z : ι → Bool) : ℝ := bernoulliAverage q (fun Q =>
    if coordinateDensity X Q z < (2 : ℝ) ^ (-(194 * k)) then (1 : ℝ) else 0)
  have hbad (z : ι → Bool) : 0 ≤ bad z := by
    have h := bernoulliAverage_mono hqp.le hq1 (f := fun _ => 0)
      (g := fun Q => if coordinateDensity X Q z < (2 : ℝ) ^ (-(194 * k)) then 1 else 0)
      (by intro Q; split_ifs <;> norm_num)
    simpa only [bernoulliAverage_const] using h
  have hpoint (z : ι → Bool) : (if z ∈ Y then (1 : ℝ) else 0) ≤
      1 * (if z ∈ Y ∧ IsDensityLimit X q (194 * k) z then 1 else 0) + 4 * bad z := by
    by_cases hy : z ∈ Y
    · by_cases hl : IsDensityLimit X q (194 * k) z
      · simp only [hy, hl, and_self, ite_true, one_mul]
        nlinarith [hbad z]
      · have hh : 1 / 4 < bad z := by
          dsimp only [bad]
          rw [densityLimit_complement]
          unfold IsDensityLimit at hl
          linarith
        simp only [hy, hl, and_false, ite_true, ite_false, mul_zero, zero_add]
        linarith
    · simp only [hy, false_and, ite_false, mul_zero, zero_add]
      nlinarith [hbad z]
  have hm := guidedAverage_mono X Y (k := k) hp.le (hpq.trans hq1) hpoint
  rw [guidedAverage_linear, one_mul] at hm
  have hhit := guidedAverage_hits X Y hX hp.le (hpq.trans hq1) hlim
  have hloss : guidedAverage X Y p k bad ≤ 1 / 16 := by
    simpa only [bad, neg_mul] using guidedAverage_bad_completion X Y hX hk hdef hp hq hq'
  linarith

/-- **The mirror-set lemma** [Korten, Sections 3 and 4][Korten2026]: if every point of a set `X`
of deficit at most `k` is a `(p, k)`-limit of `Y`, then `Y` has a nonempty subset of deficit at
most `2 k + 2` all of whose points are `(32768 k p, 194 k)`-limits of `X`. -/
theorem exists_mirror_set (X Y : Finset (ι → Bool)) (hX : X.Nonempty)
    {k p q : ℝ} (hk : 1 ≤ k) (hdef : uniformDeficit X ≤ k) (hp : 0 < p)
    (hq : q = 32768 * k * p) (hq' : q ≤ 1 / 2)
    (hlim : ∀ x ∈ X, IsDensityLimit Y p k x) :
    ∃ Y' : Finset (ι → Bool), Y' ⊆ Y ∧ Y'.Nonempty ∧ uniformDeficit Y' ≤ 2 * k + 2 ∧
      ∀ y ∈ Y', IsDensityLimit X q (194 * k) y := by
  classical
  let A := Y.filter (IsDensityLimit X q (194 * k))
  have hq1 : q ≤ 1 := by linarith
  have hpq : p ≤ q := by rw [hq]; nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hk)]
  have hm : 1 / 4 ≤ guidedAverage X Y p k (fun z => if z ∈ A then (1 : ℝ) else 0) := by
    simpa only [A, mem_filter] using
      guidedAverage_mirror_mass X Y hX hk hdef hp hq hq' hlim
  have hb : guidedAverage X Y p k (fun z => if z ∈ A then (1 : ℝ) else 0) ≤
      (2 : ℝ) ^ k * A.card / X.card := by
    simpa using guidedAverage_bound X Y hp.le (hpq.trans hq1) (show 0 ≤ k by linarith)
      (fun z => if z ∈ A then (1 : ℝ) else 0) (by intro z; split_ifs <;> norm_num)
  have hxpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hxcount := (uniformDeficit_le_iff hX).mp hdef
  have hprod : (4 * (2 : ℝ) ^ k) * (2 : ℝ) ^ ((Fintype.card ι : ℝ) - (2 * k + 2)) =
      (2 : ℝ) ^ ((Fintype.card ι : ℝ) - k) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num,
      ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hcard : (2 : ℝ) ^ ((Fintype.card ι : ℝ) - (2 * k + 2)) ≤ A.card := by
    apply (mul_le_mul_iff_right₀ (show 0 < 4 * (2 : ℝ) ^ k by positivity)).mp
    rw [hprod]
    have hh := (le_div_iff₀ hxpos).mp (hm.trans hb)
    nlinarith
  have hA : A.Nonempty := by
    apply card_pos.mp
    have hpos := (Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num)
      ((Fintype.card ι : ℝ) - (2 * k + 2))).trans_le hcard
    exact_mod_cast hpos
  exact ⟨A, filter_subset _ _, hA, (uniformDeficit_le_iff hA).mpr hcard,
    fun y hy => (mem_filter.mp hy).2⟩

end

end Cslib.BooleanAnalysis
