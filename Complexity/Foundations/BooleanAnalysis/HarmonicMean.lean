/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.Bernoulli
public import Complexity.Foundations.BooleanAnalysis.Fibers
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Korten's harmonic mean transform

The harmonic mean of a nonnegative function on a finite type (`harmonicMean`), zero as soon as a
value is zero, has a variational formula: it is the least energy `𝔼 (f w ^ 2)` of a nonnegative
weight `w` of mean one [Korten, Lemma 11][Korten2026] (`harmonicMean_variational`). Hence it is
monotone and concave, and at most the arithmetic mean.

The harmonic mean transform of a function on the cube (`harmonicTransform`,
[Korten, Definition 5][Korten2026]) projects the function to a set of selected coordinates and takes
the harmonic mean of the projection. It is the harmonic mean of the marginal on the selected
coordinates (`harmonicTransform_eq_harmonicMean_coordinateMarginal`), and it is concave in the
function, antitone in the selected set and at most the mean [Korten, Corollary 1][Korten2026].
Korten's inequality bounds the expected square root of a function by the expected square root of
its transform at a random set containing each coordinate with probability `1 / 4`
[Korten, Lemma 12][Korten2026] (`expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform`), which
gives the sampling estimate in the proof of Lemma 10 (`harmonicTransform_good_probability`). The
sparse sampling conclusion of Lemma 10 is `BitString.harmonicTransform_sparse_good_probability`.

## Main definitions

* `Cslib.BitString.harmonicMean`: the harmonic mean on a finite type.
* `Cslib.BitString.harmonicTransform`: Korten's harmonic mean transform.

## Main results

* `Cslib.BitString.harmonicMean_variational`: the variational formula.
* `Cslib.BitString.concaveOn_harmonicMean`, `Cslib.BitString.harmonicMean_le_expect`:
  the harmonic mean is concave, and at most the arithmetic mean.
* `Cslib.BitString.concaveOn_harmonicTransform`,
  `Cslib.BitString.harmonicTransform_antitone`,
  `Cslib.BitString.harmonicTransform_le_expect`: the transform is concave in the function,
  antitone in the selected set, and at most the mean.
* `Cslib.BitString.expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform`: Korten's
  inequality.
* `Cslib.BitString.harmonicTransform_good_probability`: the sampling estimate of Lemma 10.

## References

* [O. Korten, *Top-Down Lower Bounds for All Depths*][Korten2026]
-/

@[expose] public section

namespace Cslib.BitString

open scoped BigOperators
open Finset

/-! ### Harmonic means on finite types

The harmonic mean of `f : α → ℝ` on a finite type is `(𝔼 x, (f x)⁻¹)⁻¹`, and it is zero as soon as
some value of `f` is zero: inside the average, `0⁻¹` counts as `∞` rather than as Lean's
`0⁻¹ = 0`. The theorems assume nonnegative values. The variational formula
[Korten, Lemma 11][Korten2026] holds on every nonempty finite type: completing the square gives the
lower bound, and an explicit weight attains it, including when a value vanishes. -/

/-- The uniform harmonic mean, with value zero whenever an entry is zero. -/
noncomputable def harmonicMean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  if ∃ x, f x = 0 then 0 else (𝔼 x, (f x)⁻¹)⁻¹

section

variable {α : Type*} [Fintype α]

/-- A zero entry makes the harmonic mean zero: inside the average, `0⁻¹` counts as `∞` rather than
as Lean's `0⁻¹ = 0`. -/
theorem harmonicMean_eq_zero_of_exists {f : α → ℝ} (hf : ∃ x, f x = 0) : harmonicMean f = 0 := by
  rw [harmonicMean, ite_eq_left hf]

/-- The harmonic mean of positive entries is the reciprocal of the mean of their reciprocals. -/
theorem harmonicMean_of_pos {f : α → ℝ} (hf : ∀ x, 0 < f x) :
    harmonicMean f = (𝔼 x, (f x)⁻¹)⁻¹ :=
  ite_eq_right fun ⟨x, hx⟩ => (hf x).ne' hx

/-- Harmonic means of nonnegative entries are nonnegative. -/
theorem harmonicMean_nonneg {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ harmonicMean f := by
  unfold harmonicMean
  split_ifs
  · exact le_rfl
  · exact inv_nonneg.mpr (expect_nonneg fun x _ => inv_nonneg.mpr (hf x))

/-- An equivalence of finite types preserves harmonic means. -/
theorem harmonicMean_equiv {β : Type*} [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : harmonicMean (fun x => f (e x)) = harmonicMean f := by
  have hz : (∃ x, f (e x) = 0) ↔ ∃ y, f y = 0 := e.exists_congr_left.trans (by simp)
  simp only [harmonicMean, hz]
  rw [Fintype.expect_equiv e (fun x => (f (e x))⁻¹) (fun y => (f y)⁻¹) (fun _ => rfl)]

variable [Nonempty α]

/-- Every weight with mean one bounds the harmonic mean by its quadratic energy.
The weight need not be nonnegative for this direction. -/
theorem harmonicMean_le_energy {f w : α → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hw : (𝔼 x, w x) = 1) : harmonicMean f ≤ 𝔼 x, f x * w x ^ 2 := by
  by_cases hz : ∃ x, f x = 0
  · rw [harmonicMean_eq_zero_of_exists hz]
    exact expect_nonneg fun x _ => mul_nonneg (hf x) (sq_nonneg _)
  have hpos (x : α) : 0 < f x := (hf x).lt_of_ne' fun h => hz ⟨x, h⟩
  have he : (𝔼 x, (f x)⁻¹) ≠ 0 :=
    (expect_pos (fun x _ => inv_pos.mpr (hpos x)) univ_nonempty).ne'
  let h := (𝔼 x, (f x)⁻¹)⁻¹
  have hs := expect_nonneg (s := univ)
    (fun x _ => mul_nonneg (hf x) (sq_nonneg (w x - h / f x)))
  have hid (x : α) : f x * (w x - h / f x) ^ 2 =
      f x * w x ^ 2 - 2 * h * w x + h ^ 2 * (f x)⁻¹ := by
    field_simp [(hpos x).ne']
    ring
  simp_rw [hid, expect_add_distrib, expect_sub_distrib, ← mul_expect] at hs
  rw [hw] at hs
  have hh : h ^ 2 * (𝔼 x, (f x)⁻¹) = h := by
    dsimp [h]
    field_simp
  rw [hh] at hs
  rw [harmonicMean_of_pos hpos]
  dsimp [h] at hs
  linarith

/-- A nonnegative weight of mean one attains the variational minimum,
including when an entry of `f` is zero. -/
theorem harmonicMean_exists_weight {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∃ w : α → ℝ, (∀ x, 0 ≤ w x) ∧ (𝔼 x, w x) = 1 ∧
      (𝔼 x, f x * w x ^ 2) = harmonicMean f := by
  classical
  by_cases hz : ∃ x, f x = 0
  · obtain ⟨a, ha⟩ := hz
    refine ⟨fun x => if x = a then Fintype.card α else 0, ?_, ?_, ?_⟩
    · intro x; dsimp only; split_ifs <;> positivity
    · rw [Fintype.expect_eq_sum_div_card]
      simp [Fintype.card_ne_zero]
    · rw [harmonicMean_eq_zero_of_exists ⟨a, ha⟩]
      apply expect_eq_zero
      intro x _
      by_cases hx : x = a <;> simp [hx, ha]
  · have hpos (x : α) : 0 < f x := (hf x).lt_of_ne' fun h => hz ⟨x, h⟩
    have he : (𝔼 x, (f x)⁻¹) ≠ 0 :=
      (expect_pos (fun x _ => inv_pos.mpr (hpos x)) univ_nonempty).ne'
    let h := (𝔼 x, (f x)⁻¹)⁻¹
    refine ⟨fun x => h * (f x)⁻¹, ?_, ?_, ?_⟩
    · intro x
      exact mul_nonneg (inv_nonneg.mpr
        (expect_nonneg fun x _ => inv_nonneg.mpr (hf x))) (inv_nonneg.mpr (hf x))
    · rw [← mul_expect]
      exact inv_mul_cancel₀ he
    · have hid (x : α) : f x * (h * (f x)⁻¹) ^ 2 = h ^ 2 * (f x)⁻¹ := by
        field_simp [(hpos x).ne']
      simp_rw [hid, ← mul_expect]
      rw [harmonicMean_of_pos hpos]
      dsimp [h]
      field_simp

/-- **The variational formula for the harmonic mean** [Korten, Lemma 11][Korten2026], on every
nonempty finite type: the harmonic mean is the least energy `𝔼 (f w ^ 2)` of a nonnegative weight
`w` of mean one. -/
theorem harmonicMean_variational {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    harmonicMean f = sInf {a : ℝ | ∃ w : α → ℝ,
      (∀ x, 0 ≤ w x) ∧ (𝔼 x, w x) = 1 ∧ (𝔼 x, f x * w x ^ 2) = a} := by
  symm
  apply IsLeast.csInf_eq
  constructor
  · exact harmonicMean_exists_weight hf
  · rintro _ ⟨w, _, hw, rfl⟩
    exact harmonicMean_le_energy hf hw

/-- Harmonic means are monotone in their nonnegative entries. -/
theorem harmonicMean_mono {f g : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ g x) :
    harmonicMean f ≤ harmonicMean g := by
  obtain ⟨w, _, hw, he⟩ := harmonicMean_exists_weight
    (fun x => (hf x).trans (hfg x))
  rw [← he]
  exact (harmonicMean_le_energy hf hw).trans
    (expect_le_expect fun x _ => mul_le_mul_of_nonneg_right (hfg x) (sq_nonneg _))

/-- The harmonic mean is concave on nonnegative functions. -/
theorem concaveOn_harmonicMean : ConcaveOn ℝ (Set.Ici 0) (harmonicMean : (α → ℝ) → ℝ) := by
  refine ⟨convex_Ici 0, fun f hf g hg a b ha hb _ => ?_⟩
  obtain ⟨w, _, hw, he⟩ := harmonicMean_exists_weight (f := a • f + b • g)
    (fun x => add_nonneg (mul_nonneg ha (hf x)) (mul_nonneg hb (hg x)))
  rw [← he, smul_eq_mul, smul_eq_mul]
  calc
    _ ≤ a * (𝔼 x, f x * w x ^ 2) + b * (𝔼 x, g x * w x ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left (harmonicMean_le_energy hf hw) ha)
        (mul_le_mul_of_nonneg_left (harmonicMean_le_energy hg hw) hb)
    _ = _ := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc,
        expect_add_distrib, ← mul_expect]

/-- The harmonic mean is at most the arithmetic mean. -/
theorem harmonicMean_le_expect {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    harmonicMean f ≤ 𝔼 x, f x := by
  simpa using harmonicMean_le_energy (w := fun _ => 1) hf (by simp)

/-- **Jensen's inequality for the harmonic mean**: the average of harmonic means is at most the
harmonic mean of the average. -/
theorem expect_harmonicMean_le {β : Type*} [Fintype β]
    {f : β → α → ℝ} (hf : ∀ y x, 0 ≤ f y x) :
    (𝔼 y, harmonicMean (f y)) ≤ harmonicMean (fun x => 𝔼 y, f y x) := by
  obtain ⟨w, _, hw, he⟩ := harmonicMean_exists_weight
    (fun x => expect_nonneg fun y _ => hf y x)
  calc
    _ ≤ 𝔼 y, 𝔼 x, f y x * w x ^ 2 :=
      expect_le_expect fun y _ => harmonicMean_le_energy (hf y) hw
    _ = 𝔼 x, (𝔼 y, f y x) * w x ^ 2 := by
      rw [expect_comm]
      simp_rw [expect_mul]
    _ = _ := he

/-- The harmonic mean of a constant on a nonempty finite set is that constant. -/
theorem harmonicMean_const (c : ℝ) :
    harmonicMean (fun _ : α => c) = c := by
  by_cases hc : c = 0 <;> simp [harmonicMean, hc]

/-- A positive harmonic-mean lower bound controls the fraction of small entries.
This is the reciprocal-density Markov step used for light patterns. -/
theorem harmonicMean_light_fraction_le {f : α → ℝ} (hf : ∀ x, 0 ≤ f x)
    {a b : ℝ} (ha : 0 < a) (ha' : a ≤ harmonicMean f) (hb : 0 ≤ b) :
    (𝔼 x, if f x ≤ b then (1 : ℝ) else 0) ≤ b / a := by
  have hp (x : α) : 0 < f x := by
    refine (hf x).lt_of_ne' fun h => ?_
    rw [harmonicMean_eq_zero_of_exists ⟨x, h⟩] at ha'
    exact (not_le_of_gt ha) ha'
  have he : 0 < 𝔼 x, (f x)⁻¹ :=
    expect_pos (fun x _ => inv_pos.mpr (hp x)) univ_nonempty
  have hinv : (𝔼 x, (f x)⁻¹) ≤ 1 / a := by
    rw [harmonicMean_of_pos hp, ← one_div] at ha'
    have hmul := (le_div_iff₀ he).mp ha'
    apply (le_div_iff₀ ha).mpr
    linarith
  calc
    _ ≤ 𝔼 x, b * (f x)⁻¹ := by
      apply expect_le_expect
      intro x _
      split_ifs with h
      · rw [← div_eq_mul_inv]
        exact (one_le_div (hp x)).mpr h
      · exact mul_nonneg hb (inv_nonneg.mpr (hf x))
    _ = b * (𝔼 x, (f x)⁻¹) := (mul_expect _ _ _).symm
    _ ≤ b * (1 / a) := mul_le_mul_of_nonneg_left hinv hb
    _ = _ := by ring

omit [Nonempty α] in
private theorem expect_univ_prod {β : Type*} [Fintype β] (f : α × β → ℝ) :
    (𝔼 x, f x) = 𝔼 a, 𝔼 b, f (a, b) := by
  simpa only [univ_product_univ] using expect_product univ univ f

private theorem expect_univ_bool (f : Bool → ℝ) :
    (𝔼 b, f b) = (f false + f true) / 2 := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.sum_bool]
  simp only [Fintype.card_bool, Nat.cast_ofNat]
  ring

/-- The harmonic mean of a function on `Bool × α` is the two-point harmonic mean
`2 h₀ h₁ / (h₀ + h₁)` of the harmonic means `h₀`, `h₁` of its two halves. -/
theorem harmonicMean_pair {f : Bool → α → ℝ} (hf : ∀ b x, 0 ≤ f b x) :
    harmonicMean (fun x : Bool × α => f x.1 x.2) =
      2 * harmonicMean (f false) * harmonicMean (f true) /
        (harmonicMean (f false) + harmonicMean (f true)) := by
  by_cases h0 : ∃ x, f false x = 0
  · obtain ⟨x, hx⟩ := h0
    rw [harmonicMean_eq_zero_of_exists ⟨x, hx⟩,
      harmonicMean_eq_zero_of_exists (f := fun x : Bool × α => f x.1 x.2) ⟨(false, x), hx⟩]
    simp
  by_cases h1 : ∃ x, f true x = 0
  · obtain ⟨x, hx⟩ := h1
    rw [harmonicMean_eq_zero_of_exists ⟨x, hx⟩,
      harmonicMean_eq_zero_of_exists (f := fun x : Bool × α => f x.1 x.2) ⟨(true, x), hx⟩]
    simp
  have hpos (b : Bool) (x : α) : 0 < f b x := by
    refine (hf b x).lt_of_ne' fun h => ?_
    cases b
    · exact h0 ⟨x, h⟩
    · exact h1 ⟨x, h⟩
  have hp (b : Bool) : 0 < 𝔼 x, (f b x)⁻¹ :=
    expect_pos (fun x _ => inv_pos.mpr (hpos b x)) univ_nonempty
  rw [harmonicMean_of_pos (f := fun x : Bool × α => f x.1 x.2) fun x => hpos x.1 x.2,
    harmonicMean_of_pos (hpos false), harmonicMean_of_pos (hpos true), expect_univ_prod,
    expect_univ_bool]
  have hsum := add_pos (hp false) (hp true)
  field_simp [(hp false).ne', (hp true).ne', hsum.ne']
  simpa only [one_div, add_comm] using (div_self hsum.ne').symm

end

/-! ### The harmonic mean transform

A coordinate set is its Boolean membership function. The transform is represented on the full cube:
`projectionAverage f selected` depends only on the selected coordinates, and averaging on the full
cube gives each projected pattern the same multiplicity, so its harmonic mean is the harmonic mean
over the projected patterns (`harmonicTransform_eq_harmonicMean_coordinateMarginal`). -/

/-- Korten's harmonic mean transform [Korten, Definition 5][Korten2026]: the harmonic mean of the
projection of `f` to the selected coordinates, represented on the full cube. -/
noncomputable def harmonicTransform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (selected : ι → Bool) : ℝ :=
  harmonicMean (projectionAverage f selected)

/-- An equivalence of coordinate types commutes with the harmonic transform. -/
theorem harmonicTransform_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (f : (κ → Bool) → ℝ)
    (s : ι → Bool) :
    harmonicTransform (fun y => f (fun j => y (e.symm j))) s =
      harmonicTransform f (fun j => s (e.symm j)) := by
  unfold harmonicTransform
  change harmonicMean (fun x => projectionAverage
    (fun y => f (fun j => y (e.symm j))) s x) = _
  simp_rw [projectionAverage_reindex e f s]
  exact harmonicMean_equiv (Equiv.arrowCongr e (Equiv.refl Bool)) _

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The transform agrees with Definition 5 on the actual projected cube;
repeating each pattern on the full cube does not change its harmonic mean. -/
theorem harmonicTransform_eq_harmonicMean_coordinateMarginal
    (f : (ι → Bool) → ℝ) (selected : ι → Bool) :
    harmonicTransform f selected = harmonicMean (coordinateMarginal f selected) := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => selected i = true) (fun _ => Bool)
  have he (z : ({i // selected i = true} → Bool) × ({i // selected i ≠ true} → Bool)) :
      projectionAverage f selected (e.symm z) = coordinateMarginal f selected z.1 := by
    rw [projectionAverage_eq_coordinateMarginal]
    exact congrArg (coordinateMarginal f selected) (congrArg Prod.fst (e.apply_symm_apply z))
  rw [harmonicTransform, ← harmonicMean_equiv e.symm]
  simp_rw [he]
  simp [harmonicMean, expect_univ_prod]

/-- Lemma 11 on the selected-coordinate cube, with nonnegative weights of mean one. -/
theorem harmonicTransform_variational {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x)
    (selected : ι → Bool) :
    harmonicTransform f selected = sInf {a : ℝ |
      ∃ w : ({i // selected i = true} → Bool) → ℝ,
        (∀ z, 0 ≤ w z) ∧ (𝔼 z, w z) = 1 ∧
          (𝔼 z, coordinateMarginal f selected z * w z ^ 2) = a} := by
  rw [harmonicTransform_eq_harmonicMean_coordinateMarginal]
  exact harmonicMean_variational fun _ => Finset.expect_nonneg fun _ _ => hf _

/-- The harmonic transform is nonnegative on nonnegative functions. -/
theorem harmonicTransform_nonneg {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x)
    (selected : ι → Bool) : 0 ≤ harmonicTransform f selected :=
  harmonicMean_nonneg (projectionAverage_nonneg hf selected)

/-- Constants are fixed by the harmonic transform. -/
theorem harmonicTransform_const (c : ℝ) (selected : ι → Bool) :
    harmonicTransform (fun _ => c) selected = c := by
  have he : projectionAverage (fun _ => c) selected = fun _ => c := by
    funext x
    simp [projectionAverage]
  rw [harmonicTransform, he, harmonicMean_const]

/-- Selecting no coordinates gives the ordinary mean. -/
theorem harmonicTransform_empty (f : (ι → Bool) → ℝ) :
    harmonicTransform f (fun _ => false) = 𝔼 x, f x := by
  have he : projectionAverage f (fun _ => false) = fun _ => 𝔼 x, f x := by
    funext x
    simp only [projectionAverage, resample_false]
  rw [harmonicTransform, he, harmonicMean_const]

/-- Selecting all coordinates gives the harmonic mean of the original function. -/
theorem harmonicTransform_full (f : (ι → Bool) → ℝ) :
    harmonicTransform f (fun _ => true) = harmonicMean f := by
  have he : projectionAverage f (fun _ => true) = f := by
    funext x
    simp only [projectionAverage, resample_true, Fintype.expect_const]
  rw [harmonicTransform, he]

/-- **The transform is concave in the function** [Korten, Corollary 1][Korten2026]: for every
selected set, it is concave on nonnegative functions. -/
theorem concaveOn_harmonicTransform (selected : ι → Bool) :
    ConcaveOn ℝ (Set.Ici 0) (fun f : (ι → Bool) → ℝ => harmonicTransform f selected) := by
  refine ⟨convex_Ici 0, fun f hf g hg a b ha hb hab => ?_⟩
  have he : projectionAverage (a • f + b • g) selected =
      a • projectionAverage f selected + b • projectionAverage g selected := by
    funext x
    simp only [projectionAverage, Pi.add_apply, Pi.smul_apply, smul_eq_mul, expect_add_distrib,
      ← mul_expect]
  simp only [harmonicTransform, he]
  exact concaveOn_harmonicMean.2 (projectionAverage_nonneg hf selected)
    (projectionAverage_nonneg hg selected) ha hb hab

private theorem harmonicTransform_midpoint {f g : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hg : ∀ x, 0 ≤ g x) (selected : ι → Bool) :
    (harmonicTransform f selected + harmonicTransform g selected) / 2 ≤
      harmonicTransform (fun x => (f x + g x) / 2) selected := by
  have he : (fun x => (f x + g x) / 2) = (1 / 2 : ℝ) • f + (1 / 2 : ℝ) • g := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h := (concaveOn_harmonicTransform selected).2 hf hg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rw [he]
  simp only [smul_eq_mul] at h
  linarith

end

/-! ### Splitting off the first coordinate

The proofs of the antitonicity of the transform and of Korten's Lemma 12 are inductions on the
dimension, on the cube `Fin n → Bool`, which split off the first coordinate. -/

private theorem expect_univ_fin_cons {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    (𝔼 x, f x) = ((𝔼 x, f (Fin.cons false x)) + (𝔼 x, f (Fin.cons true x))) / 2 := by
  rw [← Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))
    (fun x => f (Fin.cons x.1 x.2)) f (fun _ => rfl)]
  rw [expect_univ_prod, expect_univ_bool]

private theorem resample_cons {n : ℕ} (s y x : Fin n → Bool) (a b c : Bool) :
    resample (Fin.cons a s : Fin (n + 1) → Bool) (Fin.cons b y) (Fin.cons c x) =
      Fin.cons (if a then c else b) (resample s y x) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [resample]

private theorem projectionAverage_cons_false {n : ℕ}
    (f : (Fin (n + 1) → Bool) → ℝ) (selected x : Fin n → Bool) (b : Bool) :
    projectionAverage f (Fin.cons false selected) (Fin.cons b x) =
      projectionAverage (fun x => (f (Fin.cons false x) + f (Fin.cons true x)) / 2)
        selected x := by
  unfold projectionAverage
  rw [expect_univ_fin_cons]
  simp only [resample_cons, Bool.false_eq_true, ite_false]
  rw [← expect_div, expect_add_distrib]

private theorem projectionAverage_cons_true {n : ℕ}
    (f : (Fin (n + 1) → Bool) → ℝ) (selected x : Fin n → Bool) (b : Bool) :
    projectionAverage f (Fin.cons true selected) (Fin.cons b x) =
      projectionAverage (fun x => f (Fin.cons b x)) selected x := by
  unfold projectionAverage
  rw [expect_univ_fin_cons]
  simp only [resample_cons, ite_true]
  ring

private theorem harmonicTransform_cons_false {n : ℕ}
    (f : (Fin (n + 1) → Bool) → ℝ) (selected : Fin n → Bool) :
    harmonicTransform f (Fin.cons false selected) =
      harmonicTransform
        (fun x => (f (Fin.cons false x) + f (Fin.cons true x)) / 2) selected := by
  unfold harmonicTransform
  rw [← harmonicMean_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))]
  change harmonicMean (fun x : Bool × (Fin n → Bool) =>
    projectionAverage f (Fin.cons false selected) (Fin.cons x.1 x.2)) = _
  simp_rw [projectionAverage_cons_false]
  simp [harmonicMean, expect_univ_prod]

private theorem harmonicTransform_cons_true {n : ℕ}
    {f : (Fin (n + 1) → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (selected : Fin n → Bool) :
    harmonicTransform f (Fin.cons true selected) =
      2 * harmonicTransform (fun x => f (Fin.cons false x)) selected *
        harmonicTransform (fun x => f (Fin.cons true x)) selected /
      (harmonicTransform (fun x => f (Fin.cons false x)) selected +
        harmonicTransform (fun x => f (Fin.cons true x)) selected) := by
  unfold harmonicTransform
  rw [← harmonicMean_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))]
  change harmonicMean (fun x : Bool × (Fin n → Bool) =>
    projectionAverage f (Fin.cons true selected) (Fin.cons x.1 x.2)) = _
  simp_rw [projectionAverage_cons_true]
  exact harmonicMean_pair fun b =>
    projectionAverage_nonneg (fun x => hf (Fin.cons b x)) selected

/-! ### The transform is antitone in the selected set -/

private theorem two_mul_mul_div_add_le_add_div_two {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * a * b / (a + b) ≤ (a + b) / 2 := by
  by_cases hz : a + b = 0
  · simp [hz]
  have hp : 0 < a + b := (add_nonneg ha hb).lt_of_ne' hz
  apply (div_le_iff₀ hp).mpr
  nlinarith [sq_nonneg (a - b)]

private theorem two_mul_mul_div_add_mono {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hac : a ≤ c) (hbd : b ≤ d) : 2 * a * b / (a + b) ≤ 2 * c * d / (c + d) := by
  have hc := ha.trans hac
  have hd := hb.trans hbd
  by_cases hz : a + b = 0
  · rw [hz, div_zero]
    positivity
  have hp : 0 < a + b := (add_nonneg ha hb).lt_of_ne' hz
  have hq : 0 < c + d := hp.trans_le (add_le_add hac hbd)
  apply (div_le_div_iff₀ hp hq).mpr
  nlinarith [mul_nonneg (mul_nonneg ha hc) (sub_nonneg.mpr hbd),
    mul_nonneg (mul_nonneg hb hd) (sub_nonneg.mpr hac)]

private theorem harmonicTransform_antitone_fin {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) : Antitone (harmonicTransform f) := by
  intro r s hrs
  induction n with
  | zero => exact le_of_eq (congrArg (harmonicTransform f) (Subsingleton.elim _ _))
  | succ n ih =>
    obtain ⟨⟨rb, r⟩, rfl⟩ := (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).surjective r
    obtain ⟨⟨sb, s⟩, rfl⟩ := (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).surjective s
    change harmonicTransform f (Fin.cons sb s) ≤ harmonicTransform f (Fin.cons rb r)
    have htail : r ≤ s := fun i => hrs i.succ
    have h0 := fun x => hf (Fin.cons false x)
    have h1 := fun x => hf (Fin.cons true x)
    have havg : ∀ x, 0 ≤ (f (Fin.cons false x) + f (Fin.cons true x)) / 2 :=
      fun x => div_nonneg (add_nonneg (h0 x) (h1 x)) (by norm_num)
    cases rb <;> cases sb
    · rw [harmonicTransform_cons_false, harmonicTransform_cons_false]
      exact ih havg htail
    · rw [harmonicTransform_cons_true hf, harmonicTransform_cons_false]
      exact (two_mul_mul_div_add_le_add_div_two (harmonicTransform_nonneg h0 s)
        (harmonicTransform_nonneg h1 s)).trans
        ((harmonicTransform_midpoint h0 h1 s).trans (ih havg htail))
    · exact absurd (hrs 0) (by simp)
    · rw [harmonicTransform_cons_true hf, harmonicTransform_cons_true hf]
      exact two_mul_mul_div_add_mono (harmonicTransform_nonneg h0 s)
        (harmonicTransform_nonneg h1 s) (ih h0 htail) (ih h1 htail)

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Selecting more coordinates decreases the harmonic transform**
[Korten, Corollary 1][Korten2026]. -/
theorem harmonicTransform_antitone {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    Antitone (harmonicTransform f) := by
  intro s t hst
  let e := (Fintype.equivFin ι).symm
  have h := harmonicTransform_antitone_fin (f := fun y => f (fun j => y (e.symm j)))
    (fun _ => hf _) (show (fun j => s (e j)) ≤ fun j => t (e j) from fun j => hst (e j))
  simpa only [harmonicTransform_reindex, Equiv.apply_symm_apply] using h

/-- The harmonic transform is at most the ordinary mean [Korten, Corollary 1][Korten2026]. -/
theorem harmonicTransform_le_expect {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x)
    (selected : ι → Bool) : harmonicTransform f selected ≤ 𝔼 x, f x := by
  rw [← harmonicTransform_empty f]
  exact harmonicTransform_antitone hf fun _ => Bool.false_le _

end

/-! ### Korten's harmonic mean inequality

The inequality [Korten, Lemma 12][Korten2026] follows from a scalar inequality by induction on the
dimension, using concavity of the harmonic mean. No strict-positivity assumption is needed. -/

private theorem add_sqrt_div_two_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a + Real.sqrt b) / 2 ≤
      3 / 4 * Real.sqrt ((a + b) / 2) + 1 / 4 * Real.sqrt (2 * a * b / (a + b)) := by
  by_cases hz : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  have hp : 0 < (a + b) / 2 := by positivity
  let c := Real.sqrt ((a + b) / 2)
  have hc : 0 < c := Real.sqrt_pos.mpr hp
  have hc2 : c ^ 2 = (a + b) / 2 := Real.sq_sqrt hp.le
  have hroot : Real.sqrt (2 * a * b / (a + b)) = Real.sqrt a * Real.sqrt b / c := by
    calc
      _ = Real.sqrt (a * b / ((a + b) / 2)) := by congr 1; field_simp
      _ = _ := by rw [Real.sqrt_div (mul_nonneg ha hb), Real.sqrt_mul ha]
  rw [hroot]
  change _ ≤ 3 / 4 * c + 1 / 4 * (Real.sqrt a * Real.sqrt b / c)
  apply (mul_le_mul_iff_of_pos_right hc).mp
  field_simp
  nlinarith [sq_nonneg (c - (Real.sqrt a + Real.sqrt b) / 2),
    Real.sq_sqrt ha, Real.sq_sqrt hb]

private theorem expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform_fin {n : ℕ}
    {f : (Fin n → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x, Real.sqrt (f x)) ≤
      bernoulliAverage (1 / 4) (fun selected => Real.sqrt (harmonicTransform f selected)) := by
  induction n with
  | zero =>
    have he : f = fun _ => f (fun i => Fin.elim0 i) :=
      funext fun x => congrArg f (Subsingleton.elim _ _)
    rw [he]
    simp [harmonicTransform_const, bernoulliAverage_const]
  | succ n ih =>
    let f0 := fun x => f (Fin.cons false x)
    let f1 := fun x => f (Fin.cons true x)
    have h0 : ∀ x, 0 ≤ f0 x := fun x => hf (Fin.cons false x)
    have h1 : ∀ x, 0 ≤ f1 x := fun x => hf (Fin.cons true x)
    have hi0 := ih h0
    have hi1 := ih h1
    have hpoint (s : Fin n → Bool) :
        1 / 2 * Real.sqrt (harmonicTransform f0 s) +
          1 / 2 * Real.sqrt (harmonicTransform f1 s) ≤
        3 / 4 * Real.sqrt (harmonicTransform (fun x => (f0 x + f1 x) / 2) s) +
          1 / 4 * Real.sqrt (harmonicTransform f (Fin.cons true s)) := by
      have hb := add_sqrt_div_two_le
        (harmonicTransform_nonneg h0 s) (harmonicTransform_nonneg h1 s)
      have hc := Real.sqrt_le_sqrt (harmonicTransform_midpoint h0 h1 s)
      rw [harmonicTransform_cons_true hf]
      dsimp [f0, f1] at hb hc ⊢
      linarith
    rw [expect_univ_fin_cons]
    calc
      _ ≤ 1 / 2 * bernoulliAverage (1 / 4) (fun s => Real.sqrt (harmonicTransform f0 s)) +
          1 / 2 * bernoulliAverage (1 / 4) (fun s => Real.sqrt (harmonicTransform f1 s)) := by
        dsimp [f0, f1] at hi0 hi1
        linarith
      _ = bernoulliAverage (1 / 4) (fun s =>
          1 / 2 * Real.sqrt (harmonicTransform f0 s) +
            1 / 2 * Real.sqrt (harmonicTransform f1 s)) := by
        rw [bernoulliAverage_add, bernoulliAverage_const_mul, bernoulliAverage_const_mul]
      _ ≤ bernoulliAverage (1 / 4) (fun s =>
          3 / 4 * Real.sqrt (harmonicTransform (fun x => (f0 x + f1 x) / 2) s) +
            1 / 4 * Real.sqrt (harmonicTransform f (Fin.cons true s))) :=
        bernoulliAverage_mono (by norm_num) (by norm_num) hpoint
      _ = _ := by
        rw [bernoulliAverage_add, bernoulliAverage_const_mul, bernoulliAverage_const_mul,
          bernoulliAverage_cons]
        simp_rw [harmonicTransform_cons_false]
        norm_num
        rfl

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Korten's harmonic mean inequality** [Korten, Lemma 12][Korten2026]: on the `1/4`-biased
coordinate cube, the mean square root of the harmonic transform dominates the uniform mean square
root of `f`. -/
theorem expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform {f : (ι → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x, Real.sqrt (f x)) ≤
      bernoulliAverage (1 / 4) (fun selected => Real.sqrt (harmonicTransform f selected)) := by
  let e := (Fintype.equivFin ι).symm
  have h := expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform_fin
    (f := fun y => f (fun j => y (e.symm j))) (fun _ => hf _)
  simp_rw [harmonicTransform_reindex e] at h
  rwa [bernoulliAverage_reindex e (1 / 4) (fun s => Real.sqrt (harmonicTransform f s)),
    Fintype.expect_equiv (Equiv.arrowCongr e (Equiv.refl Bool))
      (fun x => Real.sqrt (f (fun j => x (e.symm j)))) (fun x => Real.sqrt (f x))
      (fun _ => rfl)] at h

/-! ### Dense distributions and good coordinate projections

The first probability estimate in the proof of Korten's Lemma 10, before transference to a sparse
coordinate set. We use a pointwise density bound `B` instead of writing it as `2 ^ k`. -/

/-- Intermediate estimate in the proof of Lemma 10: a normalized density bounded
by `B` has harmonic transform at least `1 / (4 * B)` with probability at least
`1 / (2 * sqrt B)` under `1/4`-coordinate sampling. The `LightPatterns` module
transfers this estimate to sparse sampling. -/
theorem harmonicTransform_good_probability
    {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (hmean : (𝔼 x, f x) = 1)
    {B : ℝ} (hB : 1 ≤ B) (hbound : ∀ x, f x ≤ B) :
    1 / (2 * Real.sqrt B) ≤ bernoulliAverage (1 / 4)
      (fun selected => if 1 / (4 * B) ≤ harmonicTransform f selected then 1 else 0) := by
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hBs : 0 < Real.sqrt B := Real.sqrt_pos.mpr hBp
  let a := 1 / (2 * Real.sqrt B)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha2 : a ^ 2 = 1 / (4 * B) := by
    dsimp [a]
    rw [div_pow, mul_pow, Real.sq_sqrt hBp.le]
    norm_num
  have hlower : 1 / Real.sqrt B ≤ 𝔼 x, Real.sqrt (f x) := by
    apply (div_le_iff₀ hBs).mpr
    rw [← hmean, expect_mul]
    apply expect_le_expect
    intro x _
    calc
      f x = Real.sqrt (f x) * Real.sqrt (f x) := (Real.mul_self_sqrt (hf x)).symm
      _ ≤ Real.sqrt (f x) * Real.sqrt B :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hbound x)) (Real.sqrt_nonneg _)
  have hpoint (s : ι → Bool) : Real.sqrt (harmonicTransform f s) ≤
      a + if 1 / (4 * B) ≤ harmonicTransform f s then 1 else 0 := by
    by_cases hs : 1 / (4 * B) ≤ harmonicTransform f s
    · rw [ite_eq_left hs]
      have hupper : Real.sqrt (harmonicTransform f s) ≤ 1 := by
        have h := Real.sqrt_le_sqrt (harmonicTransform_le_expect hf s)
        simpa [hmean] using h
      linarith
    · rw [ite_eq_right hs, add_zero]
      calc
        _ ≤ Real.sqrt (1 / (4 * B)) := Real.sqrt_le_sqrt (le_of_not_ge hs)
        _ = a := by rw [← ha2, Real.sqrt_sq ha]
  have havg := bernoulliAverage_mono (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 : ℝ) / 4 ≤ 1) hpoint
  rw [bernoulliAverage_add, bernoulliAverage_const] at havg
  have hmain := expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform hf
  have ha' : 2 * a = 1 / Real.sqrt B := by dsimp [a]; field_simp
  linarith

/-- A positive transform lower bound bounds the fraction of light projected
patterns. The expectation ranges over the actual selected-coordinate cube. -/
theorem coordinateMarginal_light_fraction_le {f : (ι → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (selected : ι → Bool) {a b : ℝ} (ha : 0 < a)
    (ha' : a ≤ harmonicTransform f selected) (hb : 0 ≤ b) :
    (𝔼 z, if coordinateMarginal f selected z ≤ b then (1 : ℝ) else 0) ≤ b / a := by
  rw [harmonicTransform_eq_harmonicMean_coordinateMarginal] at ha'
  exact harmonicMean_light_fraction_le
    (fun _ => Finset.expect_nonneg fun _ _ => hf _) ha ha' hb

end

end Cslib.BitString
