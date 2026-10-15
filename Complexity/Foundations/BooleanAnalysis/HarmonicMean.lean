/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.Bernoulli
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FunProp

/-!
# Korten's harmonic mean transform

This module formalizes Definition 5, Lemmas 11--12, and Corollary 1 of [Korten2026].

`harmonicMean_variational` works on any nonempty finite type. The coordinate
transform uses Boolean membership functions for sets and real nonnegative
densities. `harmonicTransform_eq_harmonicMean_coordinateMarginal` identifies
the convenient full-cube representation with the harmonic mean over actual
projected patterns. Zero entries give harmonic mean zero, as in the paper.

`expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform` is Lemma 12, including
dimension zero. `harmonicTransform_good_probability` supplies the intermediate
1/4-sampling estimate in the proof of Lemma 10, using a density bound `B` in
place of `2 ^ k`. The sparse-sampling conclusion and pattern count of Lemma 10
are proved in `Complexity.Foundations.BooleanAnalysis.LightPatterns`, which feeds the
mirror-set argument of `Complexity.Foundations.BooleanAnalysis.MirrorSets`. The top-down
communication and circuit lower bounds of Theorem 3 are
`Complexity.KarchmerWigderson.parity_communication_lower_bound` and
`Complexity.Circuit.parity_wire_lower_bound` in
`Complexitylib.Circuits.KarchmerWigderson.TopDown`.
-/

@[expose] public section

/-! ### Harmonic means and coordinate projections

Definitions for Section 4 of [Korten2026].

The harmonic mean is zero if any value is zero. This implements the paper's
extended-real convention without using the real-number convention `0⁻¹ = 0`
inside the average. Theorems assume nonnegative inputs.

A coordinate set is its Boolean membership function. Projections are represented
on the full cube: their value depends only on the selected coordinates. Averaging
on the full cube gives each projected pattern the same multiplicity, so this is
the uniform average over projected patterns. All expectations are finite sums.
-/


namespace Cslib.BooleanAnalysis

open scoped BigOperators

/-- The uniform harmonic mean, with value zero whenever an entry is zero. -/
noncomputable def harmonicMean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  if ∃ x, f x = 0 then 0 else (𝔼 x, (f x)⁻¹)⁻¹

/-- Average over the unselected coordinates, keeping the selected bits of `x`. -/
noncomputable def projectionAverage {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (selected x : ι → Bool) : ℝ := by
  classical
  exact 𝔼 y : ι → Bool, f (fun i => if selected i then x i else y i)

/-- The marginal on actual selected-coordinate patterns, obtained by uniformly
averaging over their completions. For a normalized density `f`, this is the
normalized density of its coordinate projection. -/
noncomputable def coordinateMarginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (selected : ι → Bool)
    (pattern : {i // selected i = true} → Bool) : ℝ :=
  𝔼 rest : {i // selected i ≠ true} → Bool,
    f (fun i => if h : selected i = true then pattern ⟨i, h⟩ else rest ⟨i, h⟩)

/-- Korten's harmonic mean transform (Definition 5), represented on the full cube. -/
noncomputable def harmonicTransform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (selected : ι → Bool) : ℝ := by
  classical
  exact harmonicMean (projectionAverage f selected)


end Cslib.BooleanAnalysis

/-! ### Finite harmonic mean: proof internals

The variational formula of Korten (2026), Lemma 11, is proved for every
nonempty finite type. Completing the square gives the lower bound, and an
explicit weight attains it, including when an entry vanishes.
-/


namespace Cslib.BooleanAnalysis

open Finset
open scoped BigOperators

variable {α : Type*} [Fintype α] [Nonempty α]

omit [Nonempty α] in
/-- Harmonic means of nonnegative entries are nonnegative. -/
theorem harmonicMean_nonneg {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ harmonicMean f := by
  unfold harmonicMean
  split_ifs
  · exact le_rfl
  · exact inv_nonneg.mpr (expect_nonneg fun x _ => inv_nonneg.mpr (hf x))

/-- Every weight with mean one bounds the harmonic mean by its quadratic energy.
The weight need not be nonnegative for this direction. -/
theorem harmonicMean_le_energy {f w : α → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hw : (𝔼 x, w x) = 1) : harmonicMean f ≤ 𝔼 x, f x * w x ^ 2 := by
  classical
  by_cases hz : ∃ x, f x = 0
  · rw [harmonicMean, ite_eq_left hz]
    exact expect_nonneg fun x _ => mul_nonneg (hf x) (sq_nonneg _)
  have hpos : ∀ x, 0 < f x := fun x => lt_of_le_of_ne (hf x) (Ne.symm (by
    intro h; exact hz ⟨x, h⟩))
  have he : (𝔼 x, (f x)⁻¹) ≠ 0 := ne_of_gt
    (expect_pos (fun x _ => inv_pos.mpr (hpos x)) univ_nonempty)
  let h := (𝔼 x, (f x)⁻¹)⁻¹
  have hs := expect_nonneg (s := univ)
    (fun x _ => mul_nonneg (hf x) (sq_nonneg (w x - h / f x)))
  have hid (x : α) : f x * (w x - h / f x) ^ 2 =
      f x * w x ^ 2 - 2 * h * w x + h ^ 2 * (f x)⁻¹ := by
    field_simp [ne_of_gt (hpos x)]
    ring
  simp_rw [hid, expect_add_distrib, expect_sub_distrib, ← mul_expect] at hs
  rw [hw] at hs
  have hh : h ^ 2 * (𝔼 x, (f x)⁻¹) = h := by
    dsimp [h]
    field_simp
  rw [hh] at hs
  rw [harmonicMean, ite_eq_right hz]
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
    · rw [harmonicMean, ite_eq_left ⟨a, ha⟩]
      apply expect_eq_zero
      intro x _
      by_cases hx : x = a <;> simp [hx, ha]
  · have hpos : ∀ x, 0 < f x := fun x => lt_of_le_of_ne (hf x) (Ne.symm (by
      intro h; exact hz ⟨x, h⟩))
    have he : (𝔼 x, (f x)⁻¹) ≠ 0 := ne_of_gt
      (expect_pos (fun x _ => inv_pos.mpr (hpos x)) univ_nonempty)
    let h := (𝔼 x, (f x)⁻¹)⁻¹
    refine ⟨fun x => h * (f x)⁻¹, ?_, ?_, ?_⟩
    · intro x
      exact mul_nonneg (inv_nonneg.mpr
        (expect_nonneg fun x _ => inv_nonneg.mpr (hf x))) (inv_nonneg.mpr (hf x))
    · rw [← mul_expect]
      exact inv_mul_cancel₀ he
    · have hid (x : α) : f x * (h * (f x)⁻¹) ^ 2 = h ^ 2 * (f x)⁻¹ := by
        field_simp [ne_of_gt (hpos x)]
      simp_rw [hid, ← mul_expect]
      rw [harmonicMean, ite_eq_right hz]
      dsimp [h]
      field_simp

/-- Korten's Lemma 11, generalized to every nonempty finite type. -/
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

/-- Harmonic means are concave on nonnegative functions. -/
theorem harmonicMean_concave {f g : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    t * harmonicMean f + (1 - t) * harmonicMean g ≤
      harmonicMean (fun x => t * f x + (1 - t) * g x) := by
  obtain ⟨w, _, hw, he⟩ := harmonicMean_exists_weight
    (fun x => add_nonneg (mul_nonneg ht (hf x)) (mul_nonneg (sub_nonneg.mpr ht') (hg x)))
  calc
    _ ≤ t * (𝔼 x, f x * w x ^ 2) + (1 - t) * (𝔼 x, g x * w x ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left (harmonicMean_le_energy hf hw) ht)
        (mul_le_mul_of_nonneg_left (harmonicMean_le_energy hg hw)
          (sub_nonneg.mpr ht'))
    _ = 𝔼 x, (t * f x + (1 - t) * g x) * w x ^ 2 := by
      simp_rw [add_mul, mul_assoc, expect_add_distrib, ← mul_expect]
    _ = _ := he

/-- The harmonic mean is at most the arithmetic mean. -/
theorem harmonicMean_le_expect {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    harmonicMean f ≤ 𝔼 x, f x := by
  simpa using harmonicMean_le_energy (w := fun _ => 1) hf (by simp)

/-- The harmonic mean of a constant on a nonempty finite set is that constant. -/
theorem harmonicMean_const (c : ℝ) :
    harmonicMean (fun _ : α => c) = c := by
  classical
  by_cases hc : c = 0 <;> simp [harmonicMean, hc]

omit [Nonempty α] in
theorem harmonicMean_equiv {β : Type*} [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : harmonicMean (fun x => f (e x)) = harmonicMean f := by
  classical
  have hz : (∃ x, f (e x) = 0) ↔ ∃ y, f y = 0 := by
    constructor
    · rintro ⟨x, hx⟩; exact ⟨e x, hx⟩
    · rintro ⟨y, hy⟩; exact ⟨e.symm y, by simpa⟩
  simp only [harmonicMean, hz]
  rw [Fintype.expect_equiv e (fun x => (f (e x))⁻¹) (fun y => (f y)⁻¹)
    (fun _ => rfl)]

theorem harmonicMean_average {β : Type*} [Fintype β]
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

omit [Nonempty α] in
theorem expect_pair {β : Type*} [Fintype β] (f : α × β → ℝ) :
    (𝔼 x, f x) = 𝔼 a, 𝔼 b, f (a, b) := by
  simpa only [univ_product_univ] using expect_product univ univ f

theorem expect_bool (f : Bool → ℝ) :
    (𝔼 b, f b) = (f false + f true) / 2 := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.sum_bool]
  simp only [Fintype.card_bool, Nat.cast_ofNat]
  ring

theorem harmonicMean_pair {f : Bool → α → ℝ} (hf : ∀ b x, 0 ≤ f b x) :
    harmonicMean (fun x : Bool × α => f x.1 x.2) =
      2 * harmonicMean (f false) * harmonicMean (f true) /
        (harmonicMean (f false) + harmonicMean (f true)) := by
  classical
  by_cases h0 : ∃ x, f false x = 0
  · have hz : ∃ x : Bool × α, f x.1 x.2 = 0 := by
      obtain ⟨x, hx⟩ := h0; exact ⟨(false, x), hx⟩
    simp [harmonicMean, h0, hz]
  by_cases h1 : ∃ x, f true x = 0
  · have hz : ∃ x : Bool × α, f x.1 x.2 = 0 := by
      obtain ⟨x, hx⟩ := h1; exact ⟨(true, x), hx⟩
    simp [harmonicMean, h1, hz]
  have hz : ¬ ∃ x : Bool × α, f x.1 x.2 = 0 := by
    rintro ⟨⟨b, x⟩, hx⟩
    cases b
    · exact h0 ⟨x, hx⟩
    · exact h1 ⟨x, hx⟩
  have hp (b : Bool) : 0 < 𝔼 x, (f b x)⁻¹ := by
    apply expect_pos _ univ_nonempty
    intro x _
    apply inv_pos.mpr
    have hn : f b x ≠ 0 := fun h => hz ⟨(b, x), h⟩
    exact lt_of_le_of_ne (hf b x) hn.symm
  simp only [harmonicMean, ite_eq_right hz, ite_eq_right h0, ite_eq_right h1]
  rw [expect_pair, expect_bool]
  have hsum := add_pos (hp false) (hp true)
  field_simp [ne_of_gt (hp false), ne_of_gt (hp true), ne_of_gt hsum]
  simpa only [one_div, add_comm] using (div_self (ne_of_gt hsum)).symm

/-- A positive harmonic-mean lower bound controls the fraction of small entries.
This is the reciprocal-density Markov step used for light patterns. -/
theorem harmonicMean_light_fraction_le {f : α → ℝ} (hf : ∀ x, 0 ≤ f x)
    {a b : ℝ} (ha : 0 < a) (ha' : a ≤ harmonicMean f) (hb : 0 ≤ b) :
    (𝔼 x, if f x ≤ b then (1 : ℝ) else 0) ≤ b / a := by
  classical
  have hz : ¬ ∃ x, f x = 0 := by
    intro h
    rw [harmonicMean, ite_eq_left h] at ha'
    exact (not_le_of_gt ha) ha'
  have hp (x : α) : 0 < f x :=
    lt_of_le_of_ne (hf x) (Ne.symm fun h => hz ⟨x, h⟩)
  have he : 0 < 𝔼 x, (f x)⁻¹ :=
    expect_pos (fun x _ => inv_pos.mpr (hp x)) univ_nonempty
  have hinv : (𝔼 x, (f x)⁻¹) ≤ 1 / a := by
    rw [harmonicMean, ite_eq_right hz, ← one_div] at ha'
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

end Cslib.BooleanAnalysis

/-! ### Reindexing coordinate projections

Transport the harmonic transform along an equivalence of finite coordinate
types. This lets results proved by induction on `Fin n` apply inside fibers.
-/


namespace Cslib.BooleanAnalysis

theorem projectionAverage_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (f : (κ → Bool) → ℝ)
    (s x : ι → Bool) :
    projectionAverage (fun y => f (fun j => y (e.symm j))) s x =
      projectionAverage f (fun j => s (e.symm j)) (fun j => x (e.symm j)) := by
  unfold projectionAverage
  exact Fintype.expect_equiv (Equiv.arrowCongr e (Equiv.refl Bool)) _ _ (fun _ => rfl)

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

end Cslib.BooleanAnalysis

/-! ### Marginal semantics of the harmonic mean transform

Splitting the cube into selected and unselected coordinates identifies the
full-cube representation with the paper's averages on projected patterns.
-/


namespace Cslib.BooleanAnalysis

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The full-cube projection depends exactly on the selected input pattern. -/
theorem projectionAverage_eq_coordinateMarginal
    (f : (ι → Bool) → ℝ) (selected x : ι → Bool) :
    projectionAverage f selected x = coordinateMarginal f selected (fun i => x i) := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => selected i = true) (fun _ => Bool)
  have he (z : ({i // selected i = true} → Bool) × ({i // selected i ≠ true} → Bool)) :
      f (fun i => if h : selected i = true then x i else z.2 ⟨i, h⟩) =
      f (fun i => if selected i then x i else e.symm z i) := by
    congr 1
    funext i
    by_cases hi : selected i = true <;> simp [e, Equiv.piEquivPiSubtypeProd, hi]
  unfold projectionAverage
  rw [← Fintype.expect_equiv e.symm _ _ he, expect_pair]
  exact Fintype.expect_const (ι := {i // selected i = true} → Bool)
    (coordinateMarginal f selected (fun i => x i))

/-- Marginalization preserves the uniform mean, hence also density normalization. -/
theorem expect_coordinateMarginal (f : (ι → Bool) → ℝ) (selected : ι → Bool) :
    (𝔼 z, coordinateMarginal f selected z) = 𝔼 x, f x := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => selected i = true) (fun _ => Bool)
  rw [← Fintype.expect_equiv e.symm (fun z => f (e.symm z)) f (fun _ => rfl),
    expect_pair]
  rfl

/-- The transform agrees with Definition 5 on the actual projected cube;
repeating each pattern on the full cube does not change its harmonic mean. -/
theorem harmonicTransform_eq_harmonicMean_coordinateMarginal
    (f : (ι → Bool) → ℝ) (selected : ι → Bool) :
    harmonicTransform f selected = harmonicMean (coordinateMarginal f selected) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => selected i = true) (fun _ => Bool)
  have he (z : ({i // selected i = true} → Bool) × ({i // selected i ≠ true} → Bool)) :
      projectionAverage f selected (e.symm z) = coordinateMarginal f selected z.1 := by
    rw [projectionAverage_eq_coordinateMarginal]
    congr 1
    funext i
    simp [e, Equiv.piEquivPiSubtypeProd, i.property]
  rw [harmonicTransform, ← harmonicMean_equiv e.symm]
  simp_rw [he]
  simp [harmonicMean, expect_pair]

end Cslib.BooleanAnalysis

/-! ### Coordinate splitting for the harmonic mean transform

Finite product calculations used in the induction in Korten's Lemma 12.
-/


namespace Cslib.BooleanAnalysis

open Finset
open scoped BigOperators

theorem expect_cons {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    (𝔼 x, f x) = ((𝔼 x, f (Fin.cons false x)) + (𝔼 x, f (Fin.cons true x))) / 2 := by
  rw [← Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))
    (fun x => f (Fin.cons x.1 x.2)) f (fun _ => rfl)]
  rw [expect_pair, expect_bool]

theorem projectionAverage_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (selected x : ι → Bool) :
    0 ≤ projectionAverage f selected x :=
  expect_nonneg fun _ _ => hf _

/-- The harmonic transform is nonnegative on nonnegative functions. -/
theorem harmonicTransform_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (selected : ι → Bool) :
    0 ≤ harmonicTransform f selected :=
  harmonicMean_nonneg (projectionAverage_nonneg hf selected)

/-- Constants are fixed by the harmonic transform. -/
theorem harmonicTransform_const {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℝ) (selected : ι → Bool) : harmonicTransform (fun _ => c) selected = c := by
  have he : projectionAverage (fun _ => c) selected = fun _ => c := by
    funext x
    simp [projectionAverage]
  rw [harmonicTransform, he, harmonicMean_const]

theorem projectionAverage_midpoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : (ι → Bool) → ℝ) (selected x : ι → Bool) :
    projectionAverage (fun x => (f x + g x) / 2) selected x =
      (projectionAverage f selected x + projectionAverage g selected x) / 2 := by
  simp only [projectionAverage, ← expect_div, expect_add_distrib]

theorem projectionAverage_cons_false {n : ℕ}
    (f : (Fin (n + 1) → Bool) → ℝ) (selected x : Fin n → Bool) (b : Bool) :
    projectionAverage f (Fin.cons false selected) (Fin.cons b x) =
      projectionAverage (fun x => (f (Fin.cons false x) + f (Fin.cons true x)) / 2)
        selected x := by
  have hm (a : Bool) (y : Fin n → Bool) :
      (fun i : Fin (n + 1) => if (Fin.cons false selected : Fin (n + 1) → Bool) i then
        (Fin.cons b x : Fin (n + 1) → Bool) i else (Fin.cons a y : Fin (n + 1) → Bool) i) =
      Fin.cons a (fun i => if selected i then x i else y i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  unfold projectionAverage
  rw [expect_cons]
  simp_rw [hm]
  rw [← expect_div, expect_add_distrib]

theorem projectionAverage_cons_true {n : ℕ}
    (f : (Fin (n + 1) → Bool) → ℝ) (selected x : Fin n → Bool) (b : Bool) :
    projectionAverage f (Fin.cons true selected) (Fin.cons b x) =
      projectionAverage (fun x => f (Fin.cons b x)) selected x := by
  have hm (a : Bool) (y : Fin n → Bool) :
      (fun i : Fin (n + 1) => if (Fin.cons true selected : Fin (n + 1) → Bool) i then
        (Fin.cons b x : Fin (n + 1) → Bool) i else (Fin.cons a y : Fin (n + 1) → Bool) i) =
      Fin.cons b (fun i => if selected i then x i else y i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  unfold projectionAverage
  rw [expect_cons]
  simp_rw [hm]
  ring

theorem harmonicTransform_cons_false {n : ℕ}
    (f : (Fin (n + 1) → Bool) → ℝ) (selected : Fin n → Bool) :
    harmonicTransform f (Fin.cons false selected) =
      harmonicTransform
        (fun x => (f (Fin.cons false x) + f (Fin.cons true x)) / 2) selected := by
  classical
  unfold harmonicTransform
  rw [← harmonicMean_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))]
  change harmonicMean (fun x : Bool × (Fin n → Bool) =>
    projectionAverage f (Fin.cons false selected) (Fin.cons x.1 x.2)) = _
  simp_rw [projectionAverage_cons_false]
  simp [harmonicMean, expect_pair]

theorem harmonicTransform_cons_true {n : ℕ}
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

theorem harmonicTransform_midpoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f g : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (selected : ι → Bool) :
    (harmonicTransform f selected + harmonicTransform g selected) / 2 ≤
      harmonicTransform (fun x => (f x + g x) / 2) selected := by
  classical
  have h := harmonicMean_concave (projectionAverage_nonneg hf selected)
    (projectionAverage_nonneg hg selected) (t := 1 / 2) (by norm_num) (by norm_num)
  have he : (fun x => 1 / 2 * projectionAverage f selected x +
      (1 - 1 / 2) * projectionAverage g selected x) =
      projectionAverage (fun x => (f x + g x) / 2) selected := by
    funext x
    rw [projectionAverage_midpoint]
    ring
  rw [he] at h
  dsimp [harmonicTransform]
  linarith

end Cslib.BooleanAnalysis

/-! ### Order properties of the harmonic mean transform

The three parts of Corollary 1 in Korten (2026): concavity, decrease under
revealing more coordinates, and the upper bound by the ordinary mean.
-/


namespace Cslib.BooleanAnalysis

open Finset
open scoped BigOperators

theorem harmonicPair_le_midpoint {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * a * b / (a + b) ≤ (a + b) / 2 := by
  by_cases hz : a + b = 0
  · simp [hz]
  have hp : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hz)
  apply (div_le_iff₀ hp).mpr
  nlinarith [sq_nonneg (a - b)]

theorem harmonicPair_mono {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hac : a ≤ c) (hbd : b ≤ d) : 2 * a * b / (a + b) ≤ 2 * c * d / (c + d) := by
  have hc := ha.trans hac
  have hd := hb.trans hbd
  by_cases hz : a + b = 0
  · rw [hz, div_zero]
    positivity
  have hp : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hz)
  have hq : 0 < c + d := hp.trans_le (add_le_add hac hbd)
  apply (div_le_div_iff₀ hp hq).mpr
  nlinarith [mul_nonneg (mul_nonneg ha hc) (sub_nonneg.mpr hbd),
    mul_nonneg (mul_nonneg hb hd) (sub_nonneg.mpr hac)]

/-- Corollary 1(1): the transform is pointwise concave in its input function. -/
theorem harmonicTransform_concave {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f g : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) (selected : ι → Bool) :
    t * harmonicTransform f selected + (1 - t) * harmonicTransform g selected ≤
      harmonicTransform (fun x => t * f x + (1 - t) * g x) selected := by
  have he : projectionAverage (fun x => t * f x + (1 - t) * g x) selected =
      fun x => t * projectionAverage f selected x +
        (1 - t) * projectionAverage g selected x := by
    funext x
    simp only [projectionAverage, expect_add_distrib, ← mul_expect]
  unfold harmonicTransform
  rw [he]
  exact harmonicMean_concave (projectionAverage_nonneg hf selected)
    (projectionAverage_nonneg hg selected) ht ht'

/-- Corollary 1(2): revealing more coordinates decreases the harmonic transform.
The hypothesis is inclusion of the two sets represented by Boolean masks. -/
theorem harmonicTransform_antitone {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) {r s : Fin n → Bool}
    (hrs : ∀ i, r i = true → s i = true) : harmonicTransform f s ≤ harmonicTransform f r := by
  induction n with
  | zero => exact le_of_eq (congrArg (harmonicTransform f) (Subsingleton.elim _ _))
  | succ n ih =>
    obtain ⟨⟨rb, r⟩, rfl⟩ := (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).surjective r
    obtain ⟨⟨sb, s⟩, rfl⟩ := (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).surjective s
    change harmonicTransform f (Fin.cons sb s) ≤ harmonicTransform f (Fin.cons rb r)
    have htail : ∀ i, r i = true → s i = true := fun i => hrs i.succ
    have h0 := fun x => hf (Fin.cons false x)
    have h1 := fun x => hf (Fin.cons true x)
    have havg : ∀ x, 0 ≤ (f (Fin.cons false x) + f (Fin.cons true x)) / 2 :=
      fun x => div_nonneg (add_nonneg (h0 x) (h1 x)) (by norm_num)
    cases rb <;> cases sb
    · rw [harmonicTransform_cons_false, harmonicTransform_cons_false]
      exact ih havg htail
    · rw [harmonicTransform_cons_true hf, harmonicTransform_cons_false]
      exact (harmonicPair_le_midpoint (harmonicTransform_nonneg h0 s)
        (harmonicTransform_nonneg h1 s)).trans
        ((harmonicTransform_midpoint h0 h1 s).trans (ih havg htail))
    · have h := hrs 0 rfl
      contradiction
    · rw [harmonicTransform_cons_true hf, harmonicTransform_cons_true hf]
      exact harmonicPair_mono (harmonicTransform_nonneg h0 s)
        (harmonicTransform_nonneg h1 s) (ih h0 htail) (ih h1 htail)

/-- Selecting no coordinates gives the ordinary mean. -/
theorem harmonicTransform_empty {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) : harmonicTransform f (fun _ => false) = 𝔼 x, f x := by
  have he : projectionAverage f (fun _ => false) = fun _ => 𝔼 x, f x := by
    funext x
    simp [projectionAverage]
  rw [harmonicTransform, he, harmonicMean_const]

/-- Selecting all coordinates gives the harmonic mean of the original function. -/
theorem harmonicTransform_full {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) : harmonicTransform f (fun _ => true) = harmonicMean f := by
  have he : projectionAverage f (fun _ => true) = f := by
    funext x
    simp [projectionAverage]
  rw [harmonicTransform, he]

/-- Corollary 1(3): the harmonic transform is at most the ordinary mean. -/
theorem harmonicTransform_le_expect {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (selected : Fin n → Bool) :
    harmonicTransform f selected ≤ 𝔼 x, f x := by
  rw [← harmonicTransform_empty f]
  exact harmonicTransform_antitone hf (by simp)

end Cslib.BooleanAnalysis

/-! ### Korten's harmonic mean inequality: proof internals

Lemma 12 of *Top-Down Lower Bounds for All Depths* (2026). The scalar
inequality is followed by induction on dimension using concavity of the
harmonic mean. No strict-positivity assumption is needed.
-/


namespace Cslib.BooleanAnalysis

open Finset
open scoped BigOperators

theorem harmonicMean_sqrt_pair {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
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

/-- Korten's Lemma 12: on the `1/4`-biased coordinate cube, the mean square root
of the harmonic transform dominates the uniform mean square root of `f`. -/
theorem expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform {n : ℕ}
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
      have hb := harmonicMean_sqrt_pair
        (harmonicTransform_nonneg h0 s) (harmonicTransform_nonneg h1 s)
      have hc := Real.sqrt_le_sqrt (harmonicTransform_midpoint h0 h1 s)
      rw [harmonicTransform_cons_true hf]
      dsimp [f0, f1] at hb hc ⊢
      linarith
    rw [expect_cons]
    calc
      _ ≤ 1 / 2 * bernoulliAverage (1 / 4) (fun s => Real.sqrt (harmonicTransform f0 s)) +
          1 / 2 * bernoulliAverage (1 / 4) (fun s => Real.sqrt (harmonicTransform f1 s)) := by
        dsimp [f0, f1] at hi0 hi1
        linarith
      _ = bernoulliAverage (1 / 4) (fun s =>
          1 / 2 * Real.sqrt (harmonicTransform f0 s) +
            1 / 2 * Real.sqrt (harmonicTransform f1 s)) :=
        (bernoulliAverage_linear _ _ _ _ _).symm
      _ ≤ bernoulliAverage (1 / 4) (fun s =>
          3 / 4 * Real.sqrt (harmonicTransform (fun x => (f0 x + f1 x) / 2) s) +
            1 / 4 * Real.sqrt (harmonicTransform f (Fin.cons true s))) :=
        bernoulliAverage_mono (by norm_num) (by norm_num) hpoint
      _ = _ := by
        rw [bernoulliAverage_linear, bernoulliAverage_cons]
        simp_rw [harmonicTransform_cons_false]
        norm_num
        rfl

end Cslib.BooleanAnalysis

/-! ### Dense distributions and good coordinate projections

The first probability estimate in the proof of Korten's Lemma 10, before
transference to a sparse coordinate set. We use a pointwise density bound `B`
instead of writing it as `2 ^ k`.
-/


namespace Cslib.BooleanAnalysis

open Finset
open scoped BigOperators

/-- Intermediate estimate in the proof of Lemma 10: a normalized density bounded
by `B` has harmonic transform at least `1 / (4 * B)` with probability at least
`1 / (2 * sqrt B)` under `1/4`-coordinate sampling. The `LightPatterns` module
transfers this estimate to sparse sampling. -/
theorem harmonicTransform_good_probability {n : ℕ}
    {f : (Fin n → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (hmean : (𝔼 x, f x) = 1)
    {B : ℝ} (hB : 1 ≤ B) (hbound : ∀ x, f x ≤ B) :
    1 / (2 * Real.sqrt B) ≤ bernoulliAverage (1 / 4)
      (fun selected => if 1 / (4 * B) ≤ harmonicTransform f selected then 1 else 0) := by
  classical
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
  have hpoint (s : Fin n → Bool) : Real.sqrt (harmonicTransform f s) ≤
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
  have hlin := bernoulliAverage_linear (ι := Fin n) (1 / 4) 1 1 (fun _ => a)
    (fun s => if 1 / (4 * B) ≤ harmonicTransform f s then (1 : ℝ) else 0)
  simp only [one_mul, bernoulliAverage_const] at hlin
  rw [hlin] at havg
  have hmain := expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform hf
  have ha' : 2 * a = 1 / Real.sqrt B := by dsimp [a]; field_simp
  linarith

end Cslib.BooleanAnalysis



namespace Cslib.BooleanAnalysis

open scoped BigOperators

section Mean

variable {α : Type*} [Fintype α]

/-- A zero entry makes the harmonic mean zero, implementing `0⁻¹ = ∞`
inside the average rather than Lean's real inverse at zero. -/
theorem harmonicMean_eq_zero_of_exists {f : α → ℝ} (hf : ∃ x, f x = 0) :
    harmonicMean f = 0 := by
  rw [harmonicMean, ite_eq_left hf]

variable [Nonempty α]

end Mean

section Projection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lemma 11 on the selected-coordinate cube, with nonnegative weights of mean one. -/
theorem harmonicTransform_variational {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x)
    (selected : ι → Bool) :
    harmonicTransform f selected = sInf {a : ℝ |
      ∃ w : ({i // selected i = true} → Bool) → ℝ,
        (∀ z, 0 ≤ w z) ∧ (𝔼 z, w z) = 1 ∧
          (𝔼 z, coordinateMarginal f selected z * w z ^ 2) = a} := by
  rw [harmonicTransform_eq_harmonicMean_coordinateMarginal]
  exact harmonicMean_variational fun _ => Finset.expect_nonneg fun _ _ => hf _

/-- A positive transform lower bound bounds the fraction of light projected
patterns. The expectation ranges over the actual selected-coordinate cube. -/
theorem coordinateMarginal_light_fraction_le {f : (ι → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (selected : ι → Bool) {a b : ℝ} (ha : 0 < a)
    (ha' : a ≤ harmonicTransform f selected) (hb : 0 ≤ b) :
    (𝔼 z, if coordinateMarginal f selected z ≤ b then (1 : ℝ) else 0) ≤ b / a := by
  rw [harmonicTransform_eq_harmonicMean_coordinateMarginal] at ha'
  exact harmonicMean_light_fraction_le
    (fun _ => Finset.expect_nonneg fun _ _ => hf _) ha ha' hb

end Projection

end Cslib.BooleanAnalysis
