/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Probability.PMF
public import Mathlib.Analysis.Real.Sqrt
import Complexity.Probability.PMF

/-!
# The rewinding lemma

A two-stage experiment runs a first stage with outcome `s`, draws a challenge `t` uniformly from
a nonempty finite type `T`, and lets a second stage answer `t` from `s`; it succeeds when a test
`ok s t a` of the answer `a` passes. *Rewinding* keeps `s` and reruns the second stage on a fresh
independent challenge. Boneh and Shoup's rewinding lemma ([BonehShoup2023], Lemma 19.2) says
that if one run succeeds with probability `ε` and `N` is the number of challenges, then both runs
succeed with distinct challenges with probability at least `ε² − ε / N`
(`sq_sub_le_twice`). Consequently `ε ≤ 1 / N + √δ` for that probability `δ`
(`le_inv_add_sqrt_twice`), the form that turns a bound on `δ` into one on `ε`.

The second stage may use fresh randomness in each run. This generalizes the book's
deterministic `f(X, Y)`: averaging over the second stage's coins turns the indicator into a
success probability `p(s, t) ∈ [0, 1]`, and the proof needs only `p ^ 2 ≤ p`. The first stage
may have infinitely many outcomes. The statements are exact; no efficiency is involved.

The experiments are written in `do` notation for `PMF`, whose monad lives in a single universe;
since they return a `PMF Bool`, the outcome, challenge and answer types are in `Type`.

## Main definitions

* `Cslib.Probability.Rewinding.once`: one run of the two-stage experiment.
* `Cslib.Probability.Rewinding.twice`: two runs sharing the first stage, with independent
  challenges and second-stage randomness.

## Main results

* `Cslib.Probability.Rewinding.sq_sub_le_twice`: `ε² − ε / N ≤ δ` ([BonehShoup2023], Lemma 19.2).
* `Cslib.Probability.Rewinding.le_inv_add_sqrt_twice`: `ε ≤ 1 / N + √δ`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Lemma 19.2 and the proof of Theorem 19.1.
-/

@[expose] public section

namespace Cslib.Probability.Rewinding

variable {S T A : Type} [Fintype T] [Nonempty T]

/-- One run of a two-stage experiment: the first stage, a uniform challenge `t`, the second
stage's answer `a` to `t`, and the test `ok s t a`. -/
noncomputable def once (first : PMF S) (answer : S → T → PMF A) (ok : S → T → A → Bool) :
    PMF Bool := do
  let s ← first
  let t ← PMF.uniformOfFintype T
  let a ← answer s t
  return ok s t a

/-- Rewinding: one first stage, then the second stage on two independent uniform challenges with
independent randomness. It succeeds when both answers pass their tests and the challenges are
distinct. -/
noncomputable def twice [DecidableEq T] (first : PMF S) (answer : S → T → PMF A)
    (ok : S → T → A → Bool) : PMF Bool := do
  let s ← first
  let t ← PMF.uniformOfFintype T
  let t' ← PMF.uniformOfFintype T
  let a ← answer s t
  let a' ← answer s t'
  return (ok s t a && ok s t' a' && t != t')

/-! ### Proof of the rewinding lemma -/

/-- Jensen's inequality `E[g]² ≤ E[g²]` for a function with values in `[0, 1]`. -/
private theorem sq_tsum_le_tsum_sq {α : Type*} (μ : PMF α) {g : α → ℝ} (h0 : ∀ a, 0 ≤ g a)
    (h1 : ∀ a, g a ≤ 1) :
    (∑' a, (μ a).toReal * g a) ^ 2 ≤ ∑' a, (μ a).toReal * g a ^ 2 := by
  have hm : Summable fun a => (μ a).toReal := Probability.PMF.summable_toReal μ
  have hbounded {f : α → ℝ} (f0 : ∀ a, 0 ≤ f a) (f1 : ∀ a, f a ≤ 1) :
      Summable fun a => (μ a).toReal * f a :=
    hm.of_nonneg_of_le (fun a => mul_nonneg ENNReal.toReal_nonneg (f0 a))
      fun a => mul_le_of_le_one_right ENNReal.toReal_nonneg (f1 a)
  have hg := hbounded h0 h1
  have hg2 := hbounded (fun a => sq_nonneg (g a)) fun a => pow_le_one₀ (h0 a) (h1 a)
  set e := ∑' a, (μ a).toReal * g a
  have hexpand : ∑' a, (μ a).toReal * (g a - e) ^ 2 =
      ∑' a, (μ a).toReal * g a ^ 2 - e ^ 2 := by
    have hsplit : (fun a => (μ a).toReal * (g a - e) ^ 2) = fun a =>
        ((μ a).toReal * g a ^ 2 - 2 * e * ((μ a).toReal * g a)) + e ^ 2 * (μ a).toReal := by
      funext a
      ring
    rw [hsplit, (hg2.sub (hg.mul_left (2 * e))).tsum_add (hm.mul_left (e ^ 2)),
      hg2.tsum_sub (hg.mul_left (2 * e)), tsum_mul_left, tsum_mul_left,
      Probability.PMF.tsum_toReal]
    ring
  have hnonneg : 0 ≤ ∑' a, (μ a).toReal * (g a - e) ^ 2 :=
    tsum_nonneg fun a => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  linarith

/-- Two independent Boolean outcomes are both true, together with a fixed condition, with the
product probability. -/
private theorem bind_bind_and_apply (X Y : PMF A) (f g : A → Bool) (d : Bool) :
    (X.bind fun a => Y.bind fun a' => PMF.pure (f a && g a' && d)) true =
      if d then X.map f true * Y.map g true else 0 := by
  have hmap : (X.bind fun a => Y.bind fun a' => PMF.pure (f a && g a' && d)) =
      (X.map f).bind fun b => (Y.map g).bind fun b' => PMF.pure (b && b' && d) := by
    simp only [PMF.bind_map, Function.comp_def]
  rw [hmap]
  cases d
  · simp only [Bool.and_false, PMF.bind_const, PMF.pure_apply, Bool.true_eq_false,
      Bool.false_eq_true, ite_false]
  · simp only [Bool.and_true, PMF.bind_apply, tsum_bool, PMF.pure_apply, Bool.and_false,
      Bool.true_eq_false, ite_false, ite_true, mul_zero, zero_add, mul_one]

/-- The success probability of the second stage at the challenge `t`. -/
private noncomputable def pass (answer : S → T → PMF A) (ok : S → T → A → Bool) (s : S) (t : T) :
    ℝ :=
  ((answer s t).map (ok s t) true).toReal

omit [Fintype T] [Nonempty T] in
private theorem pass_nonneg (answer : S → T → PMF A) (ok : S → T → A → Bool) (s : S) (t : T) :
    0 ≤ pass answer ok s t := ENNReal.toReal_nonneg

omit [Fintype T] [Nonempty T] in
private theorem pass_le_one (answer : S → T → PMF A) (ok : S → T → A → Bool) (s : S) (t : T) :
    pass answer ok s t ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by rw [ENNReal.ofReal_one]; exact PMF.coe_le_one _ true)

/-- The real probability of a uniform challenge's outcome. -/
private theorem toReal_uniformOfFintype (t : T) :
    (PMF.uniformOfFintype T t).toReal = (Fintype.card T : ℝ)⁻¹ := by
  simp only [Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- An average of values in `[0, 1]` lies in `[0, 1]`. -/
private theorem average_mem_Icc (f : T → ℝ) (h0 : ∀ t, 0 ≤ f t) (h1 : ∀ t, f t ≤ 1) :
    0 ≤ ∑ t, (Fintype.card T : ℝ)⁻¹ * f t ∧ ∑ t, (Fintype.card T : ℝ)⁻¹ * f t ≤ 1 := by
  have hN : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  refine ⟨Finset.sum_nonneg fun t _ => mul_nonneg (inv_nonneg.mpr hN.le) (h0 t), ?_⟩
  calc ∑ t, (Fintype.card T : ℝ)⁻¹ * f t ≤ ∑ _t : T, (Fintype.card T : ℝ)⁻¹ * 1 :=
        Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (h1 t) (inv_nonneg.mpr hN.le)
    _ = 1 := by simp [Finset.card_univ]

/-- The rewinding lemma for a single first-stage outcome: averaging the challenges,
`g ^ 2 - g / N ≤ h`, where `g` and `h` are one-run and two-run success probabilities. -/
private theorem sq_sub_le_pairs [DecidableEq T] (p : T → ℝ) (h0 : ∀ t, 0 ≤ p t)
    (h1 : ∀ t, p t ≤ 1) :
    (∑ t, (Fintype.card T : ℝ)⁻¹ * p t) ^ 2 - (∑ t, (Fintype.card T : ℝ)⁻¹ * p t) /
        Fintype.card T ≤
      ∑ t, (Fintype.card T : ℝ)⁻¹ * ∑ t', (Fintype.card T : ℝ)⁻¹ *
        (if t = t' then 0 else p t * p t') := by
  set N : ℝ := (Fintype.card T : ℝ)
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hoff (t : T) : ∑ t', (if t = t' then 0 else p t * p t') =
      p t * ∑ t', p t' - p t * p t := by
    have hite : (fun t' => if t = t' then 0 else p t * p t') =
        fun t' => p t * p t' - if t = t' then p t * p t' else 0 := by
      funext t'
      split_ifs <;> ring
    rw [hite, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq,
      ite_eq_left (Finset.mem_univ t)]
  have hsq : ∑ t, p t * p t ≤ ∑ t, p t :=
    Finset.sum_le_sum fun t _ => mul_le_of_le_one_left (h0 t) (h1 t)
  simp only [← Finset.mul_sum, hoff, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hinv : 0 ≤ N⁻¹ := inv_nonneg.mpr hN.le
  calc (N⁻¹ * ∑ t, p t) ^ 2 - (N⁻¹ * ∑ t, p t) / N
      = N⁻¹ * (N⁻¹ * ((∑ t, p t) * ∑ t, p t - ∑ t, p t)) := by
        rw [div_eq_mul_inv]
        ring
    _ ≤ N⁻¹ * (N⁻¹ * ((∑ t, p t) * ∑ t, p t - ∑ t, p t * p t)) := by
        gcongr

/-- One run succeeds with the average over the first stage of the averaged second-stage success
probability. -/
private theorem toReal_once (first : PMF S) (answer : S → T → PMF A) (ok : S → T → A → Bool) :
    (once first answer ok true).toReal =
      ∑' s, (first s).toReal * ∑ t, (Fintype.card T : ℝ)⁻¹ * pass answer ok s t := by
  simp only [once, Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure]
  rw [Probability.PMF.bind_apply_toReal_tsum]
  refine tsum_congr fun s => congrArg _ ?_
  rw [Probability.PMF.bind_apply_toReal]
  simp only [toReal_uniformOfFintype]
  rfl

/-- Two runs succeed with the average over the first stage of the averaged product of two
second-stage success probabilities at distinct challenges. -/
private theorem toReal_twice [DecidableEq T] (first : PMF S) (answer : S → T → PMF A)
    (ok : S → T → A → Bool) :
    (twice first answer ok true).toReal =
      ∑' s, (first s).toReal * ∑ t, (Fintype.card T : ℝ)⁻¹ * ∑ t', (Fintype.card T : ℝ)⁻¹ *
        (if t = t' then 0 else pass answer ok s t * pass answer ok s t') := by
  simp only [twice, Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure]
  rw [Probability.PMF.bind_apply_toReal_tsum]
  refine tsum_congr fun s => congrArg _ ?_
  rw [Probability.PMF.bind_apply_toReal]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Probability.PMF.bind_apply_toReal, toReal_uniformOfFintype]
  refine congrArg _ (Finset.sum_congr rfl fun t' _ => ?_)
  rw [toReal_uniformOfFintype, bind_bind_and_apply]
  by_cases h : t = t' <;> simp [h, pass, ENNReal.toReal_mul]

/-! ### The rewinding lemma -/

variable [DecidableEq T] (first : PMF S) (answer : S → T → PMF A) (ok : S → T → A → Bool)

/-- **Rewinding lemma** ([BonehShoup2023], Lemma 19.2): if one run succeeds with probability `ε`,
then two runs sharing the first stage succeed with distinct challenges with probability at least
`ε ^ 2 - ε / N`, where `N` is the number of challenges. -/
theorem sq_sub_le_twice :
    (once first answer ok true).toReal ^ 2 -
        (once first answer ok true).toReal / Fintype.card T ≤
      (twice first answer ok true).toReal := by
  set N : ℝ := (Fintype.card T : ℝ)
  set p := pass answer ok
  set g : S → ℝ := fun s => ∑ t, N⁻¹ * p s t
  set h : S → ℝ := fun s => ∑ t, N⁻¹ * ∑ t', N⁻¹ * (if t = t' then 0 else p s t * p s t')
  have hg (s : S) : 0 ≤ g s ∧ g s ≤ 1 :=
    average_mem_Icc _ (pass_nonneg answer ok s) (pass_le_one answer ok s)
  have hpair (s : S) (t t' : T) :
      0 ≤ (if t = t' then 0 else p s t * p s t') ∧ (if t = t' then 0 else p s t * p s t') ≤ 1 := by
    split_ifs
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨mul_nonneg (pass_nonneg _ _ _ _) (pass_nonneg _ _ _ _),
        (mul_le_mul (pass_le_one _ _ _ _) (pass_le_one _ _ _ _) (pass_nonneg _ _ _ _)
          zero_le_one).trans_eq (one_mul 1)⟩
  have hh (s : S) : 0 ≤ h s ∧ h s ≤ 1 := by
    refine average_mem_Icc _ (fun t => (average_mem_Icc _ (fun t' => (hpair s t t').1)
      fun t' => (hpair s t t').2).1) fun t => (average_mem_Icc _ (fun t' => (hpair s t t').1)
      fun t' => (hpair s t t').2).2
  have hm : Summable fun s => (first s).toReal := Probability.PMF.summable_toReal first
  have hsum {f : S → ℝ} (f0 : ∀ s, 0 ≤ f s) (f1 : ∀ s, f s ≤ 1) :
      Summable fun s => (first s).toReal * f s :=
    hm.of_nonneg_of_le (fun s => mul_nonneg ENNReal.toReal_nonneg (f0 s))
      fun s => mul_le_of_le_one_right ENNReal.toReal_nonneg (f1 s)
  have hsumg := hsum (fun s => (hg s).1) fun s => (hg s).2
  have hsumg2 := hsum (fun s => sq_nonneg (g s)) fun s => pow_le_one₀ (hg s).1 (hg s).2
  have hsumh := hsum (fun s => (hh s).1) fun s => (hh s).2
  have hpoint (s : S) :
      (first s).toReal * g s ^ 2 - (first s).toReal * g s / N ≤ (first s).toReal * h s := by
    rw [mul_div_assoc, ← mul_sub]
    exact mul_le_mul_of_nonneg_left
      (sq_sub_le_pairs (p s) (pass_nonneg answer ok s) (pass_le_one answer ok s))
      ENNReal.toReal_nonneg
  rw [toReal_once, toReal_twice]
  calc (∑' s, (first s).toReal * g s) ^ 2 - (∑' s, (first s).toReal * g s) / N
      ≤ ∑' s, (first s).toReal * g s ^ 2 - (∑' s, (first s).toReal * g s) / N := by
        gcongr
        exact sq_tsum_le_tsum_sq first (fun s => (hg s).1) fun s => (hg s).2
    _ = ∑' s, ((first s).toReal * g s ^ 2 - (first s).toReal * g s / N) := by
        rw [hsumg2.tsum_sub (hsumg.div_const N), tsum_div_const]
    _ ≤ ∑' s, (first s).toReal * h s :=
        (hsumg2.sub (hsumg.div_const N)).tsum_le_tsum hpoint hsumh

/-- The rewinding lemma solved for the one-run probability ([BonehShoup2023], from the proof of
Theorem 19.1): `ε ≤ 1 / N + √δ`. -/
theorem le_inv_add_sqrt_twice :
    (once first answer ok true).toReal ≤
      1 / Fintype.card T + √(twice first answer ok true).toReal := by
  set ε := (once first answer ok true).toReal
  set N : ℝ := (Fintype.card T : ℝ)
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hδ := sq_sub_le_twice first answer ok
  by_cases hε : ε ≤ 1 / N
  · exact hε.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  · have hsq : (ε - 1 / N) ^ 2 ≤ (twice first answer ok true).toReal := by
      refine le_trans ?_ hδ
      have : (ε - 1 / N) ^ 2 = ε ^ 2 - ε / N - (ε - 1 / N) / N := by
        field_simp
      rw [this]
      exact sub_le_self _ (div_nonneg (by linarith) hN.le)
    have := Real.abs_le_sqrt hsq
    linarith [le_abs_self (ε - 1 / N)]

end Cslib.Probability.Rewinding
