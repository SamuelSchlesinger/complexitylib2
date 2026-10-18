/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Finite quantiles with ties

For any proportion between zero and one, a nonempty finite collection of ordered scores has a
pivot whose weak lower and upper level sets contain the corresponding proportions. Equal scores
belong to both level sets; no injectivity or tie-breaking assumption is required.

## Main results

* `Finset.exists_quantile`: select a pivot retaining the requested proportions on both sides.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Lemma 2.1]
  [ThresholdCircuitRepresentations2026]
-/

@[expose] public section

namespace Finset

variable {α β : Type*} [LinearOrder β]

/-- A finite score collection has a quantile with large weak level sets on both sides.
The pivot itself is retained on both sides, so the statement includes tied scores. -/
theorem exists_quantile (s : Finset α) (hs : s.Nonempty) (score : α → β)
    {a : ℝ} (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    ∃ p ∈ s, a * s.card ≤ ((s.filter fun x => score x ≤ score p).card : ℝ) ∧
      (1 - a) * s.card ≤ ((s.filter fun x => score p ≤ score x).card : ℝ) := by
  classical
  let candidates := s.filter fun p =>
    a * s.card ≤ ((s.filter fun x => score x ≤ score p).card : ℝ)
  have hne : candidates.Nonempty := by
    obtain ⟨p, hp, hmax⟩ := s.exists_max_image score hs
    refine ⟨p, mem_filter.mpr ⟨hp, ?_⟩⟩
    rw [filter_true_of_mem hmax]
    nlinarith [Nat.cast_nonneg (α := ℝ) s.card]
  obtain ⟨p, hp, hmin⟩ := candidates.exists_min_image score hne
  obtain ⟨hps, hlo⟩ := mem_filter.mp hp
  refine ⟨p, hps, hlo, ?_⟩
  by_contra hupper
  have hsplit := s.card_filter_add_card_filter_not fun x => score p ≤ score x
  have hsplitR : ((s.filter fun x => score p ≤ score x).card : ℝ) +
      ((s.filter fun x => ¬ score p ≤ score x).card : ℝ) = s.card := by
    exact_mod_cast hsplit
  have hlow : a * s.card < ((s.filter fun x => ¬ score p ≤ score x).card : ℝ) := by
    linarith
  have hne' : (s.filter fun x => ¬ score p ≤ score x).Nonempty := by
    rw [← card_pos, ← Nat.cast_pos (α := ℝ)]
    exact (mul_nonneg ha (Nat.cast_nonneg _)).trans_lt hlow
  obtain ⟨p', hp', hmax⟩ := (s.filter fun x => ¬ score p ≤ score x).exists_max_image score hne'
  obtain ⟨hp's, hlt⟩ := mem_filter.mp hp'
  have hsub : (s.filter fun x => ¬ score p ≤ score x) ⊆
      s.filter fun x => score x ≤ score p' := fun x hx =>
    mem_filter.mpr ⟨(mem_filter.mp hx).1, hmax x hx⟩
  have hcard : ((s.filter fun x => ¬ score p ≤ score x).card : ℝ) ≤
      ((s.filter fun x => score x ≤ score p').card : ℝ) := by
    exact_mod_cast card_le_card hsub
  exact hlt (hmin p' (mem_filter.mpr ⟨hp's, hlow.le.trans hcard⟩))

end Finset
