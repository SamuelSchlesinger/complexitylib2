/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.BruteForce
public import Mathlib.Topology.Order.Real
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The exponents of `k`-SAT

The exponent `s_k` of `k`-SAT (`Cslib.Complexity.satExponent`) lies in `[0, 1]`: exhaustive search
decides `k`-SAT within time `2 ^ n` times a polynomial
(`Cslib.Complexity.KSAT_decidableInExpTime_one`). It is monotone in `k`, since a decider for
`k'`-SAT decides `k`-SAT for `k ≤ k'` after checking the widths of the clauses. The set of
exponents is upward closed, so the hypotheses are statements about the exponents
[ImpagliazzoPaturi2001]:

* the exponential time hypothesis says `s_3 > 0` (`Cslib.Complexity.ETH_iff_satExponent_pos`);
* the strong exponential time hypothesis says `s_k → 1` (`Cslib.Complexity.SETH_iff_tendsto`).

## Measuring by clauses

A formula of width three with `m` clauses has at most `3 m` variables
(`Cslib.Logic.PL.CNF.numVars_le_mul_length`), so a decider for 3SAT within time `2 ^ (δ n)` times a
polynomial gives one within time `2 ^ (3 δ m)` times a polynomial
(`Cslib.Complexity.DecidableInSubexpTime.length_of_numVars`). Hence the exponential time hypothesis
holds as soon as 3SAT is not decidable in subexponential time in the number of clauses
(`Cslib.Complexity.ETH_of_not_decidableInSubexpTime_length`). The converse is the content of the
sparsification lemma of Impagliazzo, Paturi and Zane [ImpagliazzoPaturiZane2001], with the
sparsified formulas searched within time `2 ^ (ε n)` times a polynomial; it is proved in
`Cslib.Complexity.ETH_iff_not_decidableInSubexpTime_length`.

## Main results

* `Cslib.Complexity.satExponent_nonneg`, `Cslib.Complexity.satExponent_le_one`,
  `Cslib.Complexity.satExponent_mono`: `0 ≤ s_k ≤ 1`, monotone in `k`.
* `Cslib.Complexity.ETH_iff_satExponent_pos`: `ETH ↔ 0 < s_3`.
* `Cslib.Complexity.SETH_iff_tendsto`: `SETH ↔ s_k → 1`.
* `Cslib.Complexity.ETH_of_not_decidableInSubexpTime_length`: if 3SAT is not decidable in
  subexponential time in the number of clauses, then `ETH`.

## References

* [R. Impagliazzo, R. Paturi, *On the complexity of k-SAT*][ImpagliazzoPaturi2001]
* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM Filter Topology

/-! ### Monotonicity -/

/-- A decider for `k'`-SAT gives a decider for `k`-SAT, for `k ≤ k'`. -/
theorem DecidableInExpTime.KSAT_of_le {k k' : ℕ} (hk : k ≤ k') {δ : ℝ} (hδ : 0 ≤ δ)
    (h : DecidableInExpTime (KSAT k') encCNF CNF.numVars δ) :
    DecidableInExpTime (KSAT k) encCNF CNF.numVars δ := by
  rw [KSAT_eq_inter k (B := KSAT k') (fun φ hφ => ⟨fun c hc => (hφ.1 c hc).trans hk, hφ.2⟩)
    (KSAT_subset_SAT k')]
  exact h.inter (computableTidilyInPolyTime_all_length_le k) hδ

/-- The exponents of `k`-SAT. -/
private abbrev exponents (k : ℕ) : Set ℝ :=
  {δ | 0 ≤ δ ∧ DecidableInExpTime (KSAT k) encCNF CNF.numVars δ}

private theorem one_mem_exponents (k : ℕ) : (1 : ℝ) ∈ exponents k :=
  ⟨zero_le_one, KSAT_decidableInExpTime_one k⟩

private theorem bddBelow_exponents (k : ℕ) : BddBelow (exponents k) :=
  ⟨0, fun _ h => h.1⟩

/-- The exponent of `k`-SAT is nonnegative. -/
theorem satExponent_nonneg (k : ℕ) : 0 ≤ satExponent k :=
  le_csInf ⟨1, one_mem_exponents k⟩ fun _ h => h.1

/-- **Exhaustive search**: the exponent of `k`-SAT is at most one. -/
theorem satExponent_le_one (k : ℕ) : satExponent k ≤ 1 :=
  csInf_le (bddBelow_exponents k) (one_mem_exponents k)

/-- The exponent of `k`-SAT is at most every exponent of a decider. -/
theorem satExponent_le {k : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : DecidableInExpTime (KSAT k) encCNF CNF.numVars δ) : satExponent k ≤ δ :=
  csInf_le (bddBelow_exponents k) ⟨hδ, h⟩

/-- Below the exponent of `k`-SAT there is no decider. -/
theorem not_decidableInExpTime_of_lt_satExponent {k : ℕ} {δ : ℝ} (hδ₀ : 0 ≤ δ)
    (hδ : δ < satExponent k) : ¬DecidableInExpTime (KSAT k) encCNF CNF.numVars δ := fun h =>
  absurd (satExponent_le hδ₀ h) (not_le.mpr hδ)

/-- Without a decider for an exponent `δ`, the exponent of `k`-SAT is at least `δ`. -/
theorem le_satExponent_of_not_decidableInExpTime {k : ℕ} {δ : ℝ}
    (h : ¬DecidableInExpTime (KSAT k) encCNF CNF.numVars δ) : δ ≤ satExponent k :=
  le_csInf ⟨1, one_mem_exponents k⟩ fun _ hδ' => le_of_not_gt fun hlt => h (hδ'.2.mono hlt.le)

/-- The exponent of `k`-SAT is monotone in `k`. -/
theorem satExponent_mono : Monotone satExponent := fun k k' hk =>
  csInf_le_csInf (bddBelow_exponents k) ⟨1, one_mem_exponents k'⟩ fun _ hδ =>
    ⟨hδ.1, hδ.2.KSAT_of_le hk hδ.1⟩

/-! ### The hypotheses in terms of the exponents -/

/-- **The exponential time hypothesis in terms of the exponent**: `ETH ↔ 0 < s_3`
[ImpagliazzoPaturi2001]. -/
theorem ETH_iff_satExponent_pos : ETH ↔ 0 < satExponent 3 := by
  constructor
  · rintro ⟨δ, hδ, h⟩
    exact hδ.trans_le (le_satExponent_of_not_decidableInExpTime h)
  · intro h
    exact ⟨satExponent 3 / 2, half_pos h,
      not_decidableInExpTime_of_lt_satExponent (half_pos h).le (half_lt_self h)⟩

/-- **The strong exponential time hypothesis in terms of the exponents**: `SETH ↔ s_k → 1`
[ImpagliazzoPaturi2001]. -/
theorem SETH_iff_tendsto : SETH ↔ Tendsto satExponent atTop (𝓝 1) := by
  constructor
  · intro h
    rw [Metric.tendsto_atTop]
    intro ε hε
    set η := min ε 1 / 2
    have hη : 0 < η := half_pos (lt_min hε one_pos)
    have hηε : η < ε := (half_lt_self (lt_min hε one_pos)).trans_le (min_le_left ε 1)
    have hη₁ : 0 ≤ 1 - η := by
      have : η ≤ 1 / 2 := div_le_div_of_nonneg_right (min_le_right ε 1) zero_le_two
      linarith
    obtain ⟨k, hk⟩ := h η hη
    refine ⟨k, fun k' hk' => ?_⟩
    have h₁ : 1 - η ≤ satExponent k' :=
      le_satExponent_of_not_decidableInExpTime fun h' => hk (h'.KSAT_of_le hk' hη₁)
    have h₂ := satExponent_le_one k'
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith
  · intro h ε hε
    set η := min ε 1 / 2
    have hη : 0 < η := half_pos (lt_min hε one_pos)
    have hηε : η ≤ ε := (half_lt_self (lt_min hε one_pos)).le.trans (min_le_left ε 1)
    have hη₁ : 0 ≤ 1 - η := by
      have : η ≤ 1 / 2 := div_le_div_of_nonneg_right (min_le_right ε 1) zero_le_two
      linarith
    obtain ⟨k, hk⟩ := (h.eventually (lt_mem_nhds (by linarith : 1 - η < 1))).exists
    exact ⟨k, fun h' => not_decidableInExpTime_of_lt_satExponent hη₁ hk
      (h'.mono (by linarith))⟩

/-! ### Measuring by clauses -/

/-- **From variables to clauses.** If 3SAT is decidable in subexponential time in the number of
variables, it is decidable in subexponential time in the number of clauses, since a formula of
width three with `m` clauses has at most `3 m` variables. -/
theorem DecidableInSubexpTime.length_of_numVars
    (h : DecidableInSubexpTime ThreeSAT encCNF CNF.numVars) :
    DecidableInSubexpTime ThreeSAT encCNF List.length := by
  intro δ hδ
  obtain ⟨e, h⟩ := h (δ / 3) (by positivity)
  obtain ⟨e', h⟩ := h.inter (computableTidilyInPolyTime_all_length_le 3) fun φ => by positivity
  rw [← KSAT_three, ← KSAT_eq_inter 3 le_rfl (KSAT_subset_SAT 3)] at h
  refine ⟨e + e', h.mono 2 (fun φ => ?_) fun φ => by positivity⟩
  have hL : (1 : ℝ) ≤ (encCNF φ).length + 1 := by
    linarith [(Nat.cast_nonneg (encCNF φ).length : (0 : ℝ) ≤ _)]
  have h₁ : (1 : ℝ) ≤ 2 ^ (δ * φ.length) := Real.one_le_rpow (by norm_num) (by positivity)
  have h₂ : (((encCNF φ).length : ℝ) + 1) ^ e ≤ ((encCNF φ).length + 1) ^ (e + e') :=
    pow_le_pow_right₀ hL (Nat.le_add_right e e')
  have h₃ : (((encCNF φ).length : ℝ) + 1) ^ e' ≤ ((encCNF φ).length + 1) ^ (e + e') :=
    pow_le_pow_right₀ hL (Nat.le_add_left e' e)
  have h₅ : (((encCNF φ).length : ℝ) + 1) ^ (e + e') ≤
      2 ^ (δ * φ.length) * ((encCNF φ).length + 1) ^ (e + e') :=
    le_mul_of_one_le_left (by positivity) h₁
  have h₆ : (if (φ.all fun c => decide (c.length ≤ 3)) = true then
      2 ^ (δ / 3 * φ.numVars) * (((encCNF φ).length : ℝ) + 1) ^ e else 0) ≤
      2 ^ (δ * φ.length) * ((encCNF φ).length + 1) ^ (e + e') := by
    split_ifs with hw
    · simp only [List.all_eq_true, decide_eq_true_eq] at hw
      have hn : (φ.numVars : ℝ) ≤ 3 * φ.length := by
        exact_mod_cast CNF.numVars_le_mul_length hw
      have h₇ : (2 : ℝ) ^ (δ / 3 * φ.numVars) ≤ 2 ^ (δ * φ.length) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
      exact mul_le_mul h₇ h₂ (by positivity) (by positivity)
    · positivity
  push_cast
  nlinarith

/-- **The exponential time hypothesis from clauses**: if 3SAT is not decidable in subexponential
time in the number of clauses, then `ETH`. -/
theorem ETH_of_not_decidableInSubexpTime_length
    (h : ¬DecidableInSubexpTime ThreeSAT encCNF List.length) : ETH :=
  ETH_iff_not_decidableInSubexpTime.mpr fun h' => h h'.length_of_numVars

end Cslib.Complexity
