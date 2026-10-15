/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Finite covers from uniform local density

If a uniformly chosen test misses each of the obligations `w : W` with probability at most `p / q`,
then `t` tests hit every obligation as soon as `|W| p ^ t < q ^ t`
(`exists_cover_of_scaled_card_lt`): the bad sequences of tests are counted, with a union bound
over the obligations. In particular, if every obligation is hit by at least a `1 / q` fraction of
the tests, then `q (n + 1)` tests hit `2 ^ n` obligations (`exists_cover_of_density`).

## Main results

* `Cslib.exists_cover_of_scaled_card_lt`: the union bound for covers.
* `Cslib.exists_cover_of_density`: covers from density.
-/

@[expose] public section

namespace Cslib

open Finset

/-- **The union bound for covers**, with integer cardinalities: if a uniform test misses each
obligation with probability at most `p / q`, and `|W| p ^ t < q ^ t`, then some `t` tests hit
every obligation. -/
theorem exists_cover_of_scaled_card_lt
    {S W : Type*} [Fintype S] [Nonempty S] [Fintype W]
    (hit : S → W → Prop) [DecidableRel hit] (p q t : Nat)
    (localBound : ∀ w,
      q * Fintype.card {s : S // ¬ hit s w} ≤ p * Fintype.card S)
    (small : Fintype.card W * p ^ t < q ^ t) :
    ∃ tests : Fin t → S, ∀ w, ∃ i, hit (tests i) w := by
  classical
  let bad (w : W) : Finset (Fin t → S) :=
    univ.filter fun tests => ∀ i, ¬ hit (tests i) w
  have badCard (w : W) :
      (bad w).card = (Fintype.card {s : S // ¬ hit s w}) ^ t := by
    calc
      (bad w).card =
          Fintype.card {tests : Fin t → S // ∀ i, ¬ hit (tests i) w} := by
            simp [bad, Fintype.card_subtype]
      _ = Fintype.card (Fin t → {s : S // ¬ hit s w}) :=
        Fintype.card_congr (Equiv.subtypePiEquivPi
          (p := fun (_ : Fin t) (s : S) => ¬ hit s w))
      _ = _ := by simp
  have localPower (w : W) :
      q ^ t * (bad w).card ≤ p ^ t * (Fintype.card S) ^ t := by
    rw [badCard, ← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left (localBound w) t
  let failures := univ.biUnion bad
  have unionBound : q ^ t * failures.card ≤
      Fintype.card W * p ^ t * (Fintype.card S) ^ t := by
    calc
      q ^ t * failures.card ≤ q ^ t * ∑ w, (bad w).card :=
        Nat.mul_le_mul_left _ card_biUnion_le
      _ = ∑ w, q ^ t * (bad w).card := mul_sum ..
      _ ≤ ∑ _w : W, p ^ t * (Fintype.card S) ^ t :=
        sum_le_sum fun w _ => localPower w
      _ = _ := by simp [Nat.mul_assoc]
  have strict : q ^ t * failures.card <
      q ^ t * Fintype.card (Fin t → S) := by
    apply lt_of_le_of_lt unionBound
    simpa [Fintype.card_fun] using
      Nat.mul_lt_mul_of_pos_right small
        (Nat.pow_pos (Fintype.card_pos))
  have smaller : failures.card < Fintype.card (Fin t → S) := by
    exact Nat.lt_of_mul_lt_mul_left strict
  obtain ⟨tests, _, absent⟩ := exists_mem_notMem_of_card_lt_card
    (show failures.card < (univ : Finset (Fin t → S)).card by simpa using smaller)
  refine ⟨tests, fun w => ?_⟩
  by_contra none
  apply absent
  simp only [failures, mem_biUnion, mem_univ, true_and]
  exact ⟨w, by simpa [bad] using none⟩

private theorem failure_power_le_half (q : ℕ) (hq : 0 < q) :
    2 * (q - 1) ^ q ≤ q ^ q := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have h := Real.one_sub_div_pow_le_exp_neg (n := q) (t := 1)
    (by exact_mod_cast hq)
  have he : Real.exp (-1 : ℝ) ≤ (2 : ℝ)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by norm_num) Real.exp_one_gt_two.le
  have hr : (1 - 1 / (q : ℝ)) = (q - 1 : ℕ) / (q : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    field_simp
  rw [hr, div_pow] at h
  have hh := (div_le_iff₀ (pow_pos hqr q)).mp (h.trans he)
  have : (2 : ℝ) * (q - 1 : ℕ) ^ q ≤ (q : ℝ) ^ q := by linarith
  exact_mod_cast this

private theorem cover_power_lt (q n : ℕ) (hq : 0 < q) :
    2 ^ n * (q - 1) ^ (q * (n + 1)) < q ^ (q * (n + 1)) := by
  have h := Nat.pow_le_pow_left (failure_power_le_half q hq) (n + 1)
  rw [mul_pow, ← pow_mul, ← pow_mul, pow_succ] at h
  have hp := Nat.pow_pos (n := q * (n + 1)) hq
  nlinarith

/-- **Covers from density**: if every obligation `w` is hit by at least a `1 / q` fraction of the
tests, then `q (n + 1)` tests, with repetitions, hit all of at most `2 ^ n` obligations. -/
theorem exists_cover_of_density {S W : Type*} [Fintype S] [Nonempty S] [Fintype W]
    (hit : S → W → Prop) [DecidableRel hit] (q n : ℕ) (hq : 0 < q)
    (hw : Fintype.card W ≤ 2 ^ n)
    (density : ∀ w, Fintype.card S ≤ q * Fintype.card {s : S // hit s w}) :
    ∃ tests : Fin (q * (n + 1)) → S, ∀ w, ∃ i, hit (tests i) w := by
  classical
  apply exists_cover_of_scaled_card_lt
    hit (q - 1) q (q * (n + 1))
  · intro w
    rw [Fintype.card_subtype_compl]
    have hc : Fintype.card {s : S // hit s w} ≤ Fintype.card S :=
      Fintype.card_subtype_le _
    have hd := density w
    have hsub := Nat.sub_add_cancel hc
    have hqsub : q - 1 + 1 = q := by omega
    nlinarith
  · exact (Nat.mul_le_mul_right _ hw).trans_lt (cover_power_lt q n hq)

end Cslib
