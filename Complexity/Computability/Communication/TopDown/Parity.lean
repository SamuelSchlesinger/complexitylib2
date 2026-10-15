/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.TopDown.Adversary
public import Complexity.Computability.Communication.TopDown.Arithmetic
public import Complexity.Foundations.Data.BitString.Parity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Parity initialization and the top-down communication bound

Flipping one free coordinate pairs the two parity classes in every nonempty
fiber, giving density exactly `1/2`. A rate-`4/n` mask is nonempty with
probability at least `3/4`. Both parity classes therefore satisfy the initial
limit condition, with deficit one. Apply the bilateral density adversary and
its checked parameter bound to obtain the communication part of Theorem 3.

Source: [Korten2026]. -/

public section

namespace Cslib.BooleanAnalysis
open Finset
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem expect_half_of_flip (f : (ι → Bool) → Bool) (i : ι)
    (hf : ∀ x, f (Function.update x i (!x i)) = !f x) (b : Bool) :
    (𝔼 x, if f x = b then (1 : ℝ) else 0) = 1 / 2 := by
  let flip (x : ι → Bool) := Function.update x i (!x i)
  have hinv : Function.Involutive flip := by
    intro x
    funext j
    by_cases hj : j = i
    · subst hj
      simp [flip]
    · simp [flip, Function.update_of_ne hj]
  let e := hinv.toPerm flip
  have he := Fintype.expect_equiv e
    (fun x => if f (flip x) = b then (1 : ℝ) else 0)
    (fun x => if f x = b then (1 : ℝ) else 0) (fun _ => rfl)
  have hpoint (x : ι → Bool) : (if f (flip x) = b then (1 : ℝ) else 0) =
      1 - (if f x = b then 1 else 0) := by
    rw [hf]
    cases h : f x <;> cases b <;> norm_num
  simp_rw [hpoint, expect_sub_distrib, Fintype.expect_const] at he
  linarith

theorem coordinateDensity_half_of_flip (f : (ι → Bool) → Bool)
    (hf : ∀ x i, f (Function.update x i (!x i)) = !f x)
    (P x : ι → Bool) (b : Bool) (i : ι) (hi : P i = true) :
    coordinateDensity (univ.filter fun z => f z = b) P x = 1 / 2 := by
  have hflip (y : ι → Bool) : resample P x (Function.update y i (!y i)) =
      Function.update (resample P x y) i (!(resample P x y i)) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [resample, hi]
    · simp [resample, Function.update_of_ne hj]
  rw [coordinateDensity_eq_expect]
  simp only [mem_filter, mem_univ, true_and]
  exact expect_half_of_flip (fun y => f (resample P x y)) i
    (fun y => by rw [hflip, hf]) b



theorem parity_initial {n : ℕ} (hn : 0 < n) (b : Bool) :
    (univ.filter fun x : Fin n → Bool => parity n x = b).Nonempty ∧
      uniformDeficit (univ.filter fun x : Fin n → Bool => parity n x = b) ≤ 1 := by
  let X := univ.filter (fun x : Fin n → Bool => parity n x = b)
  have hbal := expect_half_of_flip (parity n) ⟨0, hn⟩
    (fun x => parity_update_not x _) b
  have hratio : (X.card : ℝ) / (2 : ℝ) ^ n = 1 / 2 := by
    simpa only [Fintype.expect_eq_sum_div_card, sum_boole, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using hbal
  have hcard : (X.card : ℝ) = (2 : ℝ) ^ n / 2 := by
    have he := (div_eq_iff (show (2 : ℝ) ^ n ≠ 0 by positivity)).mp hratio
    linarith
  have hX : X.Nonempty := by
    apply card_pos.mp
    have he : (0 : ℝ) < X.card := by rw [hcard]; positivity
    exact_mod_cast he
  refine ⟨hX, (uniformDeficit_le_iff hX).mpr ?_⟩
  simp only [Fintype.card_fin]
  rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_one, ← hcard]

theorem parity_isDensityLimit {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hsmall : (1 - p) ^ n ≤ 1 / 4) (b : Bool) (x : Fin n → Bool) :
    IsDensityLimit (univ.filter fun z : Fin n → Bool => parity n z = b) p 1 x := by
  have hpoint (P : Fin n → Bool) : (if ∃ i, P i = true then (1 : ℝ) else 0) ≤
      if (2 : ℝ) ^ (-(1 : ℝ)) ≤ coordinateDensity
        (univ.filter fun z : Fin n → Bool => parity n z = b) P x then 1 else 0 := by
    by_cases h : ∃ i, P i = true
    · obtain ⟨i, hi⟩ := h
      have hd := coordinateDensity_half_of_flip (parity n)
        (fun x i => parity_update_not x i) P x b i hi
      simp only [hd]
      norm_num [show ∃ j, P j = true from ⟨i, hi⟩]
    · rw [ite_eq_right h]
      split_ifs <;> norm_num
  have hh := bernoulliAverage_mono hp hp' hpoint
  have he : bernoulliAverage p
      (fun P : Fin n → Bool => if ∃ i, P i = true then (1 : ℝ) else 0) =
        1 - (1 - p) ^ n := by
    convert bernoulliAverage_nonempty (ι := Fin n) p using 1
    · congr 1
      funext P
      split_ifs <;> rfl
    · simp
  rw [he] at hh
  have hg := (show (3 : ℝ) / 4 ≤ 1 - (1 - p) ^ n by linarith).trans hh
  unfold IsDensityLimit
  convert hg using 1

theorem parity_isDensityLimit_four_div {n : ℕ} (hn : 4 ≤ n) (b : Bool) (x : Fin n → Bool) :
    IsDensityLimit (univ.filter fun z : Fin n → Bool => parity n z = b)
      (4 / n) 1 x := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hp1 : (4 : ℝ) / n ≤ 1 := (div_le_one hnpos).mpr hn4
  apply parity_isDensityLimit (by positivity) hp1 _ b x
  have ht := one_sub_pow_mul_one_add_mul_le_one hp1 n
  have hnp : (n : ℝ) * (4 / n) = 4 := by field_simp
  rw [hnp] at ht
  nlinarith

end Cslib.BooleanAnalysis

namespace Cslib.Communication.RoundProtocol
open Cslib.BooleanAnalysis Finset

variable {M : Type*} [Fintype M]

theorem not_solves_parity_finite_raw {n d : ℕ} (P : RoundProtocol (Fin n) M (d + 1))
    {m : ℝ} (hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m) (hm : 0 ≤ m)
    (hsize : 16 * (32768 * (194 : ℝ) ^ d * (m + 1)) ^ d ≤ (n : ℝ)) :
    ¬ P.Solves (univ.filter fun x => parity n x = false)
      (univ.filter fun y => parity n y = true) := by
  have hC : 1 ≤ 32768 * (194 : ℝ) ^ d * (m + 1) := by
    have hh : 1 ≤ (194 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    nlinarith [mul_nonneg (show 0 ≤ (194 : ℝ) ^ d by positivity) hm]
  have hn16 : (16 : ℝ) ≤ n := by nlinarith [one_le_pow₀ (n := d) hC]
  have hn4 : 4 ≤ n := by exact_mod_cast (show (4 : ℝ) ≤ n by linarith)
  have hnpos : (0 : ℝ) < n := by linarith
  have hX := parity_initial (show 0 < n by omega) false
  have hY := parity_initial (show 0 < n by omega) true
  apply P.not_solves_bilateral_density hM hm (show (0 : ℝ) < 4 / n by positivity)
    hX.1 hY.1 hX.2 hY.2
    (fun x _ => parity_isDensityLimit_four_div hn4 true x)
    (fun y _ => parity_isDensityLimit_four_div hn4 false y)
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hnpos).mpr
  nlinarith

theorem not_solves_parity_finite {n d : ℕ} (P : RoundProtocol (Fin n) M (d + 1))
    {m : ℝ} (hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m) (hm : 0 ≤ m)
    (hsize : 16 * (32768 * (194 : ℝ) ^ d * (m + 1)) ^ d ≤ (n : ℝ)) :
    ¬ P.SolvesKW (parity n) := by
  intro hsol
  apply not_solves_parity_finite_raw P hM hm hsize
  intro x hx y hy
  exact hsol x y (mem_filter.mp hx).2 (mem_filter.mp hy).2

end Cslib.Communication.RoundProtocol


universe u
namespace Cslib.Communication

theorem parity_communication_lower_bound (rounds : ℕ) (hrounds : 2 ≤ rounds) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ {M : Type u} [Fintype M] (m : ℝ), 0 ≤ m →
        (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m →
        m ≤ ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹) →
        ∀ P : RoundProtocol (Fin n) M rounds, ¬ P.SolvesKW (parity n) := by
  classical
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show rounds ≠ 0 by omega)
  have hd : 0 < d := by omega
  let ε : ℝ := 1 / (32 * (32768 * (194 : ℝ) ^ d))
  refine ⟨ε, by dsimp [ε]; positivity, (32 * (32768 * 194 ^ d)) ^ d, ?_⟩
  intro n hn M _ m hm hM hcost P
  have hc : m ≤ (n : ℝ) ^ ((d : ℝ)⁻¹) / (32 * (32768 * (194 : ℝ) ^ d)) := by
    simpa only [ε, Nat.succ_sub_one, one_div, div_eq_mul_inv, mul_comm, one_mul] using hcost
  exact P.not_solves_parity_finite hM hm (finite_budget_of_cost hd hn hm hc)

end Cslib.Communication
