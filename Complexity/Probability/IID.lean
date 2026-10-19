/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Product
import Complexity.Probability.PMF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Independent draws from a distribution

`Cslib.Probability.PMF.iid μ k` draws `k` independent samples from `μ`, one coordinate at a time.
Unlike the product `Cslib.Probability.PMF.pi`, it needs no finiteness of the sample space, so it
applies to distributions on infinite types such as the public-coin protocols of communication
complexity. Applying a function to each sample gives independent samples of the image
(`iid_map`), and on finite types the draws form the product distribution (`iid_eq_pi`).

The *majority tail bound* (`toOuterMeasure_iid_le_card_filter_toReal_le`): among `2 r` independent
bits, each `true` with probability `q ≤ ε ≤ 1 / 2`, at least `r` are `true` with probability at
most `(4 ε (1 - ε)) ^ r`. Each outcome with `t ≥ r` true bits has probability
`q ^ t (1 - q) ^ (2 r - t) ≤ (q (1 - q)) ^ r`, and there are at most `4 ^ r` outcomes.

## Main definitions

* `Cslib.Probability.PMF.iid`: independent draws from a distribution.

## Main results

* `Cslib.Probability.PMF.iid_map`, `Cslib.Probability.PMF.iid_eq_pi`: images and finite products.
* `Cslib.Probability.PMF.toOuterMeasure_iid_le_card_filter_toReal_le`: the majority tail bound.

## References

* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Probability.PMF

variable {α β : Type*}

/-- `k` independent draws from `μ`, as a tuple: draw the first coordinate, then the others. -/
noncomputable def iid (μ : PMF α) : (k : ℕ) → PMF (Fin k → α)
  | 0 => PMF.pure Fin.elim0
  | k + 1 => μ.bind fun a => (iid μ k).map (Fin.cons a)

/-- Every coordinate of a possible tuple of independent draws is a possible draw. -/
theorem mem_support_iid {μ : PMF α} :
    ∀ {k : ℕ} {v : Fin k → α}, v ∈ (iid μ k).support → ∀ i, v i ∈ μ.support
  | 0, _, _, i => i.elim0
  | k + 1, v, hv, i => by
    rw [iid, PMF.mem_support_bind_iff] at hv
    obtain ⟨a, ha, hv⟩ := hv
    obtain ⟨w, hw, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hv
    induction i using Fin.cases with
    | zero => simpa using ha
    | succ i => simpa using mem_support_iid hw i

/-- Applying a function to each of independent draws gives independent draws of the image. -/
theorem iid_map (μ : PMF α) (g : α → β) :
    ∀ k, (iid μ k).map (fun v i => g (v i)) = iid (μ.map g) k
  | 0 => by
    rw [iid, iid, PMF.pure_map]
    congr 1
    funext i
    exact i.elim0
  | k + 1 => by
    rw [iid, iid, PMF.map_bind, PMF.bind_map]
    congr 1
    funext a
    rw [Function.comp_apply, ← iid_map μ g k, PMF.map_comp, PMF.map_comp]
    congr 1
    funext v i
    induction i using Fin.cases <;> rfl

/-- On a finite type, independent draws form the product distribution `pi`. -/
theorem iid_eq_pi [Finite α] (μ : PMF α) : ∀ k, iid μ k = pi (fun _ : Fin k => μ)
  | 0 => by
    ext v
    obtain rfl : v = Fin.elim0 := funext fun i => i.elim0
    simp [iid, PMF.pure_apply]
  | k + 1 => by rw [pi_fin_succ, iid, iid_eq_pi μ k]

/-- If `0 ≤ a ≤ b`, `r ≤ t` and `t + u = 2 r`, then `a ^ t b ^ u ≤ (a b) ^ r`. -/
private theorem pow_mul_pow_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {r t u : ℕ} (ht : r ≤ t)
    (htu : t + u = 2 * r) : a ^ t * b ^ u ≤ (a * b) ^ r := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  obtain rfl : r = u + d := by omega
  have hb : 0 ≤ b := ha.trans hab
  calc a ^ (u + d + d) * b ^ u = a ^ u * a ^ d * b ^ u * a ^ d := by ring
    _ ≤ a ^ u * a ^ d * b ^ u * b ^ d :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab d)
          (mul_nonneg (mul_nonneg (pow_nonneg ha _) (pow_nonneg ha _)) (pow_nonneg hb _))
    _ = (a * b) ^ (u + d) := by ring

/-- **The majority tail bound**: among `2 r` independent bits that are each `true` with
probability at most `ε ≤ 1 / 2`, at least `r` are `true` with probability at most
`(4 ε (1 - ε)) ^ r`. -/
theorem toOuterMeasure_iid_le_card_filter_toReal_le {q : PMF Bool} {ε : ℝ}
    (hq : (q true).toReal ≤ ε) (hε : ε ≤ 1 / 2) (r : ℕ) :
    ((iid q (2 * r)).toOuterMeasure {v | r ≤ (Finset.univ.filter fun i => v i = true).card}).toReal
      ≤ (4 * ε * (1 - ε)) ^ r := by
  classical
  set a := (q true).toReal
  set b := (q false).toReal
  have hab : a + b = 1 := by
    have := sum_toReal q
    rwa [Fintype.sum_bool] at this
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hab' : a ≤ b := by linarith
  -- Each outcome with at least `r` true bits has probability at most `(a b) ^ r`.
  have hterm (v : Fin (2 * r) → Bool) (hv : r ≤ (Finset.univ.filter fun i => v i = true).card) :
      ∏ i, (q (v i)).toReal ≤ (a * b) ^ r := by
    have hprod : ∏ i, (q (v i)).toReal = ∏ i, (if v i = true then a else b) :=
      Finset.prod_congr rfl fun i _ => by cases v i <;> rfl
    have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ) fun i => v i = true
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    rw [hprod, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    exact pow_mul_pow_le ha hab' hv hcard
  rw [iid_eq_pi, toOuterMeasure_apply_toReal]
  calc _ ≤ ∑ _v : Fin (2 * r) → Bool, (a * b) ^ r := by
        refine Finset.sum_le_sum fun v _ => ?_
        split_ifs with hv
        · rw [pi_apply, ENNReal.toReal_prod]
          exact hterm v hv
        · positivity
    _ = (4 * (a * b)) ^ r := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul, mul_pow, pow_mul]
        norm_num [mul_pow]
    _ ≤ (4 * ε * (1 - ε)) ^ r := by
        refine pow_le_pow_left₀ (by positivity) ?_ r
        have hb : b = 1 - a := by linarith
        rw [hb]
        nlinarith

end Cslib.Probability.PMF
