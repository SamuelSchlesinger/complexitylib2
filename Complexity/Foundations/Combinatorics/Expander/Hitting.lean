/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Walk
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.BigOperators.Balance
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# The hitting property of expander walks

A random walk on a good expander is unlikely to stay inside a small set of vertices for long.
The study of this *hitting property* began with [Ajtai, Komlós and
Szemerédi][AjtaiKomlosSzemeredi1987]; the sharp bound is due to [Kahale][Kahale1995], as credited
in [Vadhan, Section 4.6][Vadhan2012]. We follow the operator-decomposition proof of Vadhan
(Theorem 4.17), allowing a different set at each step and retaining the initial density factor.
If the sets `B 0, B 1, …` all have density
at most `μ` and `λ = λ(G)`, a walk of length `t` from a uniformly random vertex has
`vᵢ ∈ B i` for all `i ≤ t` with probability at most `μ (μ + λ (1 - μ)) ^ t`
(`Cslib.RotationMap.dens_filter_forall_walkAt_mem_le`). The `t + 1` vertices of the walk are
sampled from a seed space of cardinality `|V| * |D| ^ t`, against `|V| ^ (t + 1)` for
independent vertices. When `μ < 1` and `λ < 1`, the probability of remaining in the sets
decays exponentially in `t`. This is the probabilistic estimate underlying expander-walk
error reduction for one-sided error; no machine-level error-reduction theorem is asserted here.

The expected product of weights `h i` at the vertices of a walk from `v` is computed by alternating
the walk operator with multiplication by the weights (`Cslib.RotationMap.weightedWalk`,
`Cslib.RotationMap.expect_prod_walkAt`). For indicator weights, each step multiplies the second
moment of a function supported on a set of density at most `μ` by at most
`((1 - λ) μ + λ) ^ 2`: the walk operator is `(1 - λ)` times the projection onto the constants plus
an operator of norm at most `λ`, and the projection of a function supported on a small set is small
(`Cslib.RotationMap.expect_ite_mem_walk_sq_le`).

## Main definitions

* `Cslib.RotationMap.weightedWalk`: the expected product of weights along a random walk.

## Main results

* `Cslib.RotationMap.expect_prod_walkAt`: the expected product of weights along a walk from a
  vertex is the weighted walk.
* `Cslib.RotationMap.expect_ite_mem_walk_sq_le`: one step of a walk restricted to a small set.
* `Cslib.RotationMap.dens_filter_forall_walkAt_mem_le`: the hitting property.
* `Cslib.RotationMap.dens_filter_forall_walkAt_mem_le_pow`: the usual power bound for remaining
  in sets of density at most `μ`.
* `Cslib.RotationMap.dens_filter_forall_walkAt_notMem_le`: a walk misses a set of density `δ`
  with probability at most `(1 - δ) (1 - (1 - λ) δ) ^ t`.

## References

* [M. Ajtai, J. Komlós, E. Szemerédi, *Deterministic simulation in
  LOGSPACE*][AjtaiKomlosSzemeredi1987]
* [N. Kahale, *Eigenvalues and expansion of regular graphs*][Kahale1995]
* [S. P. Vadhan, *Pseudorandomness*][Vadhan2012]
* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset
open scoped BigOperators

variable {V D : Type*} (G : RotationMap V D)

section WeightedWalk

variable [Fintype D]

/-- The *weighted walk* `G.weightedWalk t h`: the function whose value at `v` is the expected
product `∏_{i ≤ t} h i vᵢ` of the weights `h i` at the vertices `v₀ = v, v₁, …, v_t` of a uniformly
random walk of length `t` from `v` (`expect_prod_walkAt`). It multiplies by `h 0` after a step of
the walk operator applied to the weighted walk of the shifted weights. -/
noncomputable def weightedWalk : ℕ → (ℕ → V → ℝ) → V → ℝ
  | 0, h => h 0
  | t + 1, h => h 0 * G.walk (weightedWalk t fun i => h (i + 1))

@[simp]
theorem weightedWalk_zero (h : ℕ → V → ℝ) : G.weightedWalk 0 h = h 0 :=
  rfl

theorem weightedWalk_succ (t : ℕ) (h : ℕ → V → ℝ) :
    G.weightedWalk (t + 1) h = h 0 * G.walk (G.weightedWalk t fun i => h (i + 1)) :=
  rfl

/-- The weighted walk at `v` carries the weight `h 0 v` of its start. -/
theorem weightedWalk_eq_mul (t : ℕ) (h : ℕ → V → ℝ) (v : V) :
    ∃ c, G.weightedWalk t h v = h 0 v * c := by
  cases t with
  | zero => exact ⟨1, (mul_one _).symm⟩
  | succ t => exact ⟨_, rfl⟩

/-- The expected product of the weights `h i` at the vertices of a uniformly random walk of length
`t` from `v` is the weighted walk at `v`. -/
theorem expect_prod_walkAt (t : ℕ) (h : ℕ → V → ℝ) (v : V) :
    𝔼 k : Fin t → D, ∏ i ∈ range (t + 1), h i (G.walkAt (v, k) i) = G.weightedWalk t h v := by
  induction t generalizing h v with
  | zero => simp
  | succ t ih =>
    rw [Fin.expect_univ_cons, weightedWalk_succ, Pi.mul_apply, walk_apply, mul_expect]
    refine expect_congr rfl fun a _ => ?_
    simp only [prod_range_succ' _ (t + 1), walkAt_cons_succ, walkAt_zero,
      ← expect_mul, ih (fun i => h (i + 1))]
    exact mul_comm _ _

/-- The average of the weighted walk is the expected product of the weights along a uniformly
random walk. -/
theorem expect_weightedWalk [Fintype V] (t : ℕ) (h : ℕ → V → ℝ) :
    𝔼 v, G.weightedWalk t h v = 𝔼 p : V × (Fin t → D), ∏ i ∈ range (t + 1), h i (G.walkAt p i) := by
  rw [Fintype.expect_prod_type]
  exact expect_congr rfl fun v _ => (G.expect_prod_walkAt t h v).symm

end WeightedWalk

section Hitting

variable [Fintype V] [Fintype D] [DecidableEq V]

/-- One step of a walk restricted to a small set: if `x` vanishes outside a set `C`, and `B` and `C`
have density at most `μ`, then restricting `G.walk x` to `B` gives second moment at most
`((1 - λ(G)) μ + λ(G)) ^ 2` times that of `x`. -/
theorem expect_ite_mem_walk_sq_le [Nonempty D] {B C : Finset V} {μ : ℝ} (hB : (dens B : ℝ) ≤ μ)
    (hC : (dens C : ℝ) ≤ μ) {x : V → ℝ} (hx : ∀ v ∉ C, x v = 0) :
    𝔼 v, (if v ∈ B then G.walk x v else 0) ^ 2 ≤
      ((1 - G.spectralExpansion) * μ + G.spectralExpansion) ^ 2 * 𝔼 v, x v ^ 2 := by
  rcases isEmpty_or_nonempty V with hV | hV
  · simp [univ_eq_empty]
  set ℓ := G.spectralExpansion
  have hℓ₀ := G.spectralExpansion_nonneg
  have hℓ₁ := G.spectralExpansion_le_one
  have hμ : 0 ≤ μ := (by positivity : (0 : ℝ) ≤ dens B).trans hB
  set α := 𝔼 v, x v
  -- the average of a function supported on `C` is small
  have hα : α ^ 2 ≤ dens C * 𝔼 v, x v ^ 2 := by
    have h := expect_mul_sq_le_sq_mul_sq univ (fun v => if v ∈ C then (1 : ℝ) else 0) x
    have h₁ : 𝔼 v, (if v ∈ C then (1 : ℝ) else 0) * x v = α :=
      expect_congr rfl fun v _ => by by_cases hv : v ∈ C <;> simp [hv, hx]
    have h₂ : 𝔼 v, (if v ∈ C then (1 : ℝ) else 0) ^ 2 = dens C := by
      simpa only [ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0),
        filter_mem_eq_inter, univ_inter] using
        (Fintype.expect_boole (𝕜 := ℝ) fun v => v ∈ C)
    rwa [h₁, h₂] at h
  -- the walk operator is `(1 - λ)` times the average plus an operator of norm at most `λ`
  set y : V → ℝ := fun v => G.walk x v - (1 - ℓ) * α
  have hy : 𝔼 v, y v ^ 2 ≤ ℓ ^ 2 * 𝔼 v, x v ^ 2 := by
    set w : V → ℝ := G.walk (fun v => x v - α)
    have hw₀ : 𝔼 v, (x v - α) = 0 := Fintype.expect_balance x
    have hw : 𝔼 v, w v = 0 := G.expect_walk_eq_zero hw₀
    have hw₂ : 𝔼 v, w v ^ 2 ≤ ℓ ^ 2 * 𝔼 v, (x v - α) ^ 2 :=
      expect_walk_sq_le_spectralExpansion_sq_mul hw₀
    have hyw (v : V) : y v = ℓ * α + w v := by
      have : G.walk x = (fun _ => α) + w := by
        rw [← G.walk_const α, ← map_add]
        congr 1
        funext v
        simp
      simp only [y, this, Pi.add_apply]
      ring
    have hvar : 𝔼 v, (x v - α) ^ 2 = 𝔼 v, x v ^ 2 - α ^ 2 := by
      have : ∀ v, (x v - α) ^ 2 = x v ^ 2 - 2 * α * x v + α ^ 2 := fun v => by ring
      simp only [this, expect_add_distrib, expect_sub_distrib, ← mul_expect,
        Fintype.expect_const]
      ring
    calc 𝔼 v, y v ^ 2 = ℓ ^ 2 * α ^ 2 + 2 * (ℓ * α) * 𝔼 v, w v + 𝔼 v, w v ^ 2 := by
          have : ∀ v, y v ^ 2 = ℓ ^ 2 * α ^ 2 + 2 * (ℓ * α) * w v + w v ^ 2 := fun v => by
            rw [hyw]; ring
          simp only [this, expect_add_distrib, ← mul_expect, Fintype.expect_const]
      _ ≤ ℓ ^ 2 * α ^ 2 + 2 * (ℓ * α) * 0 + ℓ ^ 2 * (𝔼 v, x v ^ 2 - α ^ 2) := by
          rw [hw, ← hvar]
          gcongr
      _ = ℓ ^ 2 * 𝔼 v, x v ^ 2 := by ring
  -- so the restriction to `B` is the restriction of `(1 - λ) α` plus a function of norm `λ ‖x‖`
  have hsplit (v : V) : (if v ∈ B then G.walk x v else 0) =
      (1 - ℓ) * (if v ∈ B then α else 0) + 1 * (if v ∈ B then y v else 0) := by
    split_ifs <;> simp [y]
  simp only [hsplit]
  refine Fintype.expect_add_sq_le (by linarith) zero_le_one hμ hℓ₀
    (expect_nonneg fun _ _ => sq_nonneg _) ?_ ?_ |>.trans_eq (by ring)
  · calc 𝔼 v, (if v ∈ B then α else 0) ^ 2 = dens B * α ^ 2 := by
          have hBavg : (𝔼 v, if v ∈ B then (1 : ℝ) else 0) = dens B := by
            simpa using (Fintype.expect_boole (𝕜 := ℝ) fun v => v ∈ B)
          rw [← hBavg, expect_mul]
          exact expect_congr rfl fun v _ => by split_ifs <;> simp
      _ ≤ μ * (μ * 𝔼 v, x v ^ 2) := by
          have := expect_nonneg (s := (univ : Finset V)) fun v _ => sq_nonneg (x v)
          gcongr
          exact hα.trans (by gcongr)
      _ = μ ^ 2 * 𝔼 v, x v ^ 2 := by ring
  · refine le_trans (expect_le_expect fun v _ => ?_) hy
    split_ifs <;> simp [sq_nonneg]

/-- **The hitting property of expander walks**, following [Vadhan, Theorem 4.17][Vadhan2012]
(the sharp bound is due to [Kahale][Kahale1995]), with varying sets and the initial density
factor retained: if the sets `B i` have density at most
`μ`, a uniformly random walk of length `t` has its `i`-th vertex in `B i` for every `i ≤ t` with
probability at most `μ (μ + λ(G) (1 - μ)) ^ t`. -/
theorem dens_filter_forall_walkAt_mem_le [Nonempty D] {B : ℕ → Finset V} {μ : ℝ}
    (hB : ∀ i, (dens (B i) : ℝ) ≤ μ) (t : ℕ) :
    (dens {p : V × (Fin t → D) | ∀ i ≤ t, G.walkAt p i ∈ B i} : ℝ) ≤
      μ * (μ + G.spectralExpansion * (1 - μ)) ^ t := by
  set ℓ := G.spectralExpansion
  set c := (1 - ℓ) * μ + ℓ
  have hμ : 0 ≤ μ := (by positivity : (0 : ℝ) ≤ dens (B 0)).trans (hB 0)
  have hc : 0 ≤ c := by
    have := G.spectralExpansion_le_one
    have := G.spectralExpansion_nonneg
    positivity
  set h : ℕ → V → ℝ := fun i v => if v ∈ B i then 1 else 0
  -- the weighted walk of the indicators vanishes outside the first set
  have hsupp (t : ℕ) (B : ℕ → Finset V) (v : V) (hv : v ∉ B 0) :
      G.weightedWalk t (fun i v => if v ∈ B i then (1 : ℝ) else 0) v = 0 := by
    obtain ⟨c, hc⟩ := G.weightedWalk_eq_mul t (fun i v => if v ∈ B i then (1 : ℝ) else 0) v
    simp [hc, hv]
  -- and its second moment decays by `c ^ 2` with every step
  have hmoment (t : ℕ) : ∀ B : ℕ → Finset V, (∀ i, (dens (B i) : ℝ) ≤ μ) →
      𝔼 v, G.weightedWalk t (fun i v => if v ∈ B i then (1 : ℝ) else 0) v ^ 2 ≤
        c ^ (2 * t) * μ := by
    induction t with
    | zero =>
      intro B hB
      simp only [weightedWalk_zero, pow_zero, mul_zero, one_mul]
      calc 𝔼 v, (if v ∈ B 0 then (1 : ℝ) else 0) ^ 2 = dens (B 0) := by
            simpa only [ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0),
              filter_mem_eq_inter, univ_inter] using
              (Fintype.expect_boole (𝕜 := ℝ) fun v => v ∈ B 0)
        _ ≤ μ := hB 0
    | succ t ih =>
      intro B hB
      have hstep := G.expect_ite_mem_walk_sq_le (hB 0) (hB 1) (hsupp t (fun i => B (i + 1)))
      have heq (v : V) : G.weightedWalk (t + 1) (fun i v => if v ∈ B i then (1 : ℝ) else 0) v =
          if v ∈ B 0 then G.walk (G.weightedWalk t
            (fun i v => if v ∈ B (i + 1) then (1 : ℝ) else 0)) v else 0 := by
        rw [weightedWalk_succ, Pi.mul_apply]
        split_ifs <;> simp
      simp only [heq]
      calc _ ≤ c ^ 2 * 𝔼 v, G.weightedWalk t
              (fun i v => if v ∈ B (i + 1) then (1 : ℝ) else 0) v ^ 2 := hstep
        _ ≤ c ^ 2 * (c ^ (2 * t) * μ) := by gcongr; exact ih _ fun i => hB (i + 1)
        _ = c ^ (2 * (t + 1)) * μ := by ring
  -- the probability is the average of the weighted walk, which is small by Cauchy–Schwarz
  have hprob : (dens {p : V × (Fin t → D) | ∀ i ≤ t, G.walkAt p i ∈ B i} : ℝ) =
      𝔼 v, G.weightedWalk t h v := by
    rw [expect_weightedWalk, ← Fintype.expect_boole]
    refine expect_congr rfl fun p _ => ?_
    simp only [h, prod_ite_zero, prod_const_one, mem_range, Nat.lt_succ_iff]
  rw [hprob]
  have hCS := expect_mul_sq_le_sq_mul_sq univ (fun v => if v ∈ B 0 then (1 : ℝ) else 0)
    (G.weightedWalk t h)
  have h₁ : 𝔼 v, (if v ∈ B 0 then (1 : ℝ) else 0) * G.weightedWalk t h v =
      𝔼 v, G.weightedWalk t h v :=
    expect_congr rfl fun v _ => by
      by_cases hv : v ∈ B 0
      · simp [hv]
      · simp only [hv, ↓reduceIte, zero_mul]
        exact (hsupp t B v hv).symm
  have h₂ : 𝔼 v, (if v ∈ B 0 then (1 : ℝ) else 0) ^ 2 = dens (B 0) := by
    simpa only [ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0),
      filter_mem_eq_inter, univ_inter] using
      (Fintype.expect_boole (𝕜 := ℝ) fun v => v ∈ B 0)
  rw [h₁, h₂] at hCS
  have hbound : (𝔼 v, G.weightedWalk t h v) ^ 2 ≤ (μ * c ^ t) ^ 2 :=
    hCS.trans <| (mul_le_mul (hB 0) (hmoment t B hB) (expect_nonneg fun _ _ => sq_nonneg _)
      hμ).trans_eq (by ring)
  calc 𝔼 v, G.weightedWalk t h v ≤ μ * c ^ t := (abs_le_of_sq_le_sq' hbound (by positivity)).2
    _ = μ * (μ + ℓ * (1 - μ)) ^ t := by ring

/-- The usual power form of the hitting bound: the probability that every vertex belongs to its
specified set is at most `(μ + λ(G) (1 - μ)) ^ (t + 1)`. -/
theorem dens_filter_forall_walkAt_mem_le_pow [Nonempty D] {B : ℕ → Finset V} {μ : ℝ}
    (hB : ∀ i, (dens (B i) : ℝ) ≤ μ) (hμ : μ ≤ 1) (t : ℕ) :
    (dens {p : V × (Fin t → D) | ∀ i ≤ t, G.walkAt p i ∈ B i} : ℝ) ≤
      (μ + G.spectralExpansion * (1 - μ)) ^ (t + 1) := by
  have hμ₀ : 0 ≤ μ := (by positivity : (0 : ℝ) ≤ dens (B 0)).trans (hB 0)
  have hℓ := G.spectralExpansion_nonneg
  refine (G.dens_filter_forall_walkAt_mem_le hB t).trans ?_
  rw [pow_succ']
  gcongr
  exact le_add_of_nonneg_right (mul_nonneg hℓ (sub_nonneg.mpr hμ))

/-- A uniformly started walk misses a set of density `δ` with probability at most
`(1 - δ) (1 - (1 - λ(G)) δ) ^ t`. -/
theorem dens_filter_forall_walkAt_notMem_le [Nonempty V] [Nonempty D] (A : Finset V) (t : ℕ) :
    (dens {p : V × (Fin t → D) | ∀ i ≤ t, G.walkAt p i ∉ A} : ℝ) ≤
      (1 - (dens A : ℝ)) * (1 - (1 - G.spectralExpansion) * (dens A : ℝ)) ^ t := by
  have hsum : (dens Aᶜ : ℝ) + dens A = 1 := by
    exact_mod_cast (show dens Aᶜ + dens A = 1 by
      simpa only [compl_eq_univ_sdiff, dens_univ] using
        dens_sdiff_add_dens_eq_dens (subset_univ A))
  have hcompl : (dens Aᶜ : ℝ) = 1 - dens A := by linarith
  have h := G.dens_filter_forall_walkAt_mem_le (B := fun _ => Aᶜ)
    (μ := 1 - dens A) (fun _ => hcompl.le) t
  simpa only [mem_compl, show 1 - (dens A : ℝ) + G.spectralExpansion *
    (1 - (1 - dens A)) = 1 - (1 - G.spectralExpansion) * dens A by ring] using h

end Hitting

end Cslib.RotationMap
