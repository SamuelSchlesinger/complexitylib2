/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.DiscreteLog
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Crypto.Negligible.Basic
import Complexity.Foundations.Data.Nat.Bits
import Complexity.Probability.PMF
import Complexity.Tactic.PPT
import Mathlib.FieldTheory.Finite.Basic

/-!
# The Computational and Decisional Diffie–Hellman assumptions

Over a `PrimeOrderGroupFamily`, the Computational Diffie–Hellman (CDH) experiment
([BonehShoup2023], Attack Game 10.5) draws a group description `d` from a setup law and two
independent uniform exponents `α, β : ZMod (F.order d)`, gives the adversary `(d, encode (α • g),
encode (β • g))`, and accepts when the adversary outputs `encode ((α * β) • g)`.

The Decisional Diffie–Hellman (DDH) experiment ([BonehShoup2023], Attack Game 10.6) compares the
real tuple `(d, encode (α • g), encode (β • g), encode ((α * β) • g))` against the ideal tuple
`(d, encode (α • g), encode (β • g), encode (γ • g))` with an independent uniform `γ`.

We prove the hierarchy of reductions `DiscreteLog ≤ CDH ≤ DDH` and the worst-case-to-average-case
random self-reducibility of DDH (`ddhRerandomizeLaw_real` and `ddhRerandomizeLaw_ideal`), which
maps any fixed real DDH tuple to the uniform real DDH distribution and any fixed non-DDH tuple to
the uniform ideal DDH distribution.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.cdhGame`, `Cslib.Crypto.PrimeOrderGroupFamily.CDH`:
  the Computational Diffie–Hellman experiment and assumption.
* `Cslib.Crypto.PrimeOrderGroupFamily.dlToCDHAdversary`: the reduction from discrete logarithm to
  CDH.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhRealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhIdealGame`, `Cslib.Crypto.PrimeOrderGroupFamily.DDH`:
  the real and ideal Decisional Diffie–Hellman experiments and assumption.
* `Cslib.Crypto.PrimeOrderGroupFamily.cdhToDDHDistinguisher`: the reduction from CDH to DDH.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhRerandomize`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhRerandomizeLaw`: random self-reduction for DDH tuples.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_discreteLogGame_le_cdhGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.CDH.discreteLog`: `CDH` implies `DiscreteLog`.
* `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_cdhGame_le_advantage_ddh_add`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.cdh`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.discreteLog`: `DDH` implies `CDH` and `DiscreteLog`
  when `1 / q` is negligible.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhRerandomizeLaw_real`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhRerandomizeLaw_ideal`: random self-reducibility of DDH.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 10.4–10.6.
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

/-! ### Computational Diffie–Hellman (CDH) -/

/-- The Computational Diffie–Hellman experiment ([BonehShoup2023], Attack Game 10.5): draw a
description `d` and independent uniform `α, β : ZMod (F.order d)`, give the adversary the
description and the encodings of `α • g` and `β • g`, and accept when it outputs the encoding of
`(α * β) • g`. -/
noncomputable def cdhGame (setup : ℕ → PMF F.Desc)
    (adversary : ℕ → F.Desc × List Bool × List Bool → ProbComp (List Bool)) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let guess ← ProbComp.eval (adversary n
    (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d)))
  return decide (guess = F.encode d ((α * β) • F.generator d))

/-- The Computational Diffie–Hellman assumption for a family and a setup law: every uniform strict
PPT adversary computes `encode ((α * β) • g)` from `(d, encode (α • g), encode (β • g))` with
negligible probability. -/
def CDH (setup : ℕ → PMF F.Desc) : Prop :=
  ∀ adversary : ℕ → F.Desc × List Bool × List Bool → ProbComp (List Bool),
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits encBits))) encBits
      (fun input => adversary input.1 input.2) →
    Negligible fun n => Game.succProbability (F.cdhGame setup adversary n)

/-- Turn a discrete-logarithm adversary into a CDH adversary by running it on `(d, encode (α • g))`
to obtain a candidate exponent `a` and multiplying `encode (β • g)` by `a`. -/
def dlToCDHAdversary (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool))
    (n : ℕ) (input : F.Desc × List Bool × List Bool) : ProbComp (List Bool) := do
  let guess ← adversary n (input.1, input.2.1)
  return F.smul (input.1, ofBits guess, input.2.2)

/-- Whenever the discrete-logarithm adversary recovers `α`, `dlToCDHAdversary` outputs the valid
Diffie–Hellman shared element `encode ((α * β) • g)`. -/
theorem succProbability_discreteLogGame_le_cdhGame (setup : ℕ → PMF F.Desc)
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) (n : ℕ) :
    Game.succProbability (F.discreteLogGame setup adversary n) ≤
      Game.succProbability (F.cdhGame setup (F.dlToCDHAdversary adversary) n) := by
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  simp only [discreteLogGame, cdhGame, dlToCDHAdversary, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  rw [PMF.bind_apply, PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun d => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [PMF.bind_apply, PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun α => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [← PMF.bind_const (PMF.uniformOfFintype (ZMod (F.order d)))
    ((ProbComp.eval (adversary n (d, F.encode d (α • F.generator d)))).bind _)]
  rw [PMF.bind_apply, PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun β => mul_le_mul_of_nonneg_left ?_ zero_le
  refine ENNReal.tsum_le_tsum fun guess => mul_le_mul_of_nonneg_left ?_ zero_le
  by_cases hα : (ofBits guess : ZMod (F.order d)) = α
  · simp only [hα, F.smul_encode, smul_smul, decide_true, le_rfl]
  · simp only [hα, decide_false, PMF.pure_apply, Bool.true_eq_false, ↓reduceIte, zero_le]

/-- The discrete-logarithm-to-CDH reduction is uniform strict PPT when the discrete-logarithm
adversary is. -/
theorem isPPTOn_dlToCDHAdversary
    {adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)}
    (hA : IsPPTOn (encPair encUnary (encPair F.encDesc encBits)) encBits
      (fun input => adversary input.1 input.2)) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits encBits))) encBits
      (fun input => F.dlToCDHAdversary adversary input.1 input.2) := by
  have hsmul := F.computableInPolyTime_smul.tidy
  unfold dlToCDHAdversary
  refine (hA.preprocess
    (prepare := fun input : ℕ × F.Desc × List Bool × List Bool =>
      (input.1, (input.2.1, input.2.2.1))) (by fun_prop)).bind_with ?_
  exact ComputableTidilyInPolyTime.isPPTOn (by fun_prop)

/-- **CDH implies the discrete-logarithm assumption**. -/
theorem CDH.discreteLog {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc} (h : F.CDH setup) :
    F.DiscreteLog setup :=
  fun adversary hA => negligible_of_le (h _ (F.isPPTOn_dlToCDHAdversary hA))
    (F.succProbability_discreteLogGame_le_cdhGame setup adversary)

/-! ### Decisional Diffie–Hellman (DDH) -/

/-- The real Decisional Diffie–Hellman experiment ([BonehShoup2023], Attack Game 10.6): draw `d`
and independent uniform `α, β : ZMod (F.order d)`, and give the distinguisher
`(d, encode (α • g), encode (β • g), encode ((α * β) • g))`. -/
noncomputable def ddhRealGame (setup : ℕ → PMF F.Desc)
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool)
    (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  ProbComp.eval (distinguisher n
    (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d),
      F.encode d ((α * β) • F.generator d)))

/-- The ideal Decisional Diffie–Hellman experiment ([BonehShoup2023], Attack Game 10.6): draw `d`
and independent uniform `α, β, γ : ZMod (F.order d)`, and give the distinguisher
`(d, encode (α • g), encode (β • g), encode (γ • g))`. -/
noncomputable def ddhIdealGame (setup : ℕ → PMF F.Desc)
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool)
    (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let γ ← PMF.uniformOfFintype (ZMod (F.order d))
  ProbComp.eval (distinguisher n
    (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d),
      F.encode d (γ • F.generator d)))

/-- The Decisional Diffie–Hellman assumption for a family and a setup law: every uniform strict PPT
distinguisher has negligible advantage between `ddhRealGame` and `ddhIdealGame`. -/
def DDH (setup : ℕ → PMF F.Desc) : Prop :=
  Game.Indistinguishable (F.ddhRealGame setup) (F.ddhIdealGame setup)
    fun distinguisher =>
      IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
        encBool (fun input => distinguisher input.1 input.2)

/-- Turn a CDH adversary into a DDH distinguisher by testing whether its candidate shared element
equals the challenge third element. -/
def cdhToDDHDistinguisher
    (adversary : ℕ → F.Desc × List Bool × List Bool → ProbComp (List Bool))
    (n : ℕ) (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool := do
  let guess ← adversary n (input.1, input.2.1, input.2.2.1)
  return decide (guess = input.2.2.2)

/-- In the real DDH game, `cdhToDDHDistinguisher` simulates the CDH game exactly. -/
@[simp] theorem ddhRealGame_cdhToDDHDistinguisher (setup : ℕ → PMF F.Desc)
    (adversary : ℕ → F.Desc × List Bool × List Bool → ProbComp (List Bool)) (n : ℕ) :
    F.ddhRealGame setup (F.cdhToDDHDistinguisher adversary) n = F.cdhGame setup adversary n := by
  simp only [ddhRealGame, cdhToDDHDistinguisher, cdhGame, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]

/-- A fixed candidate word matches a uniformly chosen encoded group element with probability at
most `(F.order d)⁻¹`. -/
private theorem uniform_decide_eq_encode_le (d : F.Desc) (guess : List Bool) :
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind
      (fun γ => PMF.pure (decide (guess = F.encode d (γ • F.generator d))))) true ≤
      (F.order d : ℝ≥0∞)⁻¹ := by
  rw [PMF.bind_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, ZMod.card, PMF.pure_apply, eq_comm (a := true),
    decide_eq_true_eq]
  have hcard :
      (Finset.univ.filter
        (fun γ : ZMod (F.order d) => guess = F.encode d (γ • F.generator d))).card ≤ 1 := by
    refine Finset.card_le_one_iff.mpr fun {γ₁ γ₂} h₁ h₂ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    exact F.smul_generator_injective d (F.encode_injective d (h₁.symm.trans h₂))
  calc ∑ x : ZMod (F.order d),
        (F.order d : ℝ≥0∞)⁻¹ *
          (if guess = F.encode d (x • F.generator d) then 1 else 0)
      = ((Finset.univ.filter
          (fun γ : ZMod (F.order d) =>
            guess = F.encode d (γ • F.generator d))).card : ℝ≥0∞) *
          (F.order d : ℝ≥0∞)⁻¹ := by
        rw [← Finset.mul_sum, Finset.sum_boole, mul_comm]
    _ ≤ 1 * (F.order d : ℝ≥0∞)⁻¹ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) zero_le
    _ = (F.order d : ℝ≥0∞)⁻¹ := one_mul _

/-- In the ideal DDH game, `cdhToDDHDistinguisher` succeeds with probability at most `1 / m`
whenever every supported group order is at least `m`. -/
theorem ddhIdealGame_cdhToDDHDistinguisher_true_le (setup : ℕ → PMF F.Desc)
    (adversary : ℕ → F.Desc × List Bool × List Bool → ProbComp (List Bool)) (n m : ℕ)
    (hm : ∀ d ∈ (setup n).support, m ≤ F.order d) :
    (F.ddhIdealGame setup (F.cdhToDDHDistinguisher adversary) n) true ≤ (m : ℝ≥0∞)⁻¹ := by
  simp only [ddhIdealGame, cdhToDDHDistinguisher, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.monad_bind_eq_bind, PMF.bind_apply]
  calc ∑' d, setup n d * ∑' α, PMF.uniformOfFintype (ZMod (F.order d)) α *
        ∑' β, PMF.uniformOfFintype (ZMod (F.order d)) β *
          ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
            (ProbComp.eval (adversary n
              (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d)))).bind
              fun guess =>
                PMF.pure (decide (guess = F.encode d (γ • F.generator d)))) true
      ≤ ∑' d, setup n d * (m : ℝ≥0∞)⁻¹ := by
        refine ENNReal.tsum_le_tsum fun d => ?_
        by_cases hd : d ∈ (setup n).support
        · refine mul_le_mul_of_nonneg_left ?_ zero_le
          have hord : (F.order d : ℝ≥0∞)⁻¹ ≤ (m : ℝ≥0∞)⁻¹ :=
            ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (hm d hd))
          calc ∑' α, PMF.uniformOfFintype (ZMod (F.order d)) α *
                ∑' β, PMF.uniformOfFintype (ZMod (F.order d)) β *
                  ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
                    (ProbComp.eval (adversary n
                      (d, F.encode d (α • F.generator d),
                        F.encode d (β • F.generator d)))).bind fun guess =>
                      PMF.pure (decide (guess = F.encode d (γ • F.generator d)))) true
              ≤ ∑' α, PMF.uniformOfFintype (ZMod (F.order d)) α *
                  ∑' β, PMF.uniformOfFintype (ZMod (F.order d)) β * (m : ℝ≥0∞)⁻¹ := by
                refine ENNReal.tsum_le_tsum fun α => mul_le_mul_of_nonneg_left ?_ zero_le
                refine ENNReal.tsum_le_tsum fun β => mul_le_mul_of_nonneg_left ?_ zero_le
                rw [PMF.bind_comm, PMF.bind_apply]
                calc ∑' guess, ProbComp.eval (adversary n
                        (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d))) guess *
                      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
                        PMF.pure (decide (guess = F.encode d (γ • F.generator d)))) true
                    ≤ ∑' guess, ProbComp.eval (adversary n
                        (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d))) guess *
                      (m : ℝ≥0∞)⁻¹ := by
                      refine ENNReal.tsum_le_tsum fun guess =>
                        mul_le_mul_of_nonneg_left
                          ((F.uniform_decide_eq_encode_le d guess).trans hord) zero_le
                  _ = (m : ℝ≥0∞)⁻¹ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
            _ = (m : ℝ≥0∞)⁻¹ := by
                simp only [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
        · have hd0 : setup n d = 0 := by rwa [PMF.mem_support_iff, not_not] at hd
          simp only [hd0, zero_mul, le_rfl]
    _ = (m : ℝ≥0∞)⁻¹ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **Quantitative reduction from CDH to DDH**: when every supported group at parameter `n` has
order at least `m > 0`, any CDH adversary's success probability is at most the DDH distinguishing
advantage of `cdhToDDHDistinguisher` plus `1 / m`. -/
theorem succProbability_cdhGame_le_advantage_ddh_add (setup : ℕ → PMF F.Desc)
    (adversary : ℕ → F.Desc × List Bool × List Bool → ProbComp (List Bool)) (n m : ℕ)
    (hm0 : 0 < m) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d) :
    Game.succProbability (F.cdhGame setup adversary n) ≤
      Game.advantage (F.ddhRealGame setup (F.cdhToDDHDistinguisher adversary) n)
        (F.ddhIdealGame setup (F.cdhToDDHDistinguisher adversary) n) + 1 / m := by
  have hideal :
      Game.succProbability (F.ddhIdealGame setup (F.cdhToDDHDistinguisher adversary) n) ≤
        1 / m := by
    have htop : (m : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr hm0.ne')
    simpa only [one_div, ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast] using
      ENNReal.toNNReal_mono htop
        (F.ddhIdealGame_cdhToDDHDistinguisher_true_le setup adversary n m hm)
  rw [← F.ddhRealGame_cdhToDDHDistinguisher]
  calc Game.succProbability (F.ddhRealGame setup (F.cdhToDDHDistinguisher adversary) n)
      ≤ Game.advantage (F.ddhRealGame setup (F.cdhToDDHDistinguisher adversary) n)
          (F.ddhIdealGame setup (F.cdhToDDHDistinguisher adversary) n) +
        Game.succProbability (F.ddhIdealGame setup (F.cdhToDDHDistinguisher adversary) n) := by
        simpa only [Game.advantage_pure_false] using
          Game.advantage_triangle
            (F.ddhRealGame setup (F.cdhToDDHDistinguisher adversary) n)
            (F.ddhIdealGame setup (F.cdhToDDHDistinguisher adversary) n)
            (PMF.pure false)
    _ ≤ Game.advantage (F.ddhRealGame setup (F.cdhToDDHDistinguisher adversary) n)
          (F.ddhIdealGame setup (F.cdhToDDHDistinguisher adversary) n) + 1 / m := by
        gcongr

/-- The CDH-to-DDH reduction is uniform strict PPT when the CDH adversary is. -/
theorem isPPTOn_cdhToDDHDistinguisher
    {adversary : ℕ → F.Desc × List Bool × List Bool → ProbComp (List Bool)}
    (hA : IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits encBits))) encBits
      (fun input => adversary input.1 input.2)) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => F.cdhToDDHDistinguisher adversary input.1 input.2) := by
  unfold cdhToDDHDistinguisher
  refine (hA.preprocess
    (prepare := fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
      (input.1, (input.2.1, input.2.2.1, input.2.2.2.1))) (by fun_prop)).bind_with ?_
  have heq : ComputableTidilyInPolyTime
      (fun p : (ℕ × F.Desc × List Bool × List Bool × List Bool) × List Bool =>
        decide (p.2 = p.1.2.2.2.2))
      (encPair (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
        encBits) encBool :=
    ComputableTidilyInPolyTime.decide_eq' (encB := encBits) (by fun_prop) (by fun_prop)
  exact ComputableTidilyInPolyTime.isPPTOn heq

/-- **DDH implies CDH** when every supported group at parameter `n` has order at least `m n > 0`
and `1 / m n` is negligible. -/
theorem DDH.cdh {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc} (hDDH : F.DDH setup)
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n) (hm : ∀ n, ∀ d ∈ (setup n).support, m n ≤ F.order d)
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) : F.CDH setup := by
  intro adversary hA
  exact negligible_of_le ((hDDH _ (F.isPPTOn_cdhToDDHDistinguisher hA)).add hinv)
    fun n => F.succProbability_cdhGame_le_advantage_ddh_add setup adversary n (m n) (hm0 n) (hm n)

/-- **DDH implies the discrete-logarithm assumption** when every supported group at parameter `n`
has order at least `m n > 0` and `1 / m n` is negligible. -/
theorem DDH.discreteLog {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc} (hDDH : F.DDH setup)
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n) (hm : ∀ n, ∀ d ∈ (setup n).support, m n ≤ F.order d)
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) : F.DiscreteLog setup :=
  (hDDH.cdh hm0 hm hinv).discreteLog

/-! ### Random self-reducibility of DDH -/

/-- Re-randomize a candidate DDH triple `(u, v, w)` in `F.Carrier d` using exponents
`r, s₁, s₂ : ZMod (F.order d)`. -/
def ddhRerandomize (d : F.Desc) (u v w : F.Carrier d)
    (r s₁ s₂ : ZMod (F.order d)) : F.Carrier d × F.Carrier d × F.Carrier d :=
  (r • u + s₁ • F.generator d,
    v + s₂ • F.generator d,
    r • w + (r * s₂) • u + s₁ • v + (s₁ * s₂) • F.generator d)

/-- Algebraic action of `ddhRerandomize` on multiples of the generator: a tuple error
`γ - α * β` is scaled by `r` and added to the new Diffie–Hellman product
`(r * α + s₁) * (β + s₂)`. -/
theorem ddhRerandomize_smul_generator (d : F.Desc) (α β γ r s₁ s₂ : ZMod (F.order d)) :
    F.ddhRerandomize d (α • F.generator d) (β • F.generator d) (γ • F.generator d) r s₁ s₂ =
      ((r * α + s₁) • F.generator d,
        (β + s₂) • F.generator d,
        ((r * α + s₁) * (β + s₂) + r * (γ - α * β)) • F.generator d) := by
  simp only [ddhRerandomize, smul_smul, ← add_smul]
  refine Prod.ext rfl (Prod.ext rfl (congrArg (· • F.generator d) (by ring)))

/-- The re-randomized triple distribution obtained by drawing `r, s₁, s₂ : ZMod (F.order d)`
independently and uniformly. -/
noncomputable def ddhRerandomizeLaw (d : F.Desc) (u v w : F.Carrier d) :
    PMF (F.Carrier d × F.Carrier d × F.Carrier d) := do
  let r ← PMF.uniformOfFintype (ZMod (F.order d))
  let s₁ ← PMF.uniformOfFintype (ZMod (F.order d))
  let s₂ ← PMF.uniformOfFintype (ZMod (F.order d))
  return F.ddhRerandomize d u v w r s₁ s₂

/-- The real DDH tuple distribution on `F.Carrier d`. -/
noncomputable def ddhRealTupleLaw (d : F.Desc) :
    PMF (F.Carrier d × F.Carrier d × F.Carrier d) := do
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  return (α • F.generator d, β • F.generator d, (α * β) • F.generator d)

/-- The ideal DDH tuple distribution on `F.Carrier d`. -/
noncomputable def ddhIdealTupleLaw (d : F.Desc) :
    PMF (F.Carrier d × F.Carrier d × F.Carrier d) := do
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let γ ← PMF.uniformOfFintype (ZMod (F.order d))
  return (α • F.generator d, β • F.generator d, γ • F.generator d)

private theorem uniformOfFintype_bind_equiv {α β : Type*} [Fintype α] [Nonempty α]
    (e : α ≃ α) (f : α → PMF β) :
    (PMF.uniformOfFintype α).bind (fun a => f (e a)) = (PMF.uniformOfFintype α).bind f := by
  change (PMF.uniformOfFintype α).bind (f ∘ e) = (PMF.uniformOfFintype α).bind f
  rw [← PMF.bind_map, PMF.uniformOfFintype_map_equiv]

/-- **Random self-reducibility of DDH (real case)**: re-randomizing any fixed real DDH tuple
`(α • g, β • g, (α * β) • g)` yields the exact uniform real DDH tuple distribution. -/
theorem ddhRerandomizeLaw_real (d : F.Desc) (α β : ZMod (F.order d)) :
    F.ddhRerandomizeLaw d (α • F.generator d) (β • F.generator d) ((α * β) • F.generator d) =
      F.ddhRealTupleLaw d := by
  simp only [ddhRerandomizeLaw, ddhRealTupleLaw, ddhRerandomize_smul_generator, sub_self, mul_zero,
    add_zero, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  have hs₂ (α' : ZMod (F.order d)) :
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₂ =>
        PMF.pure (α' • F.generator d, (β + s₂) • F.generator d,
          (α' * (β + s₂)) • F.generator d)) =
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
        PMF.pure (α' • F.generator d, β' • F.generator d, (α' * β') • F.generator d)) :=
    uniformOfFintype_bind_equiv (Equiv.addLeft β)
      (fun β' => PMF.pure (α' • F.generator d, β' • F.generator d, (α' * β') • F.generator d))
  have hs₁ (r : ZMod (F.order d)) :
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₁ =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₂ =>
          PMF.pure ((r * α + s₁) • F.generator d, (β + s₂) • F.generator d,
            ((r * α + s₁) * (β + s₂)) • F.generator d)) =
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α' =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
          PMF.pure (α' • F.generator d, β' • F.generator d, (α' * β') • F.generator d)) := by
    simp_rw [hs₂]
    exact uniformOfFintype_bind_equiv (Equiv.addLeft (r * α))
      (fun α' => (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
        PMF.pure (α' • F.generator d, β' • F.generator d, (α' * β') • F.generator d))
  simp_rw [hs₁, PMF.bind_const]

/-- **Random self-reducibility of DDH (ideal case)**: re-randomizing any fixed non-DDH tuple
`(α • g, β • g, γ • g)` with `γ ≠ α * β` yields the exact uniform ideal DDH tuple distribution. -/
theorem ddhRerandomizeLaw_ideal (d : F.Desc) {α β γ : ZMod (F.order d)} (hγ : γ ≠ α * β) :
    F.ddhRerandomizeLaw d (α • F.generator d) (β • F.generator d) (γ • F.generator d) =
      F.ddhIdealTupleLaw d := by
  simp only [ddhRerandomizeLaw, ddhIdealTupleLaw, ddhRerandomize_smul_generator,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  have hs₂ (r α' : ZMod (F.order d)) :
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₂ =>
        PMF.pure (α' • F.generator d, (β + s₂) • F.generator d,
          (α' * (β + s₂) + r * (γ - α * β)) • F.generator d)) =
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
        PMF.pure (α' • F.generator d, β' • F.generator d,
          (α' * β' + r * (γ - α * β)) • F.generator d)) :=
    uniformOfFintype_bind_equiv (Equiv.addLeft β)
      (fun β' => PMF.pure (α' • F.generator d, β' • F.generator d,
        (α' * β' + r * (γ - α * β)) • F.generator d))
  have hs₁ (r : ZMod (F.order d)) :
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₁ =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₂ =>
          PMF.pure ((r * α + s₁) • F.generator d, (β + s₂) • F.generator d,
            ((r * α + s₁) * (β + s₂) + r * (γ - α * β)) • F.generator d)) =
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α' =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
          PMF.pure (α' • F.generator d, β' • F.generator d,
            (α' * β' + r * (γ - α * β)) • F.generator d)) := by
    simp_rw [hs₂]
    exact uniformOfFintype_bind_equiv (Equiv.addLeft (r * α))
      (fun α' => (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
        PMF.pure (α' • F.generator d, β' • F.generator d,
          (α' * β' + r * (γ - α * β)) • F.generator d))
  simp_rw [hs₁]
  rw [PMF.bind_comm]
  congr 1; funext α'
  rw [PMF.bind_comm]
  congr 1; funext β'
  exact uniformOfFintype_bind_equiv
    ((Equiv.mulRight₀ (γ - α * β) (sub_ne_zero.mpr hγ)).trans (Equiv.addLeft (α' * β')))
    (fun γ' => PMF.pure (α' • F.generator d, β' • F.generator d, γ' • F.generator d))

end Cslib.Crypto.PrimeOrderGroupFamily
