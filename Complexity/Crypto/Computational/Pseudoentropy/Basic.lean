/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Basic
public import Complexity.Probability.Entropy
import Complexity.Tactic.PPT

/-!
# Samplable pseudoentropy pairs

A pair consists of a public observation and a hidden bit. The observation has a finite type
at each parameter and an injective word encoding, so its conditional entropy is unambiguous.
A strict PPT sampler realizes the joint law exactly.

`SamplablePair.HasGap` says that every uniform PPT predictor eventually has signed correlation
at most `1 - H(hidden | observation) - gap`. This is the entropy threshold used in the
OWF-to-PRG construction; merely being hard to predict is not sufficient.

This interface records the joint law and its sampler. The shared saved-coin interface exposes a
strict PPT sampler's fair-bit tape as a uniform seed, including unused randomness.

## Main definitions

* `Cslib.Crypto.Pseudoentropy.predictionGame`: predict a sampled hidden bit from its observation.
* `Cslib.Crypto.Pseudoentropy.SamplablePair`: a finite joint law with a uniform strict PPT sampler.
* `Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap`: the conditional-entropy prediction threshold.

## Main results

* `Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.eventually_error_ge`: prediction error bound.
* `Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.eventually_entropy_add_gap_le_one`:
  the threshold forced by an independent fair-bit predictor.

## References

* [T. Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*][Holenstein2006], Definitions 3 and 4. We use a sampler presentation and uniform
  strict PPT predictors. Signed correlation is twice success probability minus one.

Adapted from `Crypto/Computational/Pseudoentropy/Basic.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the shared nonnegative game API and tidy machine
certificates. Existence of a pair with a positive gap is a separate security theorem.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy

open Probability Filter Turing.MultiTapeTM

local notation "Pr[" p "]" => (Game.succProbability (ProbComp.eval p) : ℝ)

/-- Predict the hidden bit from the public component of a sampled pair. -/
noncomputable def predictionGame (sample : ℕ → ProbComp (List Bool × Bool))
    (adversary : Distinguisher) (n : ℕ) : ProbComp Bool := do
  let pair ← sample n
  let guess ← adversary n pair.1
  return guess == pair.2

/-- The complete prediction experiment is strict PPT whenever the sampler and predictor are. -/
@[program_certificate]
theorem isPPTOn_predictionGame {sample : ℕ → ProbComp (List Bool × Bool)}
    (hsample : IsPPTOn encUnary (encPair encBits encBool) sample) {adversary : Distinguisher}
    (hadversary : IsPPT encBool adversary) :
    IsPPTOn encUnary encBool (predictionGame sample adversary) := by
  unfold predictionGame
  ppt

/-- A finite joint law together with its exact strict PPT word sampler. -/
structure SamplablePair where
  /-- The public information available at each parameter. -/
  Observation : ℕ → Type
  /-- Its alphabet is finite, without requiring a computable enumeration. -/
  [finite : ∀ n, Finite (Observation n)]
  /-- Encoding preserves all the public information. -/
  encode : ∀ n, Observation n ↪ List Bool
  /-- The public observation and hidden bit. -/
  joint : ∀ n, PMF (Observation n × Bool)
  /-- A word-level sampler with the strict fair-coin realization certified below. -/
  sample : ℕ → ProbComp (List Bool × Bool)
  /-- Its complete running time is bounded by one polynomial. -/
  efficient : IsPPTOn encUnary (encPair encBits encBool) sample
  /-- The sampler realizes the finite joint law exactly. -/
  eval_sample : ∀ n, ProbComp.eval (sample n) =
    (joint n).map (fun pair => (encode n pair.1, pair.2))

attribute [instance] SamplablePair.finite

namespace SamplablePair

/-- Every uniform PPT predictor stays below the conditional-entropy threshold by this gap.
The threshold beyond which the inequality holds may depend on the predictor. -/
def HasGap (pair : SamplablePair) (gap : ℕ → ℝ) : Prop :=
  ∀ adversary : Distinguisher, IsPPT encBool adversary →
    ∀ᶠ n in atTop, 2 * Pr[predictionGame pair.sample adversary n] - 1 ≤
      1 - PMF.conditionalEntropy (pair.joint n) - gap n

/-- The pseudoentropy threshold equivalently lower-bounds each efficient predictor's error. -/
theorem HasGap.eventually_error_ge {pair : SamplablePair} {gap : ℕ → ℝ}
    (hgap : pair.HasGap gap) (adversary : Distinguisher)
    (hefficient : IsPPT encBool adversary) :
    ∀ᶠ n in atTop, (PMF.conditionalEntropy (pair.joint n) + gap n) / 2 ≤
      (ProbComp.eval (predictionGame pair.sample adversary n) false).toReal := by
  filter_upwards [hgap adversary hefficient] with n hn
  have hsum := PMF.sum_toReal (ProbComp.eval (predictionGame pair.sample adversary n))
  simp only [Fintype.sum_bool] at hsum
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal] at hn
  linarith

/-- A fair-bit predictor has zero correlation, so entropy plus the prediction gap cannot
eventually exceed one. -/
theorem HasGap.eventually_entropy_add_gap_le_one {pair : SamplablePair} {gap : ℕ → ℝ}
    (hgap : pair.HasGap gap) :
    ∀ᶠ n in atTop, PMF.conditionalEntropy (pair.joint n) + gap n ≤ 1 := by
  have h := hgap (fun _ _ => ProbComp.uniform Bool) (by ppt)
  have hfair (n : ℕ) :
      Pr[predictionGame pair.sample (fun _ _ => ProbComp.uniform Bool) n] = 1 / 2 := by
    simp [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, predictionGame,
      ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_apply, PMF.map_apply,
      PMF.uniformOfFintype_apply, ENNReal.tsum_mul_right, PMF.tsum_coe]
  filter_upwards [h] with n hn
  rw [hfair] at hn
  linarith

/-- A smaller requested gap follows from any larger proved gap. -/
theorem HasGap.mono {pair : SamplablePair} {gap smaller : ℕ → ℝ} (h : pair.HasGap gap)
    (hle : ∀ n, smaller n ≤ gap n) : pair.HasGap smaller := by
  intro adversary hPPT
  filter_upwards [h adversary hPPT] with n hn
  exact hn.trans (sub_le_sub_left (hle n) _)

end SamplablePair

end Cslib.Crypto.Pseudoentropy
