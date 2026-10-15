/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Layouts.BoundedDegree
public import Complexity.Computability.Circuit.Frontier.Layouts.Gaussian
public import Complexity.Computability.Circuit.Frontier.LowerBound

/-!
# Frontier lower bounds for fan-in two

The frontier lower bound for fan-in two (`Cslib.Circuits.Frontier.eventually_lt_innerSize`) is
conditional on the layout hypothesis `LayoutBound 3 A`, and gives `s > (1 + 1/A - ε) n`. Two
layout bounds remove the hypothesis:

* median edge-score layouts give `A = 2p` with `p = (3 / (2π)) arccos ((1 + 2√2)/4)`
  (`Cslib.Circuits.Frontier.layoutBound_gaussian`), so `1 + 1/A = L`;
* vertex-score layouts give `A = 1/3` (`Cslib.Circuits.Frontier.layoutBound_one_third`), so
  `1 + 1/A = 4`.

Let `S_n ⊆ U^n` be `K_n`-rectangle-free sets over a finite alphabet `U` with at least two
symbols, with `log K_n = o(n)` and `n log |U| - log |S_n| = o(n)`. Then for every `ε > 0` and all
large `n`, every circuit of fan-in at most two deciding `S_n`, over any basis and interpretation
on `U`, has more than

* `(L - ε) n` inner gates, with `L = 1 + π / (3 arccos ((1 + 2√2)/4)) = 4.5624977…`
  (`Cslib.Circuits.Frontier.eventually_gaussian_sub_mul_lt_innerSize`);
* `(114/25 - ε) n = (4.56 - ε) n` inner gates, since `L ≥ 114/25`
  (`Cslib.Circuits.Frontier.eventually_114_div_25_sub_mul_lt_innerSize`);
* `(4 - ε) n` inner gates (`Cslib.Circuits.Frontier.eventually_four_sub_mul_lt_innerSize`).

Gates of arity zero, the constants, are not counted. The hypotheses are those of
`Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_innerSize`: the bounds apply to every family
of dense rectangle-free sets, and to a particular family once it is shown to be one.

## Main results

* `Cslib.Circuits.Frontier.eventually_gaussian_sub_mul_lt_innerSize`: `s > (L - ε) n`.
* `Cslib.Circuits.Frontier.eventually_114_div_25_sub_mul_lt_innerSize`: `s > (114/25 - ε) n`.
* `Cslib.Circuits.Frontier.eventually_four_sub_mul_lt_innerSize`: `s > (4 - ε) n`.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Filter Asymptotics Real

universe u v

variable {U : Type u} [Finite U] [Nontrivial U] {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}

/-- **The Gaussian frontier lower bound for fan-in two.** Let `S_n ⊆ U^n` be `K_n`-rectangle-free
sets over a finite alphabet `U` with at least two symbols, with `log K_n = o(n)` and
`n log |U| - log |S_n| = o(n)`. Then for every `ε > 0` and all large `n`, every circuit of fan-in
at most two deciding `S_n`, over any basis and interpretation on `U`, has more than `(L - ε) n`
inner gates, where `L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625`. -/
theorem eventually_gaussian_sub_mul_lt_innerSize
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (1 + π / (3 * arccos ((1 + 2 * √2) / 4)) - ε) * n < c.innerSize := by
  have h := eventually_lt_innerSize (mul_pos two_pos Gaussian.gaussianCoefficient_pos)
    layoutBound_gaussian hfree hK hdense hε
  rwa [Gaussian.one_add_inv_two_mul_gaussianCoefficient] at h

/-- **The `(4.56 - ε) n` frontier lower bound for fan-in two.** Under the hypotheses of
`eventually_gaussian_sub_mul_lt_innerSize`, for every `ε > 0` and all large `n`, every circuit of
fan-in at most two deciding `S_n`, over any basis and interpretation on `U`, has more than
`(114/25 - ε) n` inner gates. -/
theorem eventually_114_div_25_sub_mul_lt_innerSize
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (114 / 25 - ε) * n < c.innerSize := by
  filter_upwards [eventually_gaussian_sub_mul_lt_innerSize.{u, v} hfree hK hdense hε] with n hn
  intro σ I Acc c hfan hS
  refine lt_of_le_of_lt ?_ (hn σ I Acc c hfan hS)
  exact mul_le_mul_of_nonneg_right (by linarith [Gaussian.circuitCoefficient_ge_456])
    (Nat.cast_nonneg n)

/-- **The `(4 - ε) n` frontier lower bound for fan-in two.** Under the hypotheses of
`eventually_gaussian_sub_mul_lt_innerSize`, for every `ε > 0` and all large `n`, every circuit of
fan-in at most two deciding `S_n`, over any basis and interpretation on `U`, has more than
`(4 - ε) n` inner gates. The layout bound is that of Gaussian vertex scores. -/
theorem eventually_four_sub_mul_lt_innerSize
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (4 - ε) * n < c.innerSize := by
  have h := eventually_lt_innerSize (by norm_num) layoutBound_one_third hfree hK hdense hε
  rwa [show (1 : ℝ) + 1 / (1 / 3) = 4 by norm_num] at h

end Cslib.Circuits.Frontier
