/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.BoundedFanIn
public import Complexity.Computability.Circuit.Frontier.Extractor.Distributional
public import Complexity.Computability.Circuit.Frontier.FanInTwo
public import Complexity.Computability.Circuit.Frontier.Ledger.Unconditional
public import Complexity.Computability.Circuit.Frontier.Nondeterministic
public import Complexity.Init

/-!
# Conditional frontier circuit lower bounds from sumset extractors

Combining the extractor-to-frontier bridge (`IsSumsetExtractor.rectangleBias_ceil`,
`IsSumsetExtractor.sumsetBias_ceil`) with the unconditional Gaussian and bounded-fan-in frontier
lower bounds yields conditional average-case and worst-case circuit lower bounds for any family of
Boolean sumset extractors `E_n : (Fin n → U) → Bool` with sublinear min-entropy `k_n = o(n)`:

* **Average-case lower bounds** (`eventually_agreement_le_of_isSumsetExtractor`,
  `eventually_agreement_le_of_isSumsetExtractor_fullSignature`): any fan-in-two circuit of size at
  most `(4.56249 - ε) n` agrees with `E_n` on at most `1 / 2 + δ_n + exp(-γ n)` of the inputs;
* **Worst-case lower bounds** (factored through `frontierHypotheses_of_isSumsetExtractor` whenever
  `δ_n ≤ δ₀ < 1 / 2`):
  - `(4.56249 - ε) n` for fan-in-two circuits and `fullSignature 2 Bool`
    (`eventually_gaussian_sub_mul_lt_innerSize_of_isSumsetExtractor`,
    `eventually_456249_div_100000_sub_mul_lt_size_of_isSumsetExtractor`);
  - `(r - 1) s > (2 - ε) n`, `(1 + 1 / degreeCoefficient (r + 1) - ε) n < (r - 1) s`, and
    `(7 / 2 - ε) n < 2 s` for bounded fan-in `r ≥ 2` and `r = 3`
    (`eventually_two_sub_mul_lt_mul_innerSize_of_isSumsetExtractor`,
    `eventually_degreeCoefficient_lt_mul_innerSize_of_isSumsetExtractor`,
    `eventually_seven_div_two_lt_two_mul_innerSize_of_isSumsetExtractor`);
  - `(4.56249 - ε) n` for nondeterministic fan-in-two circuits uniformly in the number of witness
    inputs
    (`eventually_456249_div_100000_sub_mul_lt_innerSize_nondeterministic_of_isSumsetExtractor`);
  - `(4.56249 - ε) n` ordinary fan-in-two gates for circuits with `o(n)` monoid-aggregate gates of
    unbounded fan-in
    (`eventually_456249_div_100000_sub_mul_lt_card_of_aggregates_of_isSumsetExtractor`).

## Main results

* `Cslib.Circuits.Frontier.frontierHypotheses_of_isSumsetExtractor`: packages the three worst-case
  frontier hypotheses (`RectangleFree`, sublinear log-threshold, and `o(n)` logarithmic density
  deficit) for any sumset-extractor family with `k_n = o(n)` and `δ_n ≤ δ₀ < 1 / 2`.
* `Cslib.Circuits.Frontier.eventually_agreement_le_of_isSumsetExtractor`: conditional Gaussian
  frontier average-case lower bound.
* `Cslib.Circuits.Frontier.eventually_456249_div_100000_sub_mul_lt_size_of_isSumsetExtractor`,
  `Cslib.Circuits.Frontier.eventually_degreeCoefficient_lt_mul_innerSize_of_isSumsetExtractor`:
  conditional worst-case frontier lower bounds across bounded-fan-in, nondeterministic, and
  aggregate-gate circuit models.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
* [S. Schlesinger, *Frontier circuit lower bounds and two-source sumset extractors in
  Complexitylib*][Schlesinger2026FrontierExtractor]
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Filter Asymptotics Real

universe u v w

variable {U : Type u}

/-- **Any sumset-extractor family with sublinear min-entropy `k_n = o(n)` and error bounded away
from `1 / 2` eventually satisfies all three worst-case frontier hypotheses** at threshold
`⌈2^(k_n)⌉₊`. -/
theorem frontierHypotheses_of_isSumsetExtractor [AddGroup U] [Finite U] [Nontrivial U]
    {E : ∀ n, (Fin n → U) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2) :
    (∀ᶠ n in atTop, RectangleFree {z | E n z = true} ⌈(2 : ℝ) ^ k n⌉₊) ∧
    ((fun n => Real.log (⌈(2 : ℝ) ^ k n⌉₊ : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ)) ∧
    ((fun n => n * Real.log (Nat.card U) - Real.log {z | E n z = true}.ncard) =o[atTop]
      fun n : ℕ => (n : ℝ)) := by
  have hsumset : ∀ᶠ n in atTop, SumsetBias {z | E n z = true} ⌈(2 : ℝ) ^ k n⌉₊ (δ n) :=
    hE.mono fun n hn => hn.sumsetBias_ceil
  have hfree : ∀ᶠ n in atTop, RectangleFree {z | E n z = true} ⌈(2 : ℝ) ^ k n⌉₊ := by
    filter_upwards [hsumset, hδ] with n hsn hδn
    exact hsn.rectangleFree (Nat.ceil_pos.mpr (by positivity)) (hδn.trans_lt hδ₀)
  have hK := isLittleO_log_ceil_two_rpow hk
  exact ⟨hfree, hK, isLittleO_sub_log_ncard_of_sumsetBias hsumset hK hδ hδ₀⟩

/-- **Conditional Gaussian frontier average-case lower bound from a sumset-extractor family.**
If `E_n : (Fin n → U) → Bool` is a `(k_n, δ_n)`-sumset extractor with `k_n = o(n)`, then for every
`ε > 0` there is `γ > 0` such that eventually every fan-in-two circuit `c` of inner size at most
`(L - ε) n` agrees with `{z | E_n z = true}` on at most a
`1 / 2 + δ_n + exp (-γ n)` fraction of the inputs, where
`L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625`. -/
theorem eventually_agreement_le_of_isSumsetExtractor [AddZeroClass U] [Finite U] [Nontrivial U]
    {E : ∀ n, (Fin n → U) → Bool} {k δ : ℕ → ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ > 0, ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 →
        (c.innerSize : ℝ) ≤ (1 + π / (3 * arccos ((1 + 2 * √2) / 4)) - ε) * n →
        agreement {z | E n z = true} {x | c.eval I x 0 ∈ Acc} ≤
          1 / 2 + δ n + Real.exp (-(γ * n)) := by
  have hbias : ∀ᶠ n in atTop, RectangleBias {z | E n z = true} ⌈(2 : ℝ) ^ k n⌉₊ (δ n) :=
    hE.mono fun n hn => hn.rectangleBias_ceil
  obtain ⟨γ, hγ, H⟩ := averageCaseBound_gaussian.{u, v} ε hε
  exact ⟨γ, hγ, H U (fun n => {z | E n z = true}) _ δ hbias (isLittleO_log_ceil_two_rpow hk)⟩

/-- **Conditional `(4.56249 - ε) n` average-case lower bound over `fullSignature 2 Bool`.**
If `E_n : (Fin n → Bool) → Bool` is a `(k_n, δ_n)`-sumset extractor with `k_n = o(n)`, then for
every `ε > 0` there is `γ > 0` such that eventually every circuit `c` over `fullSignature 2 Bool`
of size at most `(456249 / 100000 - ε) n` agrees with `{z | E_n z = true}` on at most a
`1 / 2 + δ_n + exp (-γ n)` fraction of the inputs. -/
theorem eventually_agreement_le_of_isSumsetExtractor_fullSignature
    {E : ∀ n, (Fin n → Bool) → Bool} {k δ : ℕ → ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ > 0, ∀ᶠ n in atTop, ∀ (I : Interpretation (fullSignature 2 Bool) Bool) (Acc : Set Bool)
      (c : Circuit (fullSignature 2 Bool) n 1),
        (c.size : ℝ) ≤ (456249 / 100000 - ε) * n →
        agreement {z | E n z = true} {x | c.eval I x 0 ∈ Acc} ≤
          1 / 2 + δ n + Real.exp (-(γ * n)) := by
  obtain ⟨γ, hγ, hbound⟩ := eventually_agreement_le_of_isSumsetExtractor.{0, 0} hE hk hε
  refine ⟨γ, hγ, hbound.mono fun n hn I Acc c hsize => ?_⟩
  have hinner : (c.innerSize : ℝ) ≤ (1 + π / (3 * arccos ((1 + 2 * √2) / 4)) - ε) * n := by
    calc (c.innerSize : ℝ) ≤ c.size := by exact_mod_cast c.innerSize_le_size
      _ ≤ (456249 / 100000 - ε) * n := hsize
      _ ≤ (1 + π / (3 * arccos ((1 + 2 * √2) / 4)) - ε) * n :=
        mul_le_mul_of_nonneg_right (by linarith [Gaussian.circuitCoefficient_ge_456249])
          (Nat.cast_nonneg n)
  exact hn (fullSignature 2 Bool) I Acc c c.fanInAtMost_fullSignature hinner

/-- **Conditional Gaussian frontier worst-case lower bound from a sumset-extractor family.**
If `E_n : (Fin n → U) → Bool` is a `(k_n, δ_n)`-sumset extractor with `k_n = o(n)` and
`δ_n ≤ δ₀ < 1 / 2` eventually, then for every `ε > 0` and all large `n`, every fan-in-two circuit
deciding `{z | E_n z = true}` has more than `(L - ε) n` inner gates. -/
theorem eventually_gaussian_sub_mul_lt_innerSize_of_isSumsetExtractor [AddGroup U] [Finite U]
    [Nontrivial U] {E : ∀ n, (Fin n → U) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc {z | E n z = true} →
        (1 + π / (3 * arccos ((1 + 2 * √2) / 4)) - ε) * n < c.innerSize := by
  obtain ⟨hfree, hK, hdense⟩ := frontierHypotheses_of_isSumsetExtractor hE hk hδ hδ₀
  exact eventually_gaussian_sub_mul_lt_innerSize.{u, v} hfree hK hdense hε

/-- **Conditional `(4.56249 - ε) n` worst-case lower bound from a sumset-extractor family.** -/
theorem eventually_456249_div_100000_sub_mul_lt_innerSize_of_isSumsetExtractor [AddGroup U]
    [Finite U] [Nontrivial U] {E : ∀ n, (Fin n → U) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc {z | E n z = true} →
        (456249 / 100000 - ε) * n < c.innerSize := by
  filter_upwards [eventually_gaussian_sub_mul_lt_innerSize_of_isSumsetExtractor.{u, v}
    hE hk hδ hδ₀ hε] with n hn σ I Acc c hfan hdec
  refine lt_of_le_of_lt ?_ (hn σ I Acc c hfan hdec)
  exact mul_le_mul_of_nonneg_right (by linarith [Gaussian.circuitCoefficient_ge_456249])
    (Nat.cast_nonneg n)

/-- **Conditional `(4.56249 - ε) n` worst-case circuit size lower bound over
`fullSignature 2 Bool`.** -/
theorem eventually_456249_div_100000_sub_mul_lt_size_of_isSumsetExtractor
    {E : ∀ n, (Fin n → Bool) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (I : Interpretation (fullSignature 2 Bool) Bool) (Acc : Set Bool)
      (c : Circuit (fullSignature 2 Bool) n 1), c.Decides I Acc {z | E n z = true} →
        (456249 / 100000 - ε) * n < c.size := by
  filter_upwards [eventually_456249_div_100000_sub_mul_lt_innerSize_of_isSumsetExtractor.{0, 0}
    hE hk hδ hδ₀ hε] with n hn I Acc c hdec
  exact (hn (fullSignature 2 Bool) I Acc c c.fanInAtMost_fullSignature hdec).trans_le
    (by exact_mod_cast c.innerSize_le_size)

/-- **Conditional `(4.56249 - ε) n` worst-case circuit size lower bound for circuits computing
`single (E n)` over `fullSignature 2 Bool`.** -/
theorem eventually_456249_div_100000_sub_mul_lt_size_of_isSumsetExtractor_computes
    {E : ∀ n, (Fin n → Bool) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (I : Interpretation (fullSignature 2 Bool) Bool)
      (c : Circuit (fullSignature 2 Bool) n 1), c.Computes I (single (E n)) →
        (456249 / 100000 - ε) * n < c.size := by
  filter_upwards [eventually_456249_div_100000_sub_mul_lt_size_of_isSumsetExtractor
    hE hk hδ hδ₀ hε] with n hn I c hc
  exact hn I {true} c (hc.decides {true})

/-- **Conditional `(r - 1) s > (2 - ε) n` frontier lower bound for general fan-in `r ≥ 2` from a
sumset-extractor family.** -/
theorem eventually_two_sub_mul_lt_mul_innerSize_of_isSumsetExtractor [AddGroup U] [Finite U]
    [Nontrivial U] {E : ∀ n, (Fin n → U) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {r : ℕ} (hr : 2 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc {z | E n z = true} →
        (2 - ε) * n < (r - 1) * c.innerSize := by
  obtain ⟨hfree, hK, hdense⟩ := frontierHypotheses_of_isSumsetExtractor hE hk hδ hδ₀
  exact eventually_two_sub_mul_lt_mul_innerSize.{u, v} hr hfree hK hdense hε

/-- **Conditional Gaussian vertex-score frontier lower bound for fan-in at most `r ≥ 2` from a
sumset-extractor family.** -/
theorem eventually_degreeCoefficient_lt_mul_innerSize_of_isSumsetExtractor [AddGroup U] [Finite U]
    [Nontrivial U] {E : ∀ n, (Fin n → U) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {r : ℕ} (hr : 2 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc {z | E n z = true} →
        (1 + 1 / Gaussian.degreeCoefficient (r + 1) - ε) * n < (r - 1) * c.innerSize := by
  obtain ⟨hfree, hK, hdense⟩ := frontierHypotheses_of_isSumsetExtractor hE hk hδ hδ₀
  exact eventually_degreeCoefficient_lt_mul_innerSize.{u, v} hr hfree hK hdense hε

/-- **Conditional `(7 / 2 - ε) n < 2 s` frontier lower bound for fan-in at most three from a
sumset-extractor family.** -/
theorem eventually_seven_div_two_lt_two_mul_innerSize_of_isSumsetExtractor [AddGroup U] [Finite U]
    [Nontrivial U] {E : ∀ n, (Fin n → U) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 3 → c.Decides I Acc {z | E n z = true} →
        (7 / 2 - ε) * n < 2 * c.innerSize := by
  obtain ⟨hfree, hK, hdense⟩ := frontierHypotheses_of_isSumsetExtractor hE hk hδ hδ₀
  exact eventually_seven_div_two_lt_two_mul_innerSize.{u, v} hfree hK hdense hε

/-- **Conditional Gaussian frontier lower bound for nondeterministic circuits of fan-in two from a
sumset-extractor family**, uniformly in the number `k'` of witness inputs. -/
theorem eventually_gaussian_sub_mul_lt_innerSize_nondeterministic_of_isSumsetExtractor
    [AddGroup U] [Finite U] [Nontrivial U] {E : ∀ n, (Fin n → U) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k' : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k') 1), c.FanInAtMost 2 →
        c.NondeterministicDecides I Acc {z | E n z = true} →
          (1 + π / (3 * arccos ((1 + 2 * √2) / 4)) - ε) * n < c.innerSize := by
  obtain ⟨hfree, hK, hdense⟩ := frontierHypotheses_of_isSumsetExtractor hE hk hδ hδ₀
  exact eventually_gaussian_sub_mul_lt_innerSize_of_nondeterministicDecides.{u, v}
    hfree hK hdense hε

/-- **Conditional `(4.56249 - ε) n` frontier lower bound for nondeterministic circuits of fan-in two
from a sumset-extractor family**, uniformly in the number `k'` of witness inputs. -/
theorem eventually_456249_div_100000_sub_mul_lt_innerSize_nondeterministic_of_isSumsetExtractor
    [AddGroup U] [Finite U] [Nontrivial U] {E : ∀ n, (Fin n → U) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k' : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k') 1), c.FanInAtMost 2 →
        c.NondeterministicDecides I Acc {z | E n z = true} →
          (456249 / 100000 - ε) * n < c.innerSize := by
  obtain ⟨hfree, hK, hdense⟩ := frontierHypotheses_of_isSumsetExtractor hE hk hδ hδ₀
  exact eventually_456249_div_100000_sub_mul_lt_innerSize_of_nondeterministicDecides.{u, v}
    hfree hK hdense hε

/-- **Conditional Gaussian frontier lower bound with aggregate gates at ordinary fan-in two from a
sumset-extractor family.** -/
theorem eventually_gaussian_sub_mul_lt_card_of_aggregates_of_isSumsetExtractor
    [AddGroup U] [Finite U] [Nontrivial U] {E : ∀ n, (Fin n → U) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1) (special : Fin c.size → Prop) [DecidablePred special] (T : Type w)
      [CommMonoid T] [Finite T],
        (∀ g, ¬special g → σ.Arity (c.program.lines g).op ≤ 2) →
        (∀ g, special g → Aggregates (I (c.program.lines g).op) T) →
        Nat.card {g // special g} * Real.log (Nat.card T) ≤ β n →
        c.Decides I Acc {z | E n z = true} →
          (1 + π / (3 * arccos ((1 + 2 * √2) / 4)) - ε) * n <
            (c.program.innerGates.filter fun g => ¬special g).card := by
  obtain ⟨hfree, hK, hdense⟩ := frontierHypotheses_of_isSumsetExtractor hE hk hδ hδ₀
  exact eventually_gaussian_sub_mul_lt_card_of_aggregates.{u, v, w} hfree hK hdense hβ hε

/-- **Conditional `(4.56249 - ε) n` frontier lower bound with aggregate gates at ordinary fan-in two
from a sumset-extractor family.** -/
theorem eventually_456249_div_100000_sub_mul_lt_card_of_aggregates_of_isSumsetExtractor
    [AddGroup U] [Finite U] [Nontrivial U] {E : ∀ n, (Fin n → U) → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ n in atTop, IsSumsetExtractor (E n) (k n) (δ n))
    (hk : k =o[atTop] fun n : ℕ => (n : ℝ))
    (hδ : ∀ᶠ n in atTop, δ n ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1) (special : Fin c.size → Prop) [DecidablePred special] (T : Type w)
      [CommMonoid T] [Finite T],
        (∀ g, ¬special g → σ.Arity (c.program.lines g).op ≤ 2) →
        (∀ g, special g → Aggregates (I (c.program.lines g).op) T) →
        Nat.card {g // special g} * Real.log (Nat.card T) ≤ β n →
        c.Decides I Acc {z | E n z = true} →
          (456249 / 100000 - ε) * n <
            (c.program.innerGates.filter fun g => ¬special g).card := by
  obtain ⟨hfree, hK, hdense⟩ := frontierHypotheses_of_isSumsetExtractor hE hk hδ hδ₀
  exact eventually_456249_div_100000_sub_mul_lt_card_of_aggregates.{u, v, w} hfree hK hdense hβ hε

end Cslib.Circuits.Frontier
