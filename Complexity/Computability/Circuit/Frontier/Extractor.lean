/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Extractor.BalancePad
public import Complexity.Computability.Circuit.Frontier.Extractor.Distributional
public import Complexity.Computability.Circuit.Frontier.Extractor.LowerBounds
public import Complexity.Computability.Circuit.Frontier.Extractor.Sumset
public import Complexity.Init

/-!
# Sumset extractors, sumset dispersers, and frontier circuit lower bounds

This umbrella module re-exports the two-source sumset extractor and frontier circuit lower bound
development split across:

* `Complexity.Computability.Circuit.Frontier.Extractor.Sumset`: zero-padding of partial assignments
  (`zeroPad`), `SumsetDisperser`, `SumsetBias`, rectangle-freeness and rectangle-bias bridges, and
  implication to `IsAffineDisperser`;
* `Complexity.Computability.Circuit.Frontier.Extractor.Distributional`: distributional
  `(k, δ)`-sumset extractors (`IsSumsetExtractor`), the Chor–Goldreich flat-source characterization
  (`isSumsetExtractor_iff_sumsetBias_two_pow`), and asymptotic log-threshold and density lemmas;
* `Complexity.Computability.Circuit.Frontier.Extractor.LowerBounds`: conditional Gaussian and
  bounded-fan-in frontier average-case and worst-case circuit lower bounds from sumset-extractor
  families (`frontierHypotheses_of_isSumsetExtractor`,
  `eventually_agreement_le_of_isSumsetExtractor`,
  `eventually_456249_div_100000_sub_mul_lt_size_of_isSumsetExtractor`, …);
* `Complexity.Computability.Circuit.Frontier.Extractor.BalancePad`: one-bit balanced padding
  (`balancePad`, `balancePadFamily`) and worst-case frontier hypotheses from sumset-disperser
  families without a quantitative bias assumption (`frontierHypotheses_balancePadFamily`).

## Main definitions

* `Cslib.Circuits.Frontier.zeroPad`, `Cslib.Circuits.Frontier.SumsetDisperser`,
  `Cslib.Circuits.Frontier.SumsetBias`: zero-extension, sumset dispersion, and sumset bias.
* `Cslib.Circuits.Frontier.IsSumsetExtractor`: distributional `(k, δ)`-sumset extractor.
* `Cslib.Circuits.Frontier.balancePad`, `Cslib.Circuits.Frontier.balancePadFamily`: one-bit
  balanced padding.

## Main results

* `Cslib.Circuits.Frontier.SumsetDisperser.rectangleFree`,
  `Cslib.Circuits.Frontier.SumsetBias.rectangleBias`,
  `Cslib.Circuits.Frontier.IsSumsetExtractor.rectangleBias_ceil`: bridges to frontier rectangle
  hypotheses.
* `Cslib.Circuits.Frontier.isSumsetExtractor_iff_sumsetBias_two_pow`: flat-source equivalence for
  Boolean sumset extractors.
* `Cslib.Circuits.Frontier.eventually_agreement_le_of_isSumsetExtractor`,
  `Cslib.Circuits.Frontier.eventually_456249_div_100000_sub_mul_lt_size_of_isSumsetExtractor`:
  conditional frontier average-case and worst-case circuit lower bounds.
* `Cslib.Circuits.Frontier.frontierHypotheses_balancePadFamily`: worst-case frontier hypotheses via
  one-bit balanced padding.

## References

* [B. Chor and O. Goldreich, *Unbiased bits from sources of weak randomness and probabilistic
  communication complexity*][ChorGoldreich1988]
* [E. Chattopadhyay and J.-J. Liao, *Extractors for Sum of Two Sources*][ChattopadhyayLiao2022]
* [E. Chattopadhyay and D. Zuckerman, *Explicit Two-Source Extractors and Resilient
  Functions*][ChattopadhyayZuckerman2019]
* [X. Li, *Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More*][Li2023]
* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
* [S. Schlesinger, *Frontier circuit lower bounds and two-source sumset extractors in
  Complexitylib*][Schlesinger2026FrontierExtractor]
-/

@[expose] public section
