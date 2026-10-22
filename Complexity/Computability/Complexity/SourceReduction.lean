/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Frontier.SourceReduction
public import Complexity.Computability.Complexity.FrontierExtractor
public import Complexity.Foundations.Data.BitString.List.Operations

/-!
# Uniform `P` evaluators and conditional `(4.56249 - ε) N` lower bounds for the XOR source reduction

This module connects the combinatorial and fourth-moment source-reduction pipeline of
`Complexity.Computability.Circuit.Frontier.SourceReduction` to uniform polynomial-time languages in
`Cslib.Complexity.P encBits`:

1. **Uniform polynomial-time evaluation of `strictMajority` and `parity`
   (`computableTidilyInPolyTime_strictMajority`, `ofSlices_strictMajority_mem_P`,
   `computableTidilyInPolyTime_parity`, `ofSlices_parity_mem_P`):**
   On any bit string `x : BitString n`, `strictMajority n x` agrees with
   `BitString.listStrictMajority (List.ofFn x)` (`listStrictMajority_ofFn`), and `parity n x` agrees
   with `(List.ofFn x).foldl Bool.xor false` (`foldl_xor_ofFn_eq_parity`). Consequently, both
   `Language.ofSlices strictMajority` and `Language.ofSlices parity` belong unconditionally to
   `Complexity.P encBits`.
2. **Uniform composition with polynomial-time source reductions
   (`computableTidilyInPolyTime_strictMajority_comp`, `ofSlices_strictMajority_comp_mem_P`):**
   If a source-reduction family `reduce : ∀ N, BitString N → BitString (D N)` is computed on lists
   by a polynomial-time word map `reduceEval : List Bool → List Bool`, then the composed Boolean
   family `fun N z => strictMajority (D N) (reduce N z)` defines a language in
   `Complexity.P encBits` via `Language.ofSlices`, with a concrete decider built from
   `reduceEval` and `BitString.listStrictMajority`.
3. **Conditional `(4.56249 - ε) N` circuit lower bounds in `P` from the XOR source reduction
   (`exists_mem_P_eventually_lt_size_of_strictMajority_parity_fibers`,
   `exists_mem_P_eventually_lt_size_of_affineSourceReduction`):**
   *Assuming* a polynomial-time source reduction `reduce` (or `affineSourceReduction` at scale
   `b_N ≥ 5`) whose fibers satisfy the parity-bias hypotheses at threshold `K_N > 0` with
   `log K_N = o(N)`, the `35 / 72 < 1 / 2` sumset bias proved in
   `Complexity.Computability.Circuit.Frontier.SourceReduction` yields a language in
   `Complexity.P encBits` requiring more than `(456249 / 100000 - ε) N` gates over
   `fullSignature 2 Bool`, with `(4.56249 - ε) N` average-case agreement on `Language.ofSlices E`
   at most `1 / 2 + 35 / 72 + exp (-γ N)`. As in
   `Complexity.Computability.Complexity.FrontierExtractor`, the correlation-breaker and
   somewhere-sampler hypotheses are explicit assumptions; no unconditional sumset extractor is
   constructed here.

## Main results

* `Cslib.Circuits.Frontier.listStrictMajority_ofFn`,
  `Cslib.Circuits.Frontier.computableTidilyInPolyTime_strictMajority`,
  `Cslib.Circuits.Frontier.ofSlices_strictMajority_mem_P`: `strictMajority` is in `P encBits`.
* `Cslib.Circuits.Frontier.foldl_xor_ofFn_eq_parity`,
  `Cslib.Circuits.Frontier.computableTidilyInPolyTime_parity`,
  `Cslib.Circuits.Frontier.ofSlices_parity_mem_P`: `parity` is in `P encBits`.
* `Cslib.Circuits.Frontier.computableTidilyInPolyTime_strictMajority_comp`,
  `Cslib.Circuits.Frontier.ofSlices_strictMajority_comp_mem_P`: composition of `strictMajority` with
  any polynomial-time source reduction is in `P encBits`.
* `Cslib.Circuits.Frontier.exists_mem_P_eventually_lt_size_of_strictMajority_parity_fibers`,
  `Cslib.Circuits.Frontier.exists_mem_P_eventually_agreement_le_of_strictMajority_parity_fibers`:
  conditional `(4.56249 - ε) N` worst-case and average-case lower bounds in `P` from parity-biased
  fibers.
* `Cslib.Circuits.Frontier.exists_mem_P_eventually_lt_size_of_affineSourceReduction`: conditional
  `(4.56249 - ε) N` worst-case lower bound in `P` from `affineSourceReduction` at scale `b_N ≥ 5`.

## References

* [E. Chattopadhyay and J.-J. Liao, *Extractors for Sum of Two Sources*][ChattopadhyayLiao2022]
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Cslib.BitString Cslib.Complexity Filter Asymptotics Real Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-! ### Uniform polynomial-time evaluation of `strictMajority` and `parity` -/

/-- On the list representation `List.ofFn x` of `x : BitString n`, `listStrictMajority` agrees
with `strictMajority n x`. -/
theorem listStrictMajority_ofFn {n : ℕ} (x : BitString n) :
    listStrictMajority (List.ofFn x) = strictMajority n x := by
  have hmap : List.ofFn x = (List.finRange n).map x := List.ofFn_eq_map
  rw [hmap, listStrictMajority_map (List.finRange n) (List.nodup_finRange n) x,
    strictMajority_eq_strictMajorityOn]
  congr 1
  ext i
  simp

/-- On any list `x : List Bool`, `strictMajority x.length (BitString.ofList x.length x)` equals
`listStrictMajority x`. -/
theorem strictMajority_ofList (x : List Bool) :
    strictMajority x.length (BitString.ofList x.length x) = listStrictMajority x := by
  rw [← listStrictMajority_ofFn, ofFn_ofList rfl]

/-- **Strict majority is tidily computable in polynomial time.** -/
theorem computableTidilyInPolyTime_strictMajority :
    ComputableTidilyInPolyTime
      (fun x : List Bool => strictMajority x.length (BitString.ofList x.length x))
      encBits encBool := by
  convert bitsStrictMajority using 1
  funext x
  exact strictMajority_ofList x

/-- **`Language.ofSlices strictMajority` belongs unconditionally to `P encBits`.** -/
theorem ofSlices_strictMajority_mem_P :
    (Language.ofSlices strictMajority : Set (List Bool)) ∈ P encBits :=
  ofSlices_mem_P computableTidilyInPolyTime_strictMajority

/-- Folding `Bool.xor` over `List.ofFn x` computes `parity n x`. -/
theorem foldl_xor_ofFn_eq_parity {n : ℕ} (x : BitString n) :
    (List.ofFn x).foldl Bool.xor false = parity n x := by
  have hsum : (List.ofFn x).foldl Bool.xor false = (List.ofFn x).sum := by
    simp [List.sum_eq_foldl, Bool.add_eq_xor, Bool.zero_eq_false]
  rw [hsum, List.sum_ofFn, parity, parityOn_eq_sum]

/-- On any list `x : List Bool`, `parity x.length (BitString.ofList x.length x)` equals
`x.foldl Bool.xor false`. -/
theorem parity_ofList (x : List Bool) :
    parity x.length (BitString.ofList x.length x) = x.foldl Bool.xor false := by
  rw [← foldl_xor_ofFn_eq_parity, ofFn_ofList rfl]

/-- **Parity is tidily computable in polynomial time.** -/
theorem computableTidilyInPolyTime_parity :
    ComputableTidilyInPolyTime
      (fun x : List Bool => parity x.length (BitString.ofList x.length x))
      encBits encBool := by
  have h := bitsFoldlWithInput Bool.xor (id' (encIn := encBits)) (const false)
  convert h using 1
  funext x
  exact parity_ofList x

/-- **`Language.ofSlices parity` belongs unconditionally to `P encBits`.** -/
theorem ofSlices_parity_mem_P :
    (Language.ofSlices parity : Set (List Bool)) ∈ P encBits :=
  ofSlices_mem_P computableTidilyInPolyTime_parity

/-! ### Uniform polynomial-time composition of `strictMajority` with a source reduction -/

/-- If a source reduction `reduce : ∀ N, BitString N → BitString (D N)` is computed on bit lists by
`reduceEval : List Bool → List Bool` in polynomial time, then the composed Boolean family
`fun N z => strictMajority (D N) (reduce N z)` is tidily computable in polynomial time. -/
theorem computableTidilyInPolyTime_strictMajority_comp
    {D : ℕ → ℕ} {reduce : ∀ N, BitString N → BitString (D N)}
    {reduceEval : List Bool → List Bool}
    (hReduce : ComputableTidilyInPolyTime reduceEval encBits encBits)
    (hEq : ∀ x : List Bool,
      List.ofFn (reduce x.length (BitString.ofList x.length x)) = reduceEval x) :
    ComputableTidilyInPolyTime
      (fun x : List Bool =>
        strictMajority (D x.length) (reduce x.length (BitString.ofList x.length x)))
      encBits encBool := by
  have h := bitsStrictMajority.comp hReduce
  convert h using 1
  funext x
  rw [Function.comp_apply, ← hEq x, listStrictMajority_ofFn]

/-- If `reduce : ∀ N, BitString N → BitString (D N)` is computed on bit lists by a polynomial-time
word map `reduceEval`, then `Language.ofSlices (fun N z => strictMajority (D N) (reduce N z))`
belongs to `P encBits`. -/
theorem ofSlices_strictMajority_comp_mem_P
    {D : ℕ → ℕ} {reduce : ∀ N, BitString N → BitString (D N)}
    {reduceEval : List Bool → List Bool}
    (hReduce : ComputableTidilyInPolyTime reduceEval encBits encBits)
    (hEq : ∀ x : List Bool,
      List.ofFn (reduce x.length (BitString.ofList x.length x)) = reduceEval x) :
    (Language.ofSlices (fun N z => strictMajority (D N) (reduce N z)) : Set (List Bool)) ∈
      P encBits :=
  ofSlices_mem_P (computableTidilyInPolyTime_strictMajority_comp hReduce hEq)

/-! ### Conditional `(4.56249 - ε) N` circuit lower bounds in `P` from the source reduction -/

/-- **Conditional: a language in `P` with `B₂` circuit complexity `> (4.56249 - ε) N` from a
polynomial-time source reduction with parity-biased second-source fibers.** The reduction family and
its fiber property are hypotheses; none is constructed here. Because
`strictMajority_sumsetBias_of_parity_fibers` establishes `SumsetBias ... K_N (35 / 72)` with
`35 / 72 < 1 / 2`, the language
`L = Language.ofSlices (fun N z => strictMajority (D N) (reduce N z))` lies in `P encBits` and
requires more than `(456249 / 100000 - ε) N` gates over `fullSignature 2 Bool` whenever
`log K_N = o(N)`. -/
theorem exists_mem_P_eventually_lt_size_of_strictMajority_parity_fibers
    {D K : ℕ → ℕ} {δ : ℕ → ℝ}
    {reduce : ∀ N, BitString N → BitString (D N)}
    {reduceEval : List Bool → List Bool}
    (hReduce : ComputableTidilyInPolyTime reduceEval encBits encBits)
    (hEq : ∀ x : List Bool,
      List.ofFn (reduce x.length (BitString.ofList x.length x)) = reduceEval x)
    (hKpos : ∀ᶠ N in atTop, 0 < K N)
    (hδ : ∀ᶠ N in atTop, 0 ≤ δ N)
    (hFibers : ∀ᶠ N in atTop, ∀ P Q : Finset (BitString N), K N ≤ P.card → K N ≤ Q.card →
      ∃ Good ⊆ Q, (1 / 2 : ℝ) * Q.card ≤ Good.card ∧
        ∀ y ∈ Good, ∃ (m : ℕ) (good : Fin m ↪ Fin (D N)), 0 < m ∧
          100 * (m : ℝ) ^ 2 * δ N ≤ 1 ∧
          ParityBiasBound P (fun _ => 1 / (P.card : ℝ))
            (fun x i => if reduce N (x + y) (good i) then 1 else -1) (δ N) ∧
          ((D N - m : ℕ) : ℝ) ≤ Real.sqrt (m : ℝ) / 8)
    (hK : (fun N => Real.log (K N)) =o[atTop] fun N : ℕ => (N : ℝ)) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ P encBits ∧
      ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N in atTop, ∀ C : Circuit (fullSignature 2 Bool) N 1,
        C.Computes fullInterpretation (single (L.slice N)) →
          (456249 / 100000 - ε) * (N : ℝ) < C.size := by
  let E : ∀ N, BitString N → Bool := fun N z => strictMajority (D N) (reduce N z)
  have hBias : ∀ᶠ N in atTop, SumsetBias {z | E N z = true} (K N) (35 / 72) := by
    filter_upwards [hKpos, hδ, hFibers] with N hKN hδN hFibN
    exact strictMajority_sumsetBias_of_parity_fibers (reduce N) hKN hδN hFibN
  have hFree : ∀ᶠ N in atTop, RectangleFree {z | E N z = true} (K N) := by
    filter_upwards [hBias, hKpos] with N hBiasN hKN
    exact hBiasN.rectangleFree hKN (by norm_num)
  have hDense := isLittleO_sub_log_ncard_of_sumsetBias (b := fun _ => 35 / 72) (b₀ := 35 / 72)
    hBias hK (Eventually.of_forall fun _ => le_rfl) (by norm_num)
  refine ⟨Language.ofSlices E, ofSlices_strictMajority_comp_mem_P hReduce hEq, fun hε => ?_⟩
  filter_upwards [eventually_456249_div_100000_sub_mul_lt_innerSize.{0, 0} hFree hK hDense hε]
    with N hN C hC
  rw [Language.slice_ofSlices] at hC
  exact (hN (fullSignature 2 Bool) fullInterpretation {true} C C.fanInAtMost_fullSignature
    (hC.decides {true})).trans_le (by exact_mod_cast C.innerSize_le_size)

/-- **Conditional: a language in `P` with `(4.56249 - ε) N` average-case correlation bound
`1 / 2 + 35 / 72 + exp (-γ N)` from a polynomial-time source reduction with parity-biased
fibers.** -/
theorem exists_mem_P_eventually_agreement_le_of_strictMajority_parity_fibers
    {D K : ℕ → ℕ} {δ : ℕ → ℝ}
    {reduce : ∀ N, BitString N → BitString (D N)}
    {reduceEval : List Bool → List Bool}
    (hReduce : ComputableTidilyInPolyTime reduceEval encBits encBits)
    (hEq : ∀ x : List Bool,
      List.ofFn (reduce x.length (BitString.ofList x.length x)) = reduceEval x)
    (hKpos : ∀ᶠ N in atTop, 0 < K N)
    (hδ : ∀ᶠ N in atTop, 0 ≤ δ N)
    (hFibers : ∀ᶠ N in atTop, ∀ P Q : Finset (BitString N), K N ≤ P.card → K N ≤ Q.card →
      ∃ Good ⊆ Q, (1 / 2 : ℝ) * Q.card ≤ Good.card ∧
        ∀ y ∈ Good, ∃ (m : ℕ) (good : Fin m ↪ Fin (D N)), 0 < m ∧
          100 * (m : ℝ) ^ 2 * δ N ≤ 1 ∧
          ParityBiasBound P (fun _ => 1 / (P.card : ℝ))
            (fun x i => if reduce N (x + y) (good i) then 1 else -1) (δ N) ∧
          ((D N - m : ℕ) : ℝ) ≤ Real.sqrt (m : ℝ) / 8)
    (hK : (fun N => Real.log (K N)) =o[atTop] fun N : ℕ => (N : ℝ)) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ P encBits ∧
      ∀ {ε : ℝ}, 0 < ε → ∃ γ > 0, ∀ᶠ N in atTop, ∀ C : Circuit (fullSignature 2 Bool) N 1,
        (C.size : ℝ) ≤ (456249 / 100000 - ε) * N →
          agreement {z | L.slice N z = true} {x | C.eval fullInterpretation x 0 = true} ≤
            1 / 2 + 35 / 72 + Real.exp (-(γ * N)) := by
  let E : ∀ N, BitString N → Bool := fun N z => strictMajority (D N) (reduce N z)
  have hRect : ∀ᶠ N in atTop, RectangleBias {z | E N z = true} (K N) (35 / 72) := by
    filter_upwards [hKpos, hδ, hFibers] with N hKN hδN hFibN
    exact (strictMajority_sumsetBias_of_parity_fibers (reduce N) hKN hδN hFibN).rectangleBias
  refine ⟨Language.ofSlices E, ofSlices_strictMajority_comp_mem_P hReduce hEq, fun {ε} hε => ?_⟩
  obtain ⟨γ, hγ, H⟩ := averageCaseBound_gaussian.{0, 0} ε hε
  refine ⟨γ, hγ, (H Bool (fun N => {z | E N z = true}) K (fun _ => 35 / 72) hRect hK).mono
    fun N hN C hsize => ?_⟩
  have hinner : (C.innerSize : ℝ) ≤ (1 + π / (3 * arccos ((1 + 2 * √2) / 4)) - ε) * N := by
    calc (C.innerSize : ℝ) ≤ C.size := by exact_mod_cast C.innerSize_le_size
      _ ≤ (456249 / 100000 - ε) * N := hsize
      _ ≤ (1 + π / (3 * arccos ((1 + 2 * √2) / 4)) - ε) * N :=
        mul_le_mul_of_nonneg_right (by linarith [Gaussian.circuitCoefficient_ge_456249])
          (Nat.cast_nonneg N)
  simpa only [Language.slice_ofSlices, Set.mem_singleton_iff] using
    hN (fullSignature 2 Bool) fullInterpretation {true} C C.fanInAtMost_fullSignature hinner

/-- **Conditional: a language in `P` with `B₂` circuit complexity `> (4.56249 - ε) N` from
`affineSourceReduction` at scale `b_N ≥ 5`.** Assuming a family of correlation breakers `cb`,
somewhere samplers `sampler`, and advice tables `advice` whose `affineSourceReduction` is
polynomial-time computable on bit lists and satisfies the hypotheses of
`sumsetBias_strictMajority_affineSourceReduction` at threshold `K_N > 0` with `log K_N = o(N)`, the
composed language `Language.ofSlices (fun N z => strictMajority _ (affineSourceReduction ... z))`
belongs to `P encBits` and requires more than `(456249 / 100000 - ε) N` gates over `B₂`. -/
theorem exists_mem_P_eventually_lt_size_of_affineSourceReduction
    {Seed Advice : ℕ → Type*} [∀ N, Fintype (Seed N)]
    {b c K : ℕ → ℕ}
    (cb : ∀ N, BitString N → Seed N → Advice N → Bool)
    (sampler : ∀ N, BitString N →
      Fin (sourceReductionOuterCount (b N)) → Fin (sourceReductionCandidateCount (c N)) → Seed N)
    (advice : ∀ N,
      Fin (sourceReductionOuterCount (b N)) → Fin (sourceReductionCandidateCount (c N)) → Advice N)
    {reduceEval : List Bool → List Bool}
    (hReduce : ComputableTidilyInPolyTime reduceEval encBits encBits)
    (hEq : ∀ x : List Bool,
      List.ofFn (affineSourceReduction (cb x.length) (sampler x.length) (advice x.length)
        (BitString.ofList x.length x)) = reduceEval x)
    (hb : ∀ᶠ N in atTop, 5 ≤ b N)
    (hKpos : ∀ᶠ N in atTop, 0 < K N)
    (hSampler : ∀ᶠ N in atTop,
      SomewhereSampler (sampler N) (K N) (sourceReductionSamplerError (b N)) (1 / 2))
    (bad : ∀ N, Finset (BitString N) → Finset (BitString N) →
      Finset (Fin (sourceReductionOuterCount (b N))) →
      Fin (sourceReductionCandidateCount (c N)) → Finset (Seed N))
    (hBadCard : ∀ᶠ N in atTop, ∀ P Q : Finset (BitString N), K N ≤ P.card → K N ≤ Q.card →
      ∀ U ∈ parityTests (Fin (sourceReductionOuterCount (b N))) 4,
      ∀ z : Fin (sourceReductionCandidateCount (c N)),
        ((bad N P Q U z).card : ℝ) ≤
          (((2 : ℝ) ^ sourceReductionTarget (b N) (c N))⁻¹ /
            sourceReductionBadThreshold (b N)) * Fintype.card (Seed N))
    (hEstimate : ∀ᶠ N in atTop, ∀ P Q : Finset (BitString N), K N ≤ P.card → K N ≤ Q.card →
      ∀ U ∈ parityTests (Fin (sourceReductionOuterCount (b N))) 4,
      ∃ j ∈ U, ∀ z : Fin (sourceReductionCandidateCount (c N)), ∀ y ∈ Q,
        sampler N y j z ∉ bad N P Q U z →
          |weightedMean P (fun _ => 1 / (P.card : ℝ)) (fun x =>
            ∏ i ∈ U, ∏ r : Fin (sourceReductionCandidateCount (c N)),
              if cb N (x + y) (sampler N (x + y) i r) (advice N i r) then (1 : ℝ) else -1)| ≤
            sourceReductionParityBias (b N))
    (hK : (fun N => Real.log (K N)) =o[atTop] fun N : ℕ => (N : ℝ)) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ P encBits ∧
      ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N in atTop, ∀ C : Circuit (fullSignature 2 Bool) N 1,
        C.Computes fullInterpretation (single (L.slice N)) →
          (456249 / 100000 - ε) * (N : ℝ) < C.size := by
  let E : ∀ N, BitString N → Bool := fun N z =>
    strictMajority (sourceReductionOuterCount (b N))
      (affineSourceReduction (cb N) (sampler N) (advice N) z)
  have hBias : ∀ᶠ N in atTop, SumsetBias {z | E N z = true} (K N) (35 / 72) := by
    filter_upwards [hb, hKpos, hSampler, hBadCard, hEstimate] with N hbN hKN hSN hBCN hEstN
    exact sumsetBias_strictMajority_affineSourceReduction hbN hKN (cb N) (sampler N) (advice N)
      hSN (bad N) hBCN hEstN
  have hFree : ∀ᶠ N in atTop, RectangleFree {z | E N z = true} (K N) := by
    filter_upwards [hBias, hKpos] with N hBiasN hKN
    exact hBiasN.rectangleFree hKN (by norm_num)
  have hDense := isLittleO_sub_log_ncard_of_sumsetBias (b := fun _ => 35 / 72) (b₀ := 35 / 72)
    hBias hK (Eventually.of_forall fun _ => le_rfl) (by norm_num)
  refine ⟨Language.ofSlices E, ofSlices_strictMajority_comp_mem_P hReduce hEq, fun hε => ?_⟩
  filter_upwards [eventually_456249_div_100000_sub_mul_lt_innerSize.{0, 0} hFree hK hDense hε]
    with N hN C hC
  rw [Language.slice_ofSlices] at hC
  exact (hN (fullSignature 2 Bool) fullInterpretation {true} C C.fanInAtMost_fullSignature
    (hC.decides {true})).trans_le (by exact_mod_cast C.innerSize_le_size)

end Cslib.Circuits.Frontier
