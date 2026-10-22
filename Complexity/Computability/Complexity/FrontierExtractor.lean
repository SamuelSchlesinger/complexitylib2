/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.AffineDisperser
public import Complexity.Computability.Circuit.Boolean.PolynomialTime
public import Complexity.Computability.Circuit.Frontier.Extractor
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Cslib.Computability.Languages.Slice
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Conditional `(4.56249 - ε) N` circuit lower bounds in `P` from sumset extractors

This module does **not** construct any explicit sumset extractor or disperser. Its circuit lower
bounds for languages in `P` are all **conditional**: each takes a polynomial-time sumset-extractor
(or sumset-disperser) family with the stated parameters as a hypothesis, and no such family is
constructed in this library.

This module connects the frontier sumset-extractor lower bounds of
`Complexity.Computability.Circuit.Frontier.Extractor` to uniform polynomial-time languages in
`Cslib.Complexity.P encBits`, in the exact model of
`Complexity.Computability.Complexity.AffineDisperser`
(`Cslib.AffineDisperser.exists_mem_P_eventually_le_size`):

1. **Uniformity bridge (`ofSlices_mem_P_iff`, `ofSlices_balancePadFamily_mem_P`):**
   For any Boolean family `f : ∀ N, BitString N → Bool`, the language `Language.ofSlices f` belongs
   to `Complexity.P encBits` if and only if the list evaluator
   `fun x : List Bool => f x.length (BitString.ofList x.length x)` is tidily computable in
   polynomial time (`ComputableTidilyInPolyTime`). Multi-bit polynomial-time evaluators projected to
   their first output bit (`ofSlices_mem_P_of_headD`) and one-bit balanced padding
   (`ofSlices_balancePadFamily_mem_P`) preserve membership in `Complexity.P encBits`.
2. **Polylogarithmic min-entropy thresholds (`isLittleO_rpow_log_id`):**
   Every polylogarithmic min-entropy threshold `k_N = O((log N)^C)` (as in
   [Chattopadhyay and Liao][ChattopadhyayLiao2022], where `k_N = (log N)^C` for a constant `C > 3`,
   and [Li][Li2023], where `k_N = O(log N)`) satisfies `k_N = o(N)`.
3. **Unification with Mishra–Santhanam (`IsSumsetExtractor.seven_mul_le_two_mul_size_add`):**
   Because every `(k, δ)`-sumset extractor (`δ < 1 / 2`, `k ≤ d`) is an affine disperser for
   dimension `d` (`IsSumsetExtractor.isAffineDisperser`), every circuit over `fullSignature 2 Bool`
   computing it satisfies *both* Mishra–Santhanam's finite gate-elimination bound
   `7 N ≤ 2 |C| + 14 d` at every input length `N` *and* the asymptotic `(4.56249 - ε) N` Gaussian
   frontier bound.
4. **Conditional `(4.56249 - ε) N` average-case and worst-case lower bounds in `P`:**
   *Assuming* a polynomial-time Boolean sumset-extractor family `E` with sublinear (e.g.
   polylogarithmic) min-entropy `k_N = o(N)` and error `δ_N`, the language
   `L = Language.ofSlices E` lies in `Complexity.P encBits` and satisfies:
   * for every `ε > 0`, some `γ > 0` bounds the agreement of every `B₂` circuit of size at most
     `(456249 / 100000 - ε) N` with `L.slice N` by `1 / 2 + δ_N + exp (-γ N)`
     (`exists_mem_P_eventually_agreement_le_of_isSumsetExtractor`,
     `exists_mem_P_eventually_agreement_le_of_polylog_sumsetExtractor`);
   * when `δ_N ≤ δ₀ < 1 / 2` eventually, every `B₂` circuit computing `single (L.slice N)` has size
     strictly greater than `(456249 / 100000 - ε) N` for all large `N`
     (`exists_mem_P_eventually_lt_size_of_isSumsetExtractor`), and in particular strictly greater
     than `4.56 N`
     (`exists_mem_P_eventually_456_div_100_lt_size_of_isSumsetExtractor`). Given such a family,
     this would strengthen the unconditional `3.5 N - o(N)` bound of
     `Cslib.AffineDisperser.exists_mem_P_eventually_le_size`; no such family is constructed here;
   * via `balancePadFamily`, a hypothesised polynomial-time qualitative `SumsetDisperser` family
     with `log K_N = o(N)` yields a language in `Complexity.P encBits` requiring more than
     `(456249 / 100000 - ε) N` gates over `B₂`
     (`exists_mem_P_eventually_lt_size_of_sumsetDisperser`).

## Main results

* `Cslib.Circuits.Frontier.ofSlices_mem_P_iff`: characterization of
  `Language.ofSlices f ∈ P encBits`.
* `Cslib.Circuits.Frontier.ofSlices_balancePadFamily_mem_P`: closure of `P encBits` under
  `balancePadFamily`.
* `Cslib.Circuits.Frontier.isLittleO_rpow_log_id`: `(log N)^C = o(N)`.
* `Cslib.Circuits.Frontier.IsSumsetExtractor.seven_mul_le_two_mul_size_add`: Mishra–Santhanam's
  `7 N ≤ 2 |C| + 14 d` bound for sumset extractors.
* `Cslib.Circuits.Frontier.exists_mem_P_eventually_agreement_le_of_isSumsetExtractor`,
  `exists_mem_P_eventually_agreement_le_of_polylog_sumsetExtractor`: conditional
  `(4.56249 - ε) N` average-case circuit lower bounds in `P`, assuming a polynomial-time
  sumset-extractor family.
* `Cslib.Circuits.Frontier.exists_mem_P_eventually_lt_size_of_isSumsetExtractor`,
  `exists_mem_P_eventually_456_div_100_lt_size_of_isSumsetExtractor`: conditional
  `(4.56249 - ε) N` and `4.56 N` worst-case circuit lower bounds in `P` over `fullSignature 2 Bool`,
  assuming a polynomial-time sumset-extractor family.
* `Cslib.Circuits.Frontier.exists_mem_P_eventually_lt_size_of_sumsetDisperser`: conditional
  `(4.56249 - ε) N` worst-case circuit lower bound in `P`, assuming a polynomial-time qualitative
  sumset-disperser family, via `balancePadFamily`.

## References

* [E. Chattopadhyay and J.-J. Liao, *Extractors for Sum of Two Sources*][ChattopadhyayLiao2022]
* [X. Li, *Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More*][Li2023]
* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
* [S. Schlesinger, *Frontier circuit lower bounds and two-source sumset extractors in
  Complexitylib*][Schlesinger2026FrontierExtractor]
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Cslib.BitString Cslib.Complexity Filter Asymptotics Real Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-! ### Uniformity bridge for `Language.ofSlices` and `balancePadFamily` -/

/-- For any Boolean family `f : ∀ N, BitString N → Bool`, `Language.ofSlices f` as a set of bit
lists is `{x | f x.length (BitString.ofList x.length x) = true}`. -/
theorem ofSlices_eq_setOf_ofList (f : ∀ N, BitString N → Bool) :
    (Language.ofSlices f : Set (List Bool)) =
      {x : List Bool | f x.length (BitString.ofList x.length x) = true} :=
  Set.ext fun x => mem_ofSlices_iff f x

/-- **`Language.ofSlices f` is in `P`** if and only if its list evaluator
`fun x => f x.length (BitString.ofList x.length x)` is tidily computable in polynomial time. -/
theorem ofSlices_mem_P_iff {f : ∀ N, BitString N → Bool} :
    (Language.ofSlices f : Set (List Bool)) ∈ P encBits ↔
      ComputableTidilyInPolyTime
        (fun x : List Bool => f x.length (BitString.ofList x.length x)) encBits encBool := by
  constructor
  · rintro ⟨g, hg, hiff⟩
    have heq : (fun x : List Bool => f x.length (BitString.ofList x.length x)) = g := by
      funext x
      exact Bool.eq_iff_iff.mpr ((mem_ofSlices_iff f x).symm.trans (hiff x))
    exact heq ▸ hg
  · exact ofSlices_mem_P_of_computableInPolyTime

/-- If `fun x => f x.length (BitString.ofList x.length x)` is tidily computable in polynomial time,
then `Language.ofSlices f` belongs to `P encBits`. -/
theorem ofSlices_mem_P {f : ∀ N, BitString N → Bool}
    (hf : ComputableTidilyInPolyTime
      (fun x : List Bool => f x.length (BitString.ofList x.length x)) encBits encBool) :
    (Language.ofSlices f : Set (List Bool)) ∈ P encBits :=
  ofSlices_mem_P_of_computableInPolyTime hf

/-- **Projection of a multi-bit polynomial-time evaluator to its first output bit.** If a multi-bit
extractor is computed on bit lists by `eval : List Bool → List Bool` in polynomial time and `f N`
is its first output bit (with fallback `false`), then `Language.ofSlices f ∈ P encBits`. -/
theorem ofSlices_mem_P_of_headD {f : ∀ N, BitString N → Bool} {eval : List Bool → List Bool}
    (heval : ComputableTidilyInPolyTime eval encBits encBits)
    (hbit : ∀ x : List Bool, f x.length (BitString.ofList x.length x) = (eval x).headD false) :
    (Language.ofSlices f : Set (List Bool)) ∈ P encBits := by
  refine ofSlices_mem_P ?_
  have hcomp : ComputableTidilyInPolyTime (fun x : List Bool => (eval x).headD false)
      encBits encBool :=
    (headD (encA := encBool) (encL := encBits) false).comp heval
  convert hcomp using 1
  funext x
  exact hbit x

/-- On bit lists, `balancePadFamily f` reads the tail and XORs with the head bit on non-empty inputs
and returns `false` on `[]`. -/
theorem balancePadFamily_ofList (f : ∀ N, BitString N → Bool) (x : List Bool) :
    balancePadFamily f x.length (BitString.ofList x.length x) =
      (!x.isEmpty &&
        (f x.tail.length (BitString.ofList x.tail.length x.tail) ^^ x.headD false)) := by
  cases x with
  | nil => rfl
  | cons b xs =>
    have htail : Fin.tail (BitString.ofList (xs.length + 1) (b :: xs)) =
        BitString.ofList xs.length xs := by
      funext i
      simp [Fin.tail, BitString.ofList]
    have hzero : BitString.ofList (xs.length + 1) (b :: xs) 0 = b := rfl
    simp [balancePadFamily, balancePad, htail, hzero]

/-- **Balanced padding preserves polynomial-time computability.** -/
theorem computableTidilyInPolyTime_balancePadFamily {f : ∀ N, BitString N → Bool}
    (hf : ComputableTidilyInPolyTime
      (fun x : List Bool => f x.length (BitString.ofList x.length x)) encBits encBool) :
    ComputableTidilyInPolyTime
      (fun x : List Bool => balancePadFamily f x.length (BitString.ofList x.length x))
      encBits encBool := by
  have h := bool_and.comp
    ((bool_not.comp bitsIsEmpty).prod
      (bool_xor.comp ((hf.comp bitsTail).prod (headD (encA := encBool) (encL := encBits) false))))
  convert h using 1
  funext x
  exact balancePadFamily_ofList f x

/-- **Balanced padding preserves membership in `P encBits`.** -/
theorem ofSlices_balancePadFamily_mem_P {f : ∀ N, BitString N → Bool}
    (hf : (Language.ofSlices f : Set (List Bool)) ∈ P encBits) :
    (Language.ofSlices (balancePadFamily f) : Set (List Bool)) ∈ P encBits :=
  ofSlices_mem_P (computableTidilyInPolyTime_balancePadFamily (ofSlices_mem_P_iff.mp hf))

/-! ### Polylogarithmic min-entropy thresholds -/

/-- **Every polylogarithmic function `(log N)^C` is `o(N)`.** -/
theorem isLittleO_rpow_log_id (C : ℝ) :
    (fun N : ℕ => (Real.log N) ^ C) =o[atTop] fun N : ℕ => (N : ℝ) := by
  have h := (isLittleO_log_rpow_rpow_atTop C one_pos).natCast_atTop
  refine h.congr_right fun N => ?_
  simp [Real.rpow_one]

/-- Any sequence `k = O((log N)^C)` is `o(N)`. -/
theorem isLittleO_of_isBigO_rpow_log {k : ℕ → ℝ} {C : ℝ}
    (hk : k =O[atTop] fun N : ℕ => (Real.log N) ^ C) :
    k =o[atTop] fun N : ℕ => (N : ℝ) :=
  hk.trans_isLittleO (isLittleO_rpow_log_id C)

/-- Any nonnegative sequence eventually bounded by `A * (log N)^C` is `o(N)`. This covers both
[Chattopadhyay and Liao][ChattopadhyayLiao2022] (`k_N = (log N)^C`) and [Li][Li2023]
(`k_N = A log N`). -/
theorem isLittleO_of_eventually_le_mul_rpow_log {k : ℕ → ℝ} {A C : ℝ}
    (h0 : ∀ᶠ N in atTop, 0 ≤ k N) (hle : ∀ᶠ N in atTop, k N ≤ A * (Real.log N) ^ C) :
    k =o[atTop] fun N : ℕ => (N : ℝ) := by
  refine isLittleO_of_isBigO_rpow_log (C := C) (IsBigO.of_bound |A| ?_)
  filter_upwards [h0, hle, eventually_ge_atTop 1] with N h0N hleN hN1
  have hlog_nonneg : 0 ≤ (Real.log N) ^ C :=
    Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hN1)) C
  rw [Real.norm_of_nonneg h0N, Real.norm_of_nonneg hlog_nonneg]
  exact hleN.trans (mul_le_mul_of_nonneg_right (le_abs_self A) hlog_nonneg)

/-! ### Unification with Mishra–Santhanam's `3.5 N - 7 d` gate-elimination bound -/

/-- **Mishra–Santhanam's `3.5 N - 7 d` bound holds for every `K`-sumset disperser with
`K ≤ 2 ^ d`:** every circuit over `fullSignature 2 Bool` computing `single f` has at least
`3.5 N - 7 d` gates, stated without subtraction as `7 N ≤ 2 |C| + 14 d`. -/
theorem SumsetDisperser.seven_mul_le_two_mul_size_add {N K d : ℕ} {f : BitString N → Bool}
    (h : SumsetDisperser {z | f z = true} K) (hK : K ≤ 2 ^ d)
    (C : Circuit (fullSignature 2 Bool) N 1)
    (hC : C.Computes fullInterpretation (single f)) :
    7 * N ≤ 2 * C.size + 14 * d :=
  Boolean.AffineDisperser.seven_mul_le_two_mul_size_add (h.isAffineDisperser hK) C hC

/-- **Mishra–Santhanam's `3.5 N - 7 d` bound holds for every `(k, δ)`-sumset extractor with
`δ < 1 / 2` and `k ≤ d`:** every circuit over `fullSignature 2 Bool` computing `single f` satisfies
`7 N ≤ 2 |C| + 14 d` at every input length `N`, in addition to the asymptotic `(4.56249 - ε) N`
Gaussian frontier bound. -/
theorem IsSumsetExtractor.seven_mul_le_two_mul_size_add {N d : ℕ} {f : BitString N → Bool}
    {k δ : ℝ} (h : IsSumsetExtractor f k δ) (hδ : δ < 1 / 2) (hk : k ≤ d)
    (C : Circuit (fullSignature 2 Bool) N 1)
    (hC : C.Computes fullInterpretation (single f)) :
    7 * N ≤ 2 * C.size + 14 * d :=
  Boolean.AffineDisperser.seven_mul_le_two_mul_size_add (h.isAffineDisperser hδ hk) C hC

/-! ### Conditional `(4.56249 - ε) N` average-case and worst-case lower bounds in `P` -/

/-- **Average-case `(4.56249 - ε) N` lower bound for the slices of a sumset-extractor language.**
If `E_N : BitString N → Bool` is a `(k_N, δ_N)`-sumset extractor with `k_N = o(N)`, then for every
`ε > 0` there is `γ > 0` such that for all large `N`, every circuit `C` over `fullSignature 2 Bool`
of size at most `(456249 / 100000 - ε) N` agrees with `(Language.ofSlices E).slice N` on at most a
`1 / 2 + δ_N + exp (-γ N)` fraction of the inputs. -/
theorem eventually_agreement_le_ofSlices_of_isSumsetExtractor
    {E : ∀ N, BitString N → Bool} {k δ : ℕ → ℝ}
    (hE : ∀ᶠ N in atTop, IsSumsetExtractor (E N) (k N) (δ N))
    (hk : k =o[atTop] fun N : ℕ => (N : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ > 0, ∀ᶠ N in atTop, ∀ C : Circuit (fullSignature 2 Bool) N 1,
      (C.size : ℝ) ≤ (456249 / 100000 - ε) * N →
        agreement {z | (Language.ofSlices E).slice N z = true}
          {x | C.eval fullInterpretation x 0 = true} ≤
            1 / 2 + δ N + Real.exp (-(γ * N)) := by
  obtain ⟨γ, hγ, hbound⟩ := eventually_agreement_le_of_isSumsetExtractor_fullSignature hE hk hε
  refine ⟨γ, hγ, hbound.mono fun N hN C hsize => ?_⟩
  simpa only [Language.slice_ofSlices, Set.mem_singleton_iff] using
    hN fullInterpretation {true} C hsize

/-- **Conditional: a language in `P` with `(4.56249 - ε) N` average-case circuit hardness over
`B₂`, assuming a polynomial-time sumset-extractor family.** The extractor family is a hypothesis;
none is constructed here. If `E` is tidily computable in polynomial time and is a
`(k_N, δ_N)`-sumset extractor with `k_N = o(N)`, then `L = Language.ofSlices E` is in `P encBits`
and for every `ε > 0` there is `γ > 0` such that eventually every `B₂` circuit of size at most
`(456249 / 100000 - ε) N` agrees with `L.slice N` on at most `1 / 2 + δ_N + exp (-γ N)` of the
inputs. -/
theorem exists_mem_P_eventually_agreement_le_of_isSumsetExtractor
    {E : ∀ N, BitString N → Bool} {k δ : ℕ → ℝ}
    (hP : ComputableTidilyInPolyTime
      (fun x : List Bool => E x.length (BitString.ofList x.length x)) encBits encBool)
    (hE : ∀ᶠ N in atTop, IsSumsetExtractor (E N) (k N) (δ N))
    (hk : k =o[atTop] fun N : ℕ => (N : ℝ)) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ P encBits ∧
      ∀ {ε : ℝ}, 0 < ε → ∃ γ > 0, ∀ᶠ N in atTop, ∀ C : Circuit (fullSignature 2 Bool) N 1,
        (C.size : ℝ) ≤ (456249 / 100000 - ε) * N →
          agreement {z | L.slice N z = true} {x | C.eval fullInterpretation x 0 = true} ≤
            1 / 2 + δ N + Real.exp (-(γ * N)) :=
  ⟨Language.ofSlices E, ofSlices_mem_P hP, fun hε =>
    eventually_agreement_le_ofSlices_of_isSumsetExtractor hE hk hε⟩

/-- **Conditional: a language in `P` with `(4.56249 - ε) N` average-case circuit hardness and
`1 / 2 + N^{-c} + exp (-γ N)` correlation bound**, assuming a polynomial-time sumset-extractor
family `E` in the polylogarithmic min-entropy and polynomially small error regime of
[Chattopadhyay and Liao][ChattopadhyayLiao2022]. The family `E` and its parameters are
hypotheses; this module does not construct it. -/
theorem exists_mem_P_eventually_agreement_le_of_polylog_sumsetExtractor
    {E : ∀ N, BitString N → Bool} {k δ : ℕ → ℝ} {A C c : ℝ}
    (hP : ComputableTidilyInPolyTime
      (fun x : List Bool => E x.length (BitString.ofList x.length x)) encBits encBool)
    (hE : ∀ᶠ N in atTop, IsSumsetExtractor (E N) (k N) (δ N))
    (hk0 : ∀ᶠ N in atTop, 0 ≤ k N)
    (hk : ∀ᶠ N in atTop, k N ≤ A * (Real.log N) ^ C)
    (hδ : ∀ᶠ N in atTop, δ N ≤ (N : ℝ) ^ (-c)) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ P encBits ∧
      ∀ {ε : ℝ}, 0 < ε → ∃ γ > 0, ∀ᶠ N in atTop, ∀ Cir : Circuit (fullSignature 2 Bool) N 1,
        (Cir.size : ℝ) ≤ (456249 / 100000 - ε) * N →
          agreement {z | L.slice N z = true} {x | Cir.eval fullInterpretation x 0 = true} ≤
            1 / 2 + (N : ℝ) ^ (-c) + Real.exp (-(γ * N)) := by
  refine ⟨Language.ofSlices E, ofSlices_mem_P hP, fun hε => ?_⟩
  obtain ⟨γ, hγ, hbound⟩ := eventually_agreement_le_ofSlices_of_isSumsetExtractor hE
    (isLittleO_of_eventually_le_mul_rpow_log hk0 hk) hε
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hbound, hδ] with N hN hδN Cir hsize
  linarith [hN Cir hsize]

/-- **Worst-case `(4.56249 - ε) N` lower bound for the slices of a sumset-extractor language.** -/
theorem eventually_lt_size_of_computes_ofSlices_of_isSumsetExtractor
    {E : ∀ N, BitString N → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hE : ∀ᶠ N in atTop, IsSumsetExtractor (E N) (k N) (δ N))
    (hk : k =o[atTop] fun N : ℕ => (N : ℝ))
    (hδ : ∀ᶠ N in atTop, δ N ≤ δ₀) (hδ₀ : δ₀ < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ C : Circuit (fullSignature 2 Bool) N 1,
      C.Computes fullInterpretation (single ((Language.ofSlices E).slice N)) →
        (456249 / 100000 - ε) * (N : ℝ) < C.size := by
  filter_upwards [eventually_456249_div_100000_sub_mul_lt_size_of_isSumsetExtractor_computes
    hE hk hδ hδ₀ hε] with N hN C hC
  rw [Language.slice_ofSlices] at hC
  exact hN fullInterpretation C hC

/-- **Conditional: a language in `P` with `B₂` circuit complexity `> (4.56249 - ε) N`, assuming a
polynomial-time sumset-extractor family `E`.** The family is a hypothesis; none is constructed here.
The statement has the shape of the unconditional
`Cslib.AffineDisperser.exists_mem_P_eventually_le_size` (leading coefficient `7 / 2 = 3.5`); given
such a family it would improve that coefficient to `456249 / 100000 = 4.56249`. -/
theorem exists_mem_P_eventually_lt_size_of_isSumsetExtractor
    {E : ∀ N, BitString N → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hP : ComputableTidilyInPolyTime
      (fun x : List Bool => E x.length (BitString.ofList x.length x)) encBits encBool)
    (hE : ∀ᶠ N in atTop, IsSumsetExtractor (E N) (k N) (δ N))
    (hk : k =o[atTop] fun N : ℕ => (N : ℝ))
    (hδ : ∀ᶠ N in atTop, δ N ≤ δ₀) (hδ₀ : δ₀ < 1 / 2) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ P encBits ∧
      ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N in atTop, ∀ C : Circuit (fullSignature 2 Bool) N 1,
        C.Computes fullInterpretation (single (L.slice N)) →
          (456249 / 100000 - ε) * (N : ℝ) < C.size :=
  ⟨Language.ofSlices E, ofSlices_mem_P hP, fun hε =>
    eventually_lt_size_of_computes_ofSlices_of_isSumsetExtractor hE hk hδ hδ₀ hε⟩

/-- **Conditional: a language in `P` with `B₂` circuit complexity `> 4.56 N`, assuming a
polynomial-time sumset-extractor family**, specializing
`exists_mem_P_eventually_lt_size_of_isSumsetExtractor` to `ε = 249 / 100000`. Compare with the
unconditional `Cslib.AffineDisperser.exists_mem_P_eventually_le_size` (`3.5 N - O(N / log N)`). -/
theorem exists_mem_P_eventually_456_div_100_lt_size_of_isSumsetExtractor
    {E : ∀ N, BitString N → Bool} {k δ : ℕ → ℝ} {δ₀ : ℝ}
    (hP : ComputableTidilyInPolyTime
      (fun x : List Bool => E x.length (BitString.ofList x.length x)) encBits encBool)
    (hE : ∀ᶠ N in atTop, IsSumsetExtractor (E N) (k N) (δ N))
    (hk : k =o[atTop] fun N : ℕ => (N : ℝ))
    (hδ : ∀ᶠ N in atTop, δ N ≤ δ₀) (hδ₀ : δ₀ < 1 / 2) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ P encBits ∧
      ∀ᶠ N in atTop, ∀ C : Circuit (fullSignature 2 Bool) N 1,
        C.Computes fullInterpretation (single (L.slice N)) →
          456 / 100 * (N : ℝ) < C.size := by
  obtain ⟨L, hLP, hbound⟩ :=
    exists_mem_P_eventually_lt_size_of_isSumsetExtractor hP hE hk hδ hδ₀
  refine ⟨L, hLP, ?_⟩
  filter_upwards [hbound (ε := 249 / 100000) (by norm_num)] with N hN C hC
  have := hN C hC
  linarith

/-- **Conditional: a language in `P` with `B₂` circuit complexity `> (4.56249 - ε) N`, assuming a
qualitative sumset-disperser family whose language is in `P`**, via one-bit balanced padding
(`balancePadFamily`), requiring no quantitative bias bound. The disperser family is a hypothesis;
none is constructed here. -/
theorem exists_mem_P_eventually_lt_size_of_sumsetDisperser
    {D : ∀ N, BitString N → Bool} {K : ℕ → ℕ}
    (hP : (Language.ofSlices D : Set (List Bool)) ∈ P encBits)
    (hD : ∀ᶠ N in atTop, SumsetDisperser {z | D N z = true} (K N))
    (hKpos : ∀ᶠ N in atTop, 0 < K N)
    (hK : (fun N => Real.log (K N)) =o[atTop] fun N : ℕ => (N : ℝ)) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ P encBits ∧
      ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N in atTop, ∀ C : Circuit (fullSignature 2 Bool) N 1,
        C.Computes fullInterpretation (single (L.slice N)) →
          (456249 / 100000 - ε) * (N : ℝ) < C.size := by
  refine ⟨Language.ofSlices (balancePadFamily D), ofSlices_balancePadFamily_mem_P hP, fun hε => ?_⟩
  filter_upwards [eventually_456249_div_100000_sub_mul_lt_size_balancePadFamily hD hKpos hK hε]
    with N hN C hC
  rw [Language.slice_ofSlices] at hC
  exact hN fullInterpretation {true} C (hC.decides {true})

end Cslib.Circuits.Frontier
