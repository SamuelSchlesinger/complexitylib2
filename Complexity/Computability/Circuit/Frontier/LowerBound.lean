/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Demand
public import Complexity.Computability.Circuit.Frontier.Reduction

/-!
# The frontier lower bound

**Main theorem** (`eventually_lt_mul_innerSize`). Fix a fan-in bound `r ≥ 2`, and suppose that
the graphs of maximum degree `r + 1` have layouts of width `(A + o(1)) β₁ + o(|V|)`, where `β₁` is
the cycle rank (the layout hypothesis `LayoutBound (r + 1) A`). Let `S_n ⊆ U^n` be
`K_n`-rectangle-free sets over a finite alphabet `U`, with `log K_n = o(n)` and
`|S_n| ≥ |U| ^ (n - o(n))`. Then for every `ε > 0` and all large `n`, every circuit deciding
`S_n` over any basis of fan-in at most `r` on `U` has `s` inner gates with

`(r - 1) s > (1 + 1/A - ε) n`.

Gates of arity zero, the constants, are not counted. For fan-in two
(`eventually_lt_innerSize`) the graphs are subcubic and the bound reads `s > (1 + 1/A - ε) n`.

The proof is the reduction theorem followed by the comparison of demand and supply
(`eventually_lt_of_demand`). A circuit with `s` inner gates gives a graph of cycle rank about
`(r - 1) s - n`, all of whose layouts have width about `n`: that is the demand. The layout
hypothesis provides a layout of width about `A ((r - 1) s - n)`: that is the supply. So
`n ≤ A ((r - 1) s - n) + o(n)`, that is, `(r - 1) s ≥ (1 + 1/A - o(1)) n`.

The theorems of this file are conditional on the layout hypothesis, which is stated as
`LayoutBound`; any instance of it yields an unconditional lower bound.

**The worst-case claim** (`CircuitLowerBound L`) bundles the statement for fan-in two with
coefficient `L`, so that each layout theorem reads as one line:
`circuitLowerBound_of_layoutBound : LayoutBound 3 A → CircuitLowerBound (1 + 1/A)`.

## Main definitions

* `Cslib.Circuits.Frontier.CircuitLowerBound L`: circuits of fan-in at most two deciding dense
  rectangle-free sets need more than `(L - ε) n` inner gates.

## Main results

* `Cslib.Circuits.Frontier.eventually_lt_of_graph`: the comparison of demand and supply for any
  family of graphs with the bounds of the reduction theorem.
* `Cslib.Circuits.Frontier.eventually_lt_mul_innerSize`: the frontier lower bound for fan-in at
  most `r`.
* `Cslib.Circuits.Frontier.eventually_lt_innerSize`: the frontier lower bound for fan-in two.
* `Cslib.Circuits.Frontier.circuitLowerBound_of_layoutBound`: the same, as a bundled claim.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set Filter Asymptotics

universe u v

variable {U : Type u} [Finite U] [Nontrivial U]

/-- A set of inputs has at most `|U| ^ n` elements: `log_|U| |S| ≤ n`. -/
theorem logb_ncard_le_self {n : ℕ} {S : Set (Fin n → U)} (hS : S.Nonempty) :
    Real.logb (Nat.card U) S.ncard ≤ n := by
  have hq : (1 : ℝ) < Nat.card U := by exact_mod_cast Finite.one_lt_card
  have hle : (S.ncard : ℝ) ≤ (Nat.card U : ℝ) ^ n := by
    have := ncard_le_card S
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at this
    exact_mod_cast this
  have hpos : (0 : ℝ) < S.ncard := by exact_mod_cast (ncard_pos (toFinite S)).mpr hS
  calc Real.logb (Nat.card U) S.ncard ≤ Real.logb (Nat.card U) ((Nat.card U : ℝ) ^ n) :=
        Real.logb_le_logb_of_le hq hpos hle
    _ = n := by rw [Real.logb_pow, Real.logb_self_eq_one hq, mul_one]

variable {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}

/-- A dense family of sets has `n - log_|U| |S_n| = o(n)`. -/
theorem isLittleO_sub_logb_ncard
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ)) :
    (fun n : ℕ => (n : ℝ) - Real.logb (Nat.card U) (S n).ncard) =o[atTop] fun n => (n : ℝ) := by
  have hL : 0 < Real.log (Nat.card U) := Real.log_pos (by exact_mod_cast Finite.one_lt_card)
  refine (hdense.const_mul_left (1 / Real.log (Nat.card U))).congr_left fun n => ?_
  simp only [Real.logb]
  field_simp

/-- A dense family of rectangle-free sets is eventually large enough for the reduction:
`|U| K_n ^ 2 ≤ |S_n|`. -/
theorem eventually_card_mul_sq_le_ncard (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ)) :
    ∀ᶠ n in atTop, Nat.card U * K n ^ 2 ≤ (S n).ncard := by
  set q := Nat.card U
  have hq : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
  have hL : 0 < Real.log q := Real.log_pos hq
  have hlog : (fun n : ℕ => Real.log q + 2 * Real.log (K n) +
      (n * Real.log q - Real.log (S n).ncard)) =o[atTop] fun n => (n : ℝ) :=
    ((isLittleO_const_left.mpr
      (Or.inr (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop))).add
      (hK.const_mul_left 2)).add hdense
  filter_upwards [hlog.bound (show 0 < Real.log q / 2 by positivity), hfree,
    eventually_ge_atTop 1] with n hn hfreen hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hK1 : (1 : ℝ) ≤ K n := by exact_mod_cast hfreen.pos
  have hlogK : 0 ≤ Real.log (K n) := Real.log_nonneg hK1
  simp only [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)] at hn
  have hb := (le_abs_self _).trans hn
  -- `log |S| ≥ log q + 2 log K + (n / 2) log q > log (q K ^ 2)`.
  have hSlog : Real.log q + 2 * Real.log (K n) < Real.log (S n).ncard := by nlinarith
  have hSpos : (0 : ℝ) < (S n).ncard := by
    by_contra! h0
    have : ((S n).ncard : ℝ) = 0 := le_antisymm h0 (Nat.cast_nonneg _)
    rw [this, Real.log_zero] at hSlog
    nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ q by linarith)]
  have : Real.log (q * K n ^ 2 : ℝ) ≤ Real.log (S n).ncard := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    linarith
  exact_mod_cast (Real.log_le_log_iff (by positivity) hSpos).mp this

/-- **Demand against supply for graphs.** Assume the layout hypothesis for maximum degree `r + 1`
with coefficient `A > 0`, and let `S_n` be dense `K_n`-rectangle-free sets with
`log K_n = o(n)`. For every `ε > 0` and all large `n`: every connected, loopless graph of maximum
degree `r + 1` with the bounds of the reduction theorem for `g` gates (at most `2 r g + 3`
vertices, cycle rank at most `(r - 1) g - n + log_q K_n + 1`, and every layout of width at least
`log_q |S_n| - 3 log_q K_n - log_q (|V| + 1) - (r + 2)`) has `(r - 1) g > (1 + 1/A - ε) n`.

This is the numerical half of the lower bound, independent of circuits. -/
theorem eventually_lt_of_graph {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (g : ℕ) (V E : Type) [Finite V] [Finite E] (G : Multigraph V E),
      G.toSimpleGraph.Connected → G.Loopless → G.MaxDegreeLE (r + 1) →
      Nat.card V ≤ 2 * r * g + 3 →
      (G.cycleRank : ℝ) ≤ (r - 1) * g - n + Real.logb (Nat.card U) (K n) + 1 →
      (∀ π : Layout V, Real.logb (Nat.card U) (S n).ncard ≤
        G.width π + (r + 2) + 3 * Real.logb (Nat.card U) (K n) +
          Real.logb (Nat.card U) (Nat.card V + 1)) →
      (1 + 1 / A - ε) * n < (r - 1) * g := by
  set q := Nat.card U
  have hq : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
  -- The error of the problem: the density defect, the threshold, and constants.
  set e : ℕ → ℝ := fun n => (n - Real.logb q (S n).ncard) + 4 * Real.logb q (K n) + (r + 3)
  have he : e =o[atTop] fun n => (n : ℝ) := by
    have h2 : (fun n : ℕ => 4 * Real.logb q (K n)) =o[atTop] fun n => (n : ℝ) :=
      (hK.const_mul_left (4 / Real.log q)).congr_left fun n => by
        simp only [Real.logb]
        ring
    have h3 : (fun _ : ℕ => ((r : ℝ) + 3)) =o[atTop] fun n => (n : ℝ) :=
      isLittleO_const_left.mpr
        (Or.inr (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop))
    exact ((isLittleO_sub_logb_ncard hdense).add h2).add h3
  -- The constant bounding the size of the graph and the change of base of its logarithm.
  set κ : ℝ := 4 + 1 / Real.log 2
  have hκ : 0 ≤ κ := by positivity
  obtain ⟨η, hη, H⟩ := eventually_lt_of_demand hA hκ hε
  obtain ⟨C, hC⟩ := hlayout η hη
  filter_upwards [H η hη le_rfl C e he, hfree,
    eventually_card_mul_sq_le_ncard hfree hK hdense] with n hn hfreen hbign
  intro g V E _ _ G hconn hloop hdeg hV hrank hwidth
  obtain ⟨π, hπ⟩ := hC V E G hconn hloop hdeg
  have hwidth := hwidth π
  -- The quantities of the comparison.
  set s : ℝ := (r - 1) * g
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hs : 0 ≤ s := mul_nonneg (by linarith) (Nat.cast_nonneg g)
  have hK1 : (1 : ℝ) ≤ K n := by exact_mod_cast hfreen.pos
  have hlogK : 0 ≤ Real.logb q (K n) := Real.logb_nonneg hq hK1
  have hSne : (S n).Nonempty := by
    rw [← ncard_pos (toFinite _)]
    exact lt_of_lt_of_le (Nat.mul_pos Nat.card_pos (pow_pos hfreen.pos 2)) hbign
  have hlogS := logb_ncard_le_self hSne
  have hlogV : Real.logb q (Nat.card V + 1) ≤ κ * Real.log (Nat.card V + 1) :=
    logb_le_mul_log (by exact_mod_cast (Finite.one_lt_card : 2 ≤ q))
      (by linarith [Nat.cast_nonneg (α := ℝ) (Nat.card V)])
  have hVs : (Nat.card V : ℝ) ≤ κ * (n + s + 1) := by
    have hV' : (Nat.card V : ℝ) ≤ 2 * r * g + 3 := by exact_mod_cast hV
    have hκ4 : 4 ≤ κ := by simp only [κ]; linarith [show 0 ≤ 1 / Real.log 2 by positivity]
    have hg : (0 : ℝ) ≤ g := Nat.cast_nonneg g
    have hns : 0 ≤ (n : ℝ) + s + 1 := by positivity
    -- `2 r g + 3 ≤ 4 (r - 1) g + 4`, since `2 r ≤ 4 (r - 1)`.
    nlinarith
  refine hn s (Nat.card V) (G.width π) hs (Nat.cast_nonneg _) hVs ?_ ?_
  · -- The demand: `n ≤ width + e(n) + κ log (|V| + 1)`.
    simp only [e]
    linarith
  · -- The supply: the layout hypothesis, with the cycle rank of the reduction.
    have hrank' : (G.cycleRank : ℝ) ≤ s - n + e n := by
      simp only [e]
      linarith
    have := mul_le_mul_of_nonneg_left hrank' (by linarith : 0 ≤ A + η)
    linarith

/-- **The frontier lower bound.** Let `r ≥ 2` and assume the layout hypothesis for maximum degree
`r + 1` with coefficient `A > 0`. Let `S_n ⊆ U^n` be `K_n`-rectangle-free sets over a finite
alphabet `U` with at least two symbols, with `log K_n = o(n)` and
`n log |U| - log |S_n| = o(n)`. Then for every `ε > 0` and all large `n`, every circuit of fan-in
at most `r` deciding `S_n`, over any basis and interpretation on `U`, has `s` inner gates with
`(r - 1) s > (1 + 1/A - ε) n`. -/
theorem eventually_lt_mul_innerSize {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        (1 + 1 / A - ε) * n < (r - 1) * c.innerSize := by
  filter_upwards [eventually_lt_of_graph hr hA hlayout hfree hK hdense hε, hfree,
    eventually_card_mul_sq_le_ncard hfree hK hdense] with n hn hf hb
  intro σ I Acc c hfan hS
  obtain ⟨V, E, _, _, G, hc, hl, hd, hV, hrank, hw⟩ := exists_graph_of_decides hr hfan hS hf hb
  exact hn c.innerSize V E G hc hl hd hV hrank hw

/-- **The frontier lower bound for fan-in two.** Assume the layout hypothesis for subcubic graphs
with coefficient `A > 0`. Under the hypotheses of `eventually_lt_mul_innerSize`, for every
`ε > 0` and all large `n`, every circuit of fan-in at most two deciding `S_n`, over any basis and
interpretation on `U`, has more than `(1 + 1/A - ε) n` inner gates. -/
theorem eventually_lt_innerSize {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound 3 A)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (1 + 1 / A - ε) * n < c.innerSize := by
  filter_upwards [eventually_lt_mul_innerSize le_rfl hA hlayout hfree hK hdense hε] with n hn
  intro σ I Acc c hfan hS
  simpa only [Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using
    hn σ I Acc c hfan hS

/-- **The worst-case claim with coefficient `L`.** Let `U` be a finite alphabet with at least
two symbols, and let `S_n ⊆ U^n` be `K_n`-rectangle-free sets with `log K_n = o(n)` and
`n log |U| - log |S_n| = o(n)`. Then for every `ε > 0` and all large `n`, every circuit of fan-in
at most two deciding `S_n`, over any basis and interpretation on `U`, has more than `(L - ε) n`
gates of positive arity.

The alphabet lives in the universe `u` and the basis in the universe `v`. -/
def CircuitLowerBound (L : ℝ) : Prop :=
  ∀ (U : Type u) [Finite U] [Nontrivial U] (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ),
    (∀ᶠ n in atTop, RectangleFree (S n) (K n)) →
    (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
    (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop] (fun n => (n : ℝ)) →
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (L - ε) * n < c.innerSize

/-- A circuit lower bound holds for every smaller coefficient. -/
theorem CircuitLowerBound.mono {L L' : ℝ} (h : CircuitLowerBound.{u, v} L) (hL : L' ≤ L) :
    CircuitLowerBound.{u, v} L' := by
  intro U _ _ S K hfree hK hdense ε hε
  filter_upwards [h U S K hfree hK hdense ε hε] with n hn
  intro σ I Acc c hfan hS
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (sub_le_sub_right hL ε) (Nat.cast_nonneg n))
    (hn σ I Acc c hfan hS)

/-- **The frontier lower bound as a bundled claim.** If subcubic graphs have layouts of width
`(A + o(1)) β₁ + o(|V|)` (`LayoutBound 3 A`), then circuits of fan-in at most two deciding dense
rectangle-free sets need more than `(1 + 1/A - ε) n` inner gates. -/
theorem circuitLowerBound_of_layoutBound {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound 3 A) :
    CircuitLowerBound.{u, v} (1 + 1 / A) :=
  fun _ _ _ _ _ hfree hK hdense _ hε => eventually_lt_innerSize hA hlayout hfree hK hdense hε

end Cslib.Circuits.Frontier
