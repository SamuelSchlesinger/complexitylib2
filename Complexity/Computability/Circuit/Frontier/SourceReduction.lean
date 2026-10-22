/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Frontier.SourceReduction.Conditioning
public import Complexity.Computability.Circuit.Frontier.SourceReduction.Majority
public import Complexity.Computability.Circuit.Frontier.SourceReduction.Sampler
public import Complexity.Foundations.Data.BitString.Parity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The Chattopadhyay–Liao XOR source reduction to non-oblivious bit-fixing sources

In [Chattopadhyay and Liao][ChattopadhyayLiao2022] (Lemma 5.4 and Theorem 2), two independent weak
sources `X, Y` are reduced via their sum `X + Y` to a non-oblivious bit-fixing (NOBF) source on `D`
bits, to which `strictMajority D` is applied:
1. **Deterministic XOR reduction (`affineSourceReduction`):** at each outer coordinate `i : Fin D`,
   we take the parity (`Cslib.parity C`) of `C` correlation-breaker calls
   `cb z (sampler z i r) (advice i r)` across all candidates `r : Fin C`.
2. **Sign-product invariance (`affineSourceReduction_parity_bias_eq`):** the `±1` sign of a parity
   of `C` bits equals `(-1)^(C + 1)` times the product of the `C` candidate signs (`sign_parity`),
   so the absolute weighted mean of any subset `U ⊆ Fin D` of outer signs equals the absolute
   weighted mean of the product of all `|U| * C` candidate signs.
3. **Bad-seed union bound (`parityTests`, `parityBadSeeds`, `card_parityBadSeeds_le`):** there are
   at most `D^t` nonempty parity tests `U ⊆ Fin D` of size at most `t`. Unioning bad seeds over all
   `U ∈ parityTests (Fin D) 4` and all `r : Fin C` multiplies the single-test bad-seed density `η`
   by at most `D^4 * C`.
4. **Good second-source fibers from a somewhere sampler (`SomewhereSampler.exists_good_fibers`,
   `SomewhereSampler.parity_fibers`):** a `SomewhereSampler` applied to `parityBadSeeds bad 4` on
   the second source `Q` guarantees that on at least a `1 - δ` fraction of `y ∈ Q`, at least
   `m ≥ D - 2 ε D` outer coordinates have *at least one* candidate `r` avoiding `parityBadSeeds`,
   which suffices for `ParityBiasBound` on those `m` good coordinates.
5. **Sumset bias `35 / 72 < 1 / 2` (`strictMajority_sumsetBias_of_parity_fibers`,
   `sumsetBias_strictMajority_affineSourceReduction`):** combining the `1 / 2` fraction of good
   second-source fibers with the `1 / 36` fourth-moment majority tail bound yields
   `SumsetBias {z | strictMajority D (reduce z) = true} K (35 / 72)` (`1 / 2 - (1 / 36) * (1 / 2) =
   35 / 72 < 1 / 2`), and hence a `SumsetDisperser` at threshold `K`.
6. **Parameter arithmetic (`sourceReduction_union_budget`, `sourceReduction_moment_budget`,
   `sourceReduction_majority_guards`):** explicit dyadic parameter schedules for `b ≥ 5` satisfying
   all union, fourth-moment, and majority-margin guards simultaneously.

This module proves the reduction and its conditional composition theorems; it does not construct an
unconditional correlation breaker or somewhere sampler.

## Main definitions

* `Cslib.Circuits.Frontier.affineSourceReduction`: XOR (`Cslib.parity C`) of candidate
  correlation-breaker outputs at each outer coordinate.
* `Cslib.Circuits.Frontier.parityTests`, `Cslib.Circuits.Frontier.parityBadSeeds`: nonempty
  coordinate subsets of size `≤ t` and their combined bad-seed set.
* `Cslib.Circuits.Frontier.sourceReductionOuterBits`,
  `Cslib.Circuits.Frontier.sourceReductionOuterCount`,
  `Cslib.Circuits.Frontier.sourceReductionCandidateCount`,
  `Cslib.Circuits.Frontier.sourceReductionTarget`,
  `Cslib.Circuits.Frontier.sourceReductionSamplerError`,
  `Cslib.Circuits.Frontier.sourceReductionBadThreshold`,
  `Cslib.Circuits.Frontier.sourceReductionParityBias`: dyadic parameter schedule for Lemma 5.4.

## Main results

* `Cslib.Circuits.Frontier.sign_parity`,
  `Cslib.Circuits.Frontier.affineSourceReduction_parity_bias_eq`: parity sign factorization and
  invariance of absolute parity bias.
* `Cslib.Circuits.Frontier.card_parityTests_le_pow`,
  `Cslib.Circuits.Frontier.card_parityBadSeeds_le`: counting low-order parity tests and bad seeds.
* `Cslib.Circuits.Frontier.SomewhereSampler.exists_good_fibers`,
  `Cslib.Circuits.Frontier.SomewhereSampler.parity_fibers`: selection of good second-source fibers
  and good outer coordinates.
* `Cslib.Circuits.Frontier.strictMajority_flatSumsetExtractor_of_parity_fibers`,
  `Cslib.Circuits.Frontier.strictMajority_sumsetBias_of_parity_fibers`: conditional sumset bias
  `35 / 72` from parity-biased fibers.
* `Cslib.Circuits.Frontier.sourceReduction_union_budget`,
  `Cslib.Circuits.Frontier.sourceReduction_moment_budget`,
  `Cslib.Circuits.Frontier.sourceReduction_majority_guards`: dyadic parameter verification.
* `Cslib.Circuits.Frontier.sumsetBias_strictMajority_affineSourceReduction`,
  `Cslib.Circuits.Frontier.sumsetDisperser_strictMajority_affineSourceReduction`: end-to-end
  conditional sumset bias `35 / 72` and `SumsetDisperser` for
  `strictMajority ∘ affineSourceReduction` at scale `b ≥ 5`.

## References

* [E. Chattopadhyay and J.-J. Liao, *Extractors for Sum of Two Sources*][ChattopadhyayLiao2022]
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Cslib.BitString

/-! ### Conditional sumset bias `35 / 72` from good second-source parity fibers -/

/-- **Conditional `FlatSumsetExtractor` with bias `35 / 72` from parity-biased fibers:** if for
every `P, Q : Finset G` of size at least `K > 0`, at least half of `y ∈ Q` admit `m > 0` coordinates
`good : Fin m ↪ Fin D` of `reduce (x + y)` with `100 m^2 δ ≤ 1`, `ParityBiasBound` at level `δ`, and
at most `√m / 8` bad coordinates, then `fun z => strictMajority D (reduce z)` is a flat
`(K, 35 / 72)`-sumset extractor. -/
theorem strictMajority_flatSumsetExtractor_of_parity_fibers {G : Type*} [Add G] {D K : ℕ}
    (reduce : G → BitString D) (positive : 0 < K)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (fibers : ∀ P Q : Finset G, K ≤ P.card → K ≤ Q.card →
      ∃ Good ⊆ Q, (1 / 2 : ℝ) * Q.card ≤ Good.card ∧
        ∀ y ∈ Good, ∃ (m : ℕ) (good : Fin m ↪ Fin D), 0 < m ∧
          100 * (m : ℝ) ^ 2 * δ ≤ 1 ∧
          ParityBiasBound P (fun _ => 1 / (P.card : ℝ))
            (fun x i => if reduce (x + y) (good i) then 1 else -1) δ ∧
          ((D - m : ℕ) : ℝ) ≤ Real.sqrt (m : ℝ) / 8) :
    FlatSumsetExtractor (fun z => strictMajority D (reduce z)) K (35 / 72) := by
  have h := FlatSumsetExtractor.of_many_good_fibers (f := fun z => strictMajority D (reduce z))
    (ρ := 1 / 36) (θ := 1 / 2) positive (by norm_num) fun P Q hP hQ => by
      obtain ⟨Good, inside, many, goodFibers⟩ := fibers P Q hP hQ
      refine ⟨Good, inside, many, fun y hy b => ?_⟩
      obtain ⟨m, good, hm, budget, bias, bad⟩ := goodFibers y hy
      have hPpos : (0 : ℝ) < P.card := by exact_mod_cast positive.trans_le hP
      exact strictMajority_mass_ge_of_parityBias good (fun x => reduce (x + y))
        (fun _ _ => div_nonneg zero_le_one hPpos.le)
        (by simp [ne_of_gt hPpos]) hm hδ budget bias bad b
  exact h.mono le_rfl (by norm_num)

/-- **Conditional `SumsetBias` `35 / 72` from parity-biased fibers** on a finite additive type
`G`. -/
theorem strictMajority_sumsetBias_of_parity_fibers {G : Type*} [Add G] [Finite G] {D K : ℕ}
    (reduce : G → BitString D) (positive : 0 < K)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (fibers : ∀ P Q : Finset G, K ≤ P.card → K ≤ Q.card →
      ∃ Good ⊆ Q, (1 / 2 : ℝ) * Q.card ≤ Good.card ∧
        ∀ y ∈ Good, ∃ (m : ℕ) (good : Fin m ↪ Fin D), 0 < m ∧
          100 * (m : ℝ) ^ 2 * δ ≤ 1 ∧
          ParityBiasBound P (fun _ => 1 / (P.card : ℝ))
            (fun x i => if reduce (x + y) (good i) then 1 else -1) δ ∧
          ((D - m : ℕ) : ℝ) ≤ Real.sqrt (m : ℝ) / 8) :
    SumsetBias {z | strictMajority D (reduce z) = true} K (35 / 72) :=
  (strictMajority_flatSumsetExtractor_of_parity_fibers reduce positive hδ fibers).sumsetBias

/-! ### The deterministic XOR source reduction and parity sign factorization -/

/-- **Deterministic XOR source reduction ([Chattopadhyay and Liao][ChattopadhyayLiao2022], Lemma
5.4):** at each outer coordinate `i : Fin D`, take the parity (`Cslib.parity C`) of the `C`
candidate correlation-breaker outputs `cb x (sampler x i z) (advice i z)`. -/
def affineSourceReduction {α Seed Advice : Type*} {D C : ℕ}
    (cb : α → Seed → Advice → Bool)
    (sampler : α → Fin D → Fin C → Seed)
    (advice : Fin D → Fin C → Advice) (x : α) : BitString D :=
  fun i => parity C (fun z => cb x (sampler x i z) (advice i z))

private theorem sign_xor (a b : Bool) :
    (if (a ^^ b) then (1 : ℝ) else -1) =
      -(if a then (1 : ℝ) else -1) * (if b then (1 : ℝ) else -1) := by
  cases a <;> cases b <;> norm_num

/-- For any finite index set `s : Finset ι`, the `±1` sign of `parityOn s bits` equals
`(-1) ^ (s.card + 1)` times the product of the `±1` signs of the individual bits in `s`. -/
theorem sign_parityOn {ι : Type*} (s : Finset ι) (bits : ι → Bool) :
    (if parityOn s bits then (1 : ℝ) else -1) =
      (-1 : ℝ) ^ (s.card + 1) * ∏ z ∈ s, (if bits z then (1 : ℝ) else -1) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [parityOn_insert ha, sign_xor, ih, Finset.card_insert_of_notMem ha,
      Finset.prod_insert ha, pow_succ]
    ring

/-- The `±1` sign of `parity C bits` equals `(-1) ^ (C + 1)` times the product of the `C`
coordinate signs. -/
theorem sign_parity (C : ℕ) (bits : BitString C) :
    (if parity C bits then (1 : ℝ) else -1) =
      (-1 : ℝ) ^ (C + 1) * ∏ z : Fin C, (if bits z then (1 : ℝ) else -1) := by
  rw [parity, sign_parityOn, Finset.card_univ, Fintype.card_fin]

/-- **Invariance of absolute parity bias under `affineSourceReduction`:** for any subset
`U : Finset (Fin D)` of outer coordinates, the absolute weighted mean of the product of outer signs
equals the absolute weighted mean of the product of all `|U| * C` candidate signs. -/
theorem affineSourceReduction_parity_bias_eq {α Input Seed Advice : Type*} {D C : ℕ}
    (cb : Input → Seed → Advice → Bool)
    (sampler : Input → Fin D → Fin C → Seed)
    (advice : Fin D → Fin C → Advice)
    (s : Finset α) (w : α → ℝ) (input : α → Input) (U : Finset (Fin D)) :
    |weightedMean s w (fun x =>
      ∏ i ∈ U, if affineSourceReduction cb sampler advice (input x) i then (1 : ℝ) else -1)| =
      |weightedMean s w (fun x =>
        ∏ i ∈ U, ∏ z, if cb (input x) (sampler (input x) i z) (advice i z)
          then (1 : ℝ) else -1)| := by
  have sign (x : α) (i : Fin D) :
      (if affineSourceReduction cb sampler advice (input x) i then (1 : ℝ) else -1) =
        (-1 : ℝ) ^ (C + 1) *
          ∏ z, if cb (input x) (sampler (input x) i z) (advice i z) then (1 : ℝ) else -1 :=
    sign_parity C _
  have factor (x : α) :
      (∏ i ∈ U, if affineSourceReduction cb sampler advice (input x) i then (1 : ℝ) else -1) =
        ((-1 : ℝ) ^ (C + 1)) ^ U.card *
          ∏ i ∈ U, ∏ z, if cb (input x) (sampler (input x) i z) (advice i z)
            then (1 : ℝ) else -1 := by
    simp_rw [sign]
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp_rw [factor]
  simp only [weightedMean, ← mul_assoc, mul_left_comm (w _) (((-1 : ℝ) ^ (C + 1)) ^ U.card)]
  simp only [mul_assoc]
  rw [← Finset.mul_sum, abs_mul]
  simp [abs_pow]

/-! ### Counting low-order parity tests and bad seeds -/

open Classical in
/-- All nonempty coordinate subsets of `ι` of cardinality at most `t`. -/
noncomputable def parityTests (ι : Type*) [Fintype ι] (t : ℕ) : Finset (Finset ι) :=
  Finset.univ.filter fun U => U.Nonempty ∧ U.card ≤ t

open Classical in
/-- Union of bad seeds `bad U z` over all nonempty parity tests `U` of size at most `t` and all
candidate indices `z : Choice`. -/
noncomputable def parityBadSeeds {ι Choice Seed : Type*} [Fintype ι] [Fintype Choice]
    (bad : Finset ι → Choice → Finset Seed) (t : ℕ) : Finset Seed :=
  (parityTests ι t).biUnion fun U => Finset.univ.biUnion (bad U)

private theorem exists_tuple_image {ι : Type*} [DecidableEq ι] (U : Finset ι) {t : ℕ}
    (hne : U.Nonempty) (hcard : U.card ≤ t) :
    ∃ f : Fin t → ι, Finset.univ.image f = U := by
  obtain ⟨a, ha⟩ := hne
  let f : Fin t → ι := fun i =>
    if hi : i.val < U.card then (U.equivFin.symm ⟨i.val, hi⟩).val else a
  refine ⟨f, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    dsimp only [f]
    split_ifs with hi
    · exact (U.equivFin.symm _).property
    · exact ha
  · intro hx
    let j := U.equivFin ⟨x, hx⟩
    refine Finset.mem_image.mpr ⟨⟨j.val, j.isLt.trans_le hcard⟩, Finset.mem_univ _, ?_⟩
    dsimp only [f]
    simp only [j.isLt, ↓reduceDIte]
    exact congrArg Subtype.val (U.equivFin.symm_apply_apply ⟨x, hx⟩)

/-- **Upper bound on the number of low-order parity tests:** `|parityTests ι t| ≤ |ι|^t`. -/
theorem card_parityTests_le_pow (ι : Type*) [Fintype ι] (t : ℕ) :
    (parityTests ι t).card ≤ Fintype.card ι ^ t := by
  classical
  have inside : parityTests ι t ⊆
      Finset.univ.image (fun f : Fin t → ι => Finset.univ.image f) := by
    intro U hU
    obtain ⟨hne, hcard⟩ := (Finset.mem_filter.mp hU).2
    obtain ⟨f, hf⟩ := exists_tuple_image U hne hcard
    exact Finset.mem_image.mpr ⟨f, Finset.mem_univ _, hf⟩
  calc
    (parityTests ι t).card ≤
        (Finset.univ.image (fun f : Fin t → ι => Finset.univ.image f)).card :=
      Finset.card_le_card inside
    _ ≤ Fintype.card (Fin t → ι) := Finset.card_image_le
    _ = Fintype.card ι ^ t := Fintype.card_pi_const ι t

/-- **Union bound on `parityBadSeeds`:** if each `bad U z` has density at most `η` in `Seed`, then
`parityBadSeeds bad t` has cardinality at most `|ι|^t * |Choice| * η * |Seed|`. -/
theorem card_parityBadSeeds_le {ι Choice Seed : Type*} [Fintype ι] [Fintype Choice]
    [Fintype Seed] (bad : Finset ι → Choice → Finset Seed) (t : ℕ)
    {η : ℝ} (hη : 0 ≤ η)
    (bound : ∀ U ∈ parityTests ι t, ∀ z,
      ((bad U z).card : ℝ) ≤ η * Fintype.card Seed) :
    ((parityBadSeeds bad t).card : ℝ) ≤
      (Fintype.card ι : ℝ) ^ t * Fintype.card Choice * η * Fintype.card Seed := by
  classical
  have tests : ((parityTests ι t).card : ℝ) ≤ (Fintype.card ι : ℝ) ^ t := by
    exact_mod_cast card_parityTests_le_pow ι t
  have unionBound (U : Finset ι) (hU : U ∈ parityTests ι t) :
      ((Finset.univ.biUnion (bad U)).card : ℝ) ≤
        Fintype.card Choice * (η * Fintype.card Seed) := by
    calc
      ((Finset.univ.biUnion (bad U)).card : ℝ) ≤ ∑ z, ((bad U z).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le (s := Finset.univ) (t := bad U)
      _ ≤ ∑ _z : Choice, η * Fintype.card Seed :=
        Finset.sum_le_sum fun z _ => bound U hU z
      _ = Fintype.card Choice * (η * Fintype.card Seed) := by simp
  calc
    ((parityBadSeeds bad t).card : ℝ) ≤
        ∑ U ∈ parityTests ι t, ((Finset.univ.biUnion (bad U)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
        (s := parityTests ι t) (t := fun U => Finset.univ.biUnion (bad U))
    _ ≤ ∑ _U ∈ parityTests ι t,
        Fintype.card Choice * (η * Fintype.card Seed) := Finset.sum_le_sum unionBound
    _ = (parityTests ι t).card * (Fintype.card Choice * (η * Fintype.card Seed)) := by
      simp
    _ ≤ (Fintype.card ι : ℝ) ^ t *
        (Fintype.card Choice * (η * Fintype.card Seed)) :=
      mul_le_mul_of_nonneg_right tests
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hη (Nat.cast_nonneg _)))
    _ = _ := by ring

/-! ### Selecting good second-source fibers and good outer coordinates via a somewhere sampler -/

/-- **Good second-source fibers from a `SomewhereSampler`:** on any flat source `Q` of size at least
`L` (`0 < Q.card`) and any test `T` of density at most `ε`, at least a `1 - δ` fraction of `y ∈ Q`
have at most `2 ε |Outer|` all-hit outer seeds. -/
theorem SomewhereSampler.exists_good_fibers {α Outer Candidate Ω : Type*}
    [Fintype α] [Fintype Outer] [Fintype Ω]
    {S : α → Outer → Candidate → Ω} {L ε δ : ℝ}
    (sampler : SomewhereSampler S L ε δ) (Q : Finset α)
    (positive : 0 < Q.card) (source : L ≤ Q.card)
    (T : Finset Ω) (small : (T.card : ℝ) ≤ ε * Fintype.card Ω) :
    ∃ Good ⊆ Q, (1 - δ) * Q.card ≤ Good.card ∧
      ∀ y ∈ Good, ((allHitSeeds S T y).card : ℝ) ≤ 2 * ε * Fintype.card Outer := by
  classical
  have hQ : (0 : ℝ) < Q.card := by exact_mod_cast positive
  let p : α → ℝ := fun y => if y ∈ Q then 1 / (Q.card : ℝ) else 0
  have nonneg : ∀ y, 0 ≤ p y := by
    intro y
    dsimp only [p]
    split_ifs <;> positivity
  have mass : ∑ y, p y = 1 := by
    simp [p, div_eq_mul_inv, ne_of_gt hQ]
  have cap : ∀ y, L * p y ≤ 1 := by
    intro y
    by_cases hy : y ∈ Q
    · simpa [p, hy, div_eq_mul_inv] using (div_le_one hQ).mpr source
    · simp [p, hy]
  have failure := sampler T small p nonneg mass cap
  have count : (∑ y ∈ somewhereBadInputs S T ε, p y) =
      (Q ∩ somewhereBadInputs S T ε).card / (Q.card : ℝ) := by
    simp [p, Finset.inter_comm, div_eq_mul_inv]
  rw [count] at failure
  have badBound := (div_le_iff₀ hQ).mp failure
  refine ⟨Q \ somewhereBadInputs S T ε, Finset.sdiff_subset, ?_, ?_⟩
  · have partition : ((Q \ somewhereBadInputs S T ε).card : ℝ) +
        (Q ∩ somewhereBadInputs S T ε).card = Q.card := by
      exact_mod_cast Finset.card_sdiff_add_card_inter Q (somewhereBadInputs S T ε)
    nlinarith only [badBound, partition]
  · intro y hy
    have outside := (Finset.mem_sdiff.mp hy).2
    simpa only [somewhereBadInputs, Finset.mem_filter, Finset.mem_univ, true_and,
      not_lt] using outside

/-- **Seed-escape criterion for `ParityBiasBound`:** if at each good outer coordinate `good i` there
is at least one candidate `z` whose seed `S (good i) z` avoids `parityBadSeeds bad 4`, and for every
parity test `U ∈ parityTests (Fin D) 4` there is some coordinate `j ∈ U` where avoiding `bad U z`
bounds the parity bias by `β`, then the `good` coordinates satisfy `ParityBiasBound` at level
`β`. -/
theorem parityBiasBound_of_seed_escape {α Choice Seed : Type*} [Fintype Choice]
    {m D : ℕ} {s : Finset α} {w : α → ℝ} {σ : α → Fin D → ℝ} {β : ℝ}
    (S : Fin D → Choice → Seed) (bad : Finset (Fin D) → Choice → Finset Seed)
    (good : Fin m ↪ Fin D)
    (escape : ∀ i, ∃ z, S (good i) z ∉ parityBadSeeds bad 4)
    (estimate : ∀ U ∈ parityTests (Fin D) 4, ∃ j ∈ U, ∀ z,
      S j z ∉ bad U z → |weightedMean s w (fun x => ∏ i ∈ U, σ x i)| ≤ β) :
    ParityBiasBound s w (fun x i => σ x (good i)) β := by
  classical
  intro T hT ht
  have imageMem : T.image good ∈ parityTests (Fin D) 4 := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hT.image good, ?_⟩
    simpa only [Finset.card_image_of_injective _ good.injective] using ht
  obtain ⟨j, hj, bound⟩ := estimate (T.image good) imageMem
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨z, hz⟩ := escape i
  have outside : S (good i) z ∉ bad (T.image good) z := by
    intro inside
    apply hz
    exact Finset.mem_biUnion.mpr ⟨T.image good, imageMem,
      Finset.mem_biUnion.mpr ⟨z, Finset.mem_univ _, inside⟩⟩
  have h := bound z outside
  simpa only [Finset.prod_image good.injective.injOn] using h

/-- **Somewhere-sampler selection of parity-biased fibers:** given a `SomewhereSampler S L ε δ` and
a bad-seed family `bad` of density `≤ η` with `D^4 * |Choice| * η ≤ ε`, at least a `1 - δ` fraction
of `y ∈ Q` admit `m ≥ D - 2 ε D` outer coordinates `good : Fin m ↪ Fin D` satisfying
`ParityBiasBound` at level `β`. -/
theorem SomewhereSampler.parity_fibers {α Source Choice Seed : Type*}
    [Fintype Source] [Fintype Choice] [Fintype Seed] {D : ℕ}
    {s : Finset α} {w : α → ℝ} (σ : α → Source → Fin D → ℝ)
    {S : Source → Fin D → Choice → Seed} {L ε δ β η : ℝ}
    (sampler : SomewhereSampler S L ε δ) (Q : Finset Source)
    (positive : 0 < Q.card) (source : L ≤ Q.card)
    (bad : Finset (Fin D) → Choice → Finset Seed) (nonneg : 0 ≤ η)
    (seedBound : ∀ U ∈ parityTests (Fin D) 4, ∀ z,
      ((bad U z).card : ℝ) ≤ η * Fintype.card Seed)
    (budget : (D : ℝ) ^ 4 * Fintype.card Choice * η ≤ ε)
    (estimate : ∀ U ∈ parityTests (Fin D) 4, ∃ j ∈ U, ∀ z, ∀ y ∈ Q,
      S y j z ∉ bad U z →
        |weightedMean s w (fun x => ∏ i ∈ U, σ x y i)| ≤ β) :
    ∃ Good ⊆ Q, (1 - δ) * Q.card ≤ Good.card ∧
      ∀ y ∈ Good, ∃ (m : ℕ) (good : Fin m ↪ Fin D),
        ((D - m : ℕ) : ℝ) ≤ 2 * ε * D ∧
        ParityBiasBound s w (fun x i => σ x y (good i)) β := by
  classical
  have small : ((parityBadSeeds bad 4).card : ℝ) ≤ ε * Fintype.card Seed := by
    have bound := card_parityBadSeeds_le bad 4 nonneg seedBound
    simp only [Fintype.card_fin] at bound
    exact bound.trans (mul_le_mul_of_nonneg_right budget (Nat.cast_nonneg _))
  obtain ⟨Good, inside, many, goodFibers⟩ :=
    sampler.exists_good_fibers Q positive source (parityBadSeeds bad 4) small
  refine ⟨Good, inside, many, ?_⟩
  intro y hy
  let U := Finset.univ \ allHitSeeds S (parityBadSeeds bad 4) y
  let good : Fin U.card ↪ Fin D := (U.orderEmbOfFin rfl).toEmbedding
  refine ⟨U.card, good, ?_, ?_⟩
  · have partition : U.card + (allHitSeeds S (parityBadSeeds bad 4) y).card = D := by
      simpa only [U, Finset.univ_inter, Finset.card_univ, Fintype.card_fin] using
        Finset.card_sdiff_add_card_inter Finset.univ (allHitSeeds S (parityBadSeeds bad 4) y)
    have count : D - U.card = (allHitSeeds S (parityBadSeeds bad 4) y).card := by omega
    rw [count]
    simpa only [Fintype.card_fin] using goodFibers y hy
  · apply parityBiasBound_of_seed_escape (fun i z => S y i z) bad good
    · intro i
      have hmem : good i ∈ U := U.orderEmbOfFin_mem rfl i
      have hout := (Finset.mem_sdiff.mp hmem).2
      simpa only [allHitSeeds, Finset.mem_filter, Finset.mem_univ, true_and,
        not_forall] using hout
    · intro T hT
      obtain ⟨j, hj, bound⟩ := estimate T hT
      exact ⟨j, hj, fun z => bound z y (inside hy)⟩

/-! ### Dyadic parameter schedule and budget verification for Lemma 5.4 -/

/-- Bit width `8 * b` of the outer sampler coordinate index at scale `b`. -/
def sourceReductionOuterBits (b : ℕ) : ℕ := 8 * b

/-- Number `2 ^ (8 * b)` of outer coordinates fed to `strictMajority`. -/
def sourceReductionOuterCount (b : ℕ) : ℕ := 2 ^ sourceReductionOuterBits b

/-- Number `2 ^ c` of candidate correlation-breaker calls XORed at each outer coordinate. -/
def sourceReductionCandidateCount (c : ℕ) : ℕ := 2 ^ c

/-- Number `4 * 2^c - 1` of tampered correlation-breaker calls in a degree-4 parity test. -/
def sourceReductionTamperingCount (c : ℕ) : ℕ := 4 * sourceReductionCandidateCount c - 1

/-- Advice bit length `8 * b + c` recording the outer coordinate and candidate index. -/
def sourceReductionAdviceLength (b c : ℕ) : ℕ := sourceReductionOuterBits b + c

/-- Dyadic error exponent `54 * b + c + 10` of the correlation breaker. -/
def sourceReductionTarget (b c : ℕ) : ℕ := 54 * b + c + 10

/-- Test-set density allowance `2 ^ (-5 * b)` for the somewhere sampler. -/
noncomputable def sourceReductionSamplerError (b : ℕ) : ℝ := ((2 : ℝ) ^ (5 * b))⁻¹

/-- Discrepancy threshold `2 ^ (-(17 * b + 10))` defining each bad-seed test. -/
noncomputable def sourceReductionBadThreshold (b : ℕ) : ℝ := ((2 : ℝ) ^ (17 * b + 10))⁻¹

/-- Low-order sign-parity bias bound `2 * 2 ^ (-(17 * b + 10))` outside the bad seeds. -/
noncomputable def sourceReductionParityBias (b : ℕ) : ℝ := 2 * sourceReductionBadThreshold b

theorem sourceReductionOuterCount_pos (b : ℕ) : 0 < sourceReductionOuterCount b := by
  unfold sourceReductionOuterCount
  positivity

theorem sourceReductionCandidateCount_pos (c : ℕ) : 0 < sourceReductionCandidateCount c := by
  unfold sourceReductionCandidateCount
  positivity

theorem sourceReductionTamperingCount_pos (c : ℕ) : 0 < sourceReductionTamperingCount c := by
  have positive := sourceReductionCandidateCount_pos c
  unfold sourceReductionTamperingCount
  omega

theorem sourceReductionTamperingCount_add_one (c : ℕ) :
    sourceReductionTamperingCount c + 1 = 4 * sourceReductionCandidateCount c := by
  have positive := sourceReductionCandidateCount_pos c
  unfold sourceReductionTamperingCount
  omega

theorem sourceReductionSamplerError_pos (b : ℕ) : 0 < sourceReductionSamplerError b := by
  unfold sourceReductionSamplerError
  positivity

theorem sourceReductionBadThreshold_pos (b : ℕ) : 0 < sourceReductionBadThreshold b := by
  unfold sourceReductionBadThreshold
  positivity

theorem sourceReductionParityBias_nonneg (b : ℕ) : 0 ≤ sourceReductionParityBias b := by
  unfold sourceReductionParityBias
  exact mul_nonneg (by norm_num) (sourceReductionBadThreshold_pos b).le

private theorem power_union_budget (a c d : ℕ) :
    (2 : ℝ) ^ a * ((2 : ℝ) ^ (a + c + d))⁻¹ / ((2 : ℝ) ^ c)⁻¹ =
      ((2 : ℝ) ^ d)⁻¹ := by
  rw [pow_add, pow_add]
  field_simp

/-- **Bad-seed union budget:** `(2^(8b))^4 * 2^c * (2^(-(54b + c + 10)) / 2^(-(17b + 10))) =
2^(-5b)`. -/
theorem sourceReduction_union_budget (b c : ℕ) :
    (sourceReductionOuterCount b : ℝ) ^ 4 * sourceReductionCandidateCount c *
      (((2 : ℝ) ^ sourceReductionTarget b c)⁻¹ / sourceReductionBadThreshold b) =
        sourceReductionSamplerError b := by
  simp only [sourceReductionOuterCount, sourceReductionOuterBits,
    sourceReductionCandidateCount, sourceReductionTarget, sourceReductionBadThreshold,
    sourceReductionSamplerError, Nat.cast_pow, Nat.cast_ofNat]
  rw [← pow_mul, ← pow_add]
  have exponent : 54 * b + c + 10 = (8 * b * 4 + c) + (17 * b + 10) + 5 * b := by omega
  rw [exponent]
  simpa only [mul_div_assoc] using
    power_union_budget (8 * b * 4 + c) (17 * b + 10) (5 * b)

private theorem power_moment_budget (b : ℕ) :
    100 * ((2 : ℝ) ^ (8 * b)) ^ 2 * (2 * ((2 : ℝ) ^ (17 * b + 10))⁻¹) ≤ 1 := by
  have denominator : 17 * b + 10 = 8 * b * 2 + b + 10 := by omega
  rw [denominator, pow_add, pow_add, ← pow_mul]
  have one : 1 ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num)
  field_simp
  nlinarith

/-- **Fourth-moment parity-bias budget:** for any `m ≤ 2^(8b)`,
`100 * m^2 * sourceReductionParityBias b ≤ 1`. -/
theorem sourceReduction_moment_budget {b m : ℕ} (size : m ≤ sourceReductionOuterCount b) :
    100 * (m : ℝ) ^ 2 * sourceReductionParityBias b ≤ 1 := by
  have castSize : (m : ℝ) ≤ sourceReductionOuterCount b := by exact_mod_cast size
  have square := pow_le_pow_left₀ (Nat.cast_nonneg m) castSize 2
  calc
    _ ≤ 100 * (sourceReductionOuterCount b : ℝ) ^ 2 * sourceReductionParityBias b :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left square (by norm_num))
        (sourceReductionParityBias_nonneg b)
    _ ≤ 1 := by
      simpa only [sourceReductionOuterCount, sourceReductionOuterBits,
        sourceReductionParityBias, sourceReductionBadThreshold, Nat.cast_pow, Nat.cast_ofNat]
        using power_moment_budget b

/-- The maximum number `2 * ε * D` of discarded outer coordinates at scale `b` equals
`2 ^ (3 * b + 1)`. -/
theorem sourceReduction_bad_count_bound (b : ℕ) :
    2 * sourceReductionSamplerError b * sourceReductionOuterCount b =
      (2 : ℝ) ^ (3 * b + 1) := by
  simp only [sourceReductionSamplerError, sourceReductionOuterCount,
    sourceReductionOuterBits, Nat.cast_pow, Nat.cast_ofNat]
  have exponent : 8 * b = 5 * b + 3 * b := by omega
  rw [exponent, pow_add, pow_add]
  field_simp

private theorem majority_margin {D m B : ℝ} (positive : 0 < D) (nonneg : 0 ≤ m)
    (discarded : 0 ≤ D - m) (bad : D - m ≤ B)
    (half : 2 * B ≤ D) (square : 128 * B ^ 2 ≤ D) :
    0 < m ∧ D - m ≤ Real.sqrt m / 8 := by
  have lower : D / 2 ≤ m := by linarith
  have strict : 0 < m := lt_of_lt_of_le (half_pos positive) lower
  have squared : (8 * (D - m)) ^ 2 ≤ m := by
    have monotone := pow_le_pow_left₀
      (mul_nonneg (show (0 : ℝ) ≤ 8 by norm_num) discarded)
      (mul_le_mul_of_nonneg_left bad (show (0 : ℝ) ≤ 8 by norm_num)) 2
    nlinarith
  have root := (Real.le_sqrt (mul_nonneg (by norm_num) discarded) nonneg).mpr squared
  exact ⟨strict, by linarith⟩

/-- **Majority-margin guards for `b ≥ 5`:** if at most `2 * ε * D = 2^(3b + 1)` outer coordinates
out of `D = 2^(8b)` are discarded (`b ≥ 5`), then `m > 0` and `D - m ≤ √m / 8`. -/
theorem sourceReduction_majority_guards {b m : ℕ} (large : 5 ≤ b)
    (size : m ≤ sourceReductionOuterCount b)
    (bad : ((sourceReductionOuterCount b - m : ℕ) : ℝ) ≤
      2 * sourceReductionSamplerError b * sourceReductionOuterCount b) :
    0 < m ∧ ((sourceReductionOuterCount b - m : ℕ) : ℝ) ≤ Real.sqrt (m : ℝ) / 8 := by
  rw [sourceReduction_bad_count_bound, Nat.cast_sub size] at bad
  have half : 2 * (2 : ℝ) ^ (3 * b + 1) ≤ (2 : ℝ) ^ (8 * b) := by
    calc
      _ = (2 : ℝ) ^ (3 * b + 2) := by
        rw [show 3 * b + 2 = (3 * b + 1) + 1 by omega]
        exact (pow_succ' _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have square : 128 * ((2 : ℝ) ^ (3 * b + 1)) ^ 2 ≤ (2 : ℝ) ^ (8 * b) := by
    calc
      _ = (2 : ℝ) ^ (6 * b + 9) := by
        rw [← pow_mul, show 6 * b + 9 = 7 + (3 * b + 1) * 2 by omega, pow_add]
        norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have castCount : (sourceReductionOuterCount b : ℝ) = (2 : ℝ) ^ (8 * b) := by
    simp only [sourceReductionOuterCount, sourceReductionOuterBits, Nat.cast_pow, Nat.cast_ofNat]
  have result := majority_margin (D := (sourceReductionOuterCount b : ℝ))
    (m := (m : ℝ)) (B := (2 : ℝ) ^ (3 * b + 1))
    (by exact_mod_cast sourceReductionOuterCount_pos b) (Nat.cast_nonneg m)
    (sub_nonneg.mpr (by exact_mod_cast size)) bad
    (by rwa [castCount]) (by rwa [castCount])
  refine ⟨by exact_mod_cast result.1, ?_⟩
  simpa only [Nat.cast_sub size] using result.2

/-! ### End-to-end conditional sumset bias for `strictMajority ∘ affineSourceReduction` -/

/-- **End-to-end conditional sumset bias `35 / 72` for `strictMajority ∘ affineSourceReduction` at
scale `b ≥ 5`:** if `sampler` is a `(K, 2^(-5b), 1 / 2)`-somewhere sampler and for every pair of
flat sources `P, Q` of size at least `K > 0`, a bad-seed family `bad P Q` of density at most
`2^(-(54b + c + 10)) / 2^(-(17b + 10))` witnesses candidate-product parity bias at most
`sourceReductionParityBias b` on `x + y`, then
`fun z => strictMajority (sourceReductionOuterCount b) (affineSourceReduction cb sampler advice z)`
has `SumsetBias` at most `35 / 72` above threshold `K`. -/
theorem sumsetBias_strictMajority_affineSourceReduction
    {G Seed Advice : Type*} [Add G] [Fintype G] [Fintype Seed]
    {b c K : ℕ} (hb : 5 ≤ b) (hK : 0 < K)
    (cb : G → Seed → Advice → Bool)
    (sampler : G → Fin (sourceReductionOuterCount b) → Fin (sourceReductionCandidateCount c) → Seed)
    (advice : Fin (sourceReductionOuterCount b) → Fin (sourceReductionCandidateCount c) → Advice)
    (hSampler : SomewhereSampler sampler K (sourceReductionSamplerError b) (1 / 2))
    (bad : Finset G → Finset G → Finset (Fin (sourceReductionOuterCount b)) →
      Fin (sourceReductionCandidateCount c) → Finset Seed)
    (hBadCard : ∀ P Q : Finset G, K ≤ P.card → K ≤ Q.card →
      ∀ U ∈ parityTests (Fin (sourceReductionOuterCount b)) 4,
      ∀ z : Fin (sourceReductionCandidateCount c),
        ((bad P Q U z).card : ℝ) ≤
          (((2 : ℝ) ^ sourceReductionTarget b c)⁻¹ / sourceReductionBadThreshold b) *
            Fintype.card Seed)
    (hEstimate : ∀ P Q : Finset G, K ≤ P.card → K ≤ Q.card →
      ∀ U ∈ parityTests (Fin (sourceReductionOuterCount b)) 4,
      ∃ j ∈ U, ∀ z : Fin (sourceReductionCandidateCount c), ∀ y ∈ Q,
        sampler y j z ∉ bad P Q U z →
          |weightedMean P (fun _ => 1 / (P.card : ℝ)) (fun x =>
            ∏ i ∈ U, ∏ r : Fin (sourceReductionCandidateCount c),
              if cb (x + y) (sampler (x + y) i r) (advice i r) then (1 : ℝ) else -1)| ≤
            sourceReductionParityBias b) :
    SumsetBias
      {z | strictMajority (sourceReductionOuterCount b)
        (affineSourceReduction cb sampler advice z) = true} K (35 / 72) := by
  refine strictMajority_sumsetBias_of_parity_fibers
    (affineSourceReduction cb sampler advice) hK (sourceReductionParityBias_nonneg b) ?_
  intro P Q hP hQ
  let η : ℝ := ((2 : ℝ) ^ sourceReductionTarget b c)⁻¹ / sourceReductionBadThreshold b
  have hη : 0 ≤ η := by
    dsimp only [η]
    exact div_nonneg (by positivity) (sourceReductionBadThreshold_pos b).le
  have hbudget :
      (sourceReductionOuterCount b : ℝ) ^ 4 *
        Fintype.card (Fin (sourceReductionCandidateCount c)) * η ≤
          sourceReductionSamplerError b := by
    rw [Fintype.card_fin]
    exact (sourceReduction_union_budget b c).le
  have hest : ∀ U ∈ parityTests (Fin (sourceReductionOuterCount b)) 4,
      ∃ j ∈ U, ∀ z : Fin (sourceReductionCandidateCount c), ∀ y ∈ Q,
        sampler y j z ∉ bad P Q U z →
          |weightedMean P (fun _ => 1 / (P.card : ℝ)) (fun x =>
            ∏ i ∈ U,
              if affineSourceReduction cb sampler advice (x + y) i then (1 : ℝ) else -1)| ≤
            sourceReductionParityBias b := by
    intro U hU
    obtain ⟨j, hj, hbound⟩ := hEstimate P Q hP hQ U hU
    refine ⟨j, hj, fun z y hy hnot => ?_⟩
    rw [affineSourceReduction_parity_bias_eq cb sampler advice P
      (fun _ => 1 / (P.card : ℝ)) (fun x => x + y) U]
    exact hbound z y hy hnot
  obtain ⟨Good, inside, many, hfib⟩ :=
    hSampler.parity_fibers
      (fun x y i => if affineSourceReduction cb sampler advice (x + y) i then (1 : ℝ) else -1)
      Q (hK.trans_le hQ) (by exact_mod_cast hQ) (bad P Q) hη (hBadCard P Q hP hQ) hbudget hest
  refine ⟨Good, inside, by linarith, fun y hy => ?_⟩
  obtain ⟨m, good, hdisc, hbias⟩ := hfib y hy
  have hm_le : m ≤ sourceReductionOuterCount b := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding good
  have hguards := sourceReduction_majority_guards hb hm_le hdisc
  exact ⟨m, good, hguards.1, sourceReduction_moment_budget hm_le, hbias, hguards.2⟩

/-- **Conditional `SumsetDisperser` for `strictMajority ∘ affineSourceReduction` at scale `b ≥ 5`:**
under the hypotheses of `sumsetBias_strictMajority_affineSourceReduction`, since `35 / 72 < 1 / 2`,
the support `{z | strictMajority (sourceReductionOuterCount b) (affineSourceReduction cb sampler
advice z) = true}` is a `SumsetDisperser` at threshold `K`. -/
theorem sumsetDisperser_strictMajority_affineSourceReduction
    {G Seed Advice : Type*} [Add G] [Fintype G] [Fintype Seed]
    {b c K : ℕ} (hb : 5 ≤ b) (hK : 0 < K)
    (cb : G → Seed → Advice → Bool)
    (sampler : G → Fin (sourceReductionOuterCount b) → Fin (sourceReductionCandidateCount c) → Seed)
    (advice : Fin (sourceReductionOuterCount b) → Fin (sourceReductionCandidateCount c) → Advice)
    (hSampler : SomewhereSampler sampler K (sourceReductionSamplerError b) (1 / 2))
    (bad : Finset G → Finset G → Finset (Fin (sourceReductionOuterCount b)) →
      Fin (sourceReductionCandidateCount c) → Finset Seed)
    (hBadCard : ∀ P Q : Finset G, K ≤ P.card → K ≤ Q.card →
      ∀ U ∈ parityTests (Fin (sourceReductionOuterCount b)) 4,
      ∀ z : Fin (sourceReductionCandidateCount c),
        ((bad P Q U z).card : ℝ) ≤
          (((2 : ℝ) ^ sourceReductionTarget b c)⁻¹ / sourceReductionBadThreshold b) *
            Fintype.card Seed)
    (hEstimate : ∀ P Q : Finset G, K ≤ P.card → K ≤ Q.card →
      ∀ U ∈ parityTests (Fin (sourceReductionOuterCount b)) 4,
      ∃ j ∈ U, ∀ z : Fin (sourceReductionCandidateCount c), ∀ y ∈ Q,
        sampler y j z ∉ bad P Q U z →
          |weightedMean P (fun _ => 1 / (P.card : ℝ)) (fun x =>
            ∏ i ∈ U, ∏ r : Fin (sourceReductionCandidateCount c),
              if cb (x + y) (sampler (x + y) i r) (advice i r) then (1 : ℝ) else -1)| ≤
            sourceReductionParityBias b) :
    SumsetDisperser
      {z | strictMajority (sourceReductionOuterCount b)
        (affineSourceReduction cb sampler advice z) = true} K :=
  (sumsetBias_strictMajority_affineSourceReduction hb hK cb sampler advice hSampler bad hBadCard
    hEstimate).sumsetDisperser hK (by norm_num)

end Cslib.Circuits.Frontier
