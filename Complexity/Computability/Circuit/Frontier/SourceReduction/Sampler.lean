/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite seeded extractors, samplers, and somewhere-sampler amplification

In [Chattopadhyay and Liao][ChattopadhyayLiao2022] (Definitions 3.14 and 3.16, and Appendix A), a
seeded extractor `E : α → Seed → Ω` acts as an averaging sampler for small output tests `T ⊆ Ω`,
and composing `E` with a neighbor generator `Γ : Outer → Candidate → Base` satisfying
`NeighborCoverage` amplifies `E` into a `SomewhereSampler` whose outer seed fails at `y` only when
every candidate `z` lands in `T`.

This module develops the finite combinatorial theory of:
1. **Seeded extractors to samplers (`FlatSeededExtractor.card_badInputs_lt`,
   `FlatSeededExtractor.sampler`):** if `E` extracts from flat sources of size `K` with error `ε`,
   at most `K - 1` inputs can hit a test `T` of density `≤ ε` on more than a `2 ε` fraction of
   seeds, so any source with point masses `≤ 1 / L` places at most `δ` mass on `badInputs E T ε`
   whenever `K ≤ δ L`.
2. **Neighbor coverage and somewhere-sampler amplification (`NeighborCoverage.card_allHitSeeds_lt`,
   `FlatSeededExtractor.neighborCoverage`, `Sampler.amplify`):** composing a base sampler `E` with a
   neighbor map `Γ` whose `K`-sets cover at least a `ρ > 2 ε₀` fraction of base seeds yields a
   `SomewhereSampler` whenever `K ≤ 2 ε |Outer|`.
3. **Unconditional seed projections (`sampler_seedProjection`,
   `neighborCoverage_seedProjection`, `somewhereSampler_seedProjection`):** trivial seed-projection
   realizations demonstrating that all three interfaces are non-vacuously satisfiable with zero
   failure probability.

## Main definitions

* `Cslib.Circuits.Frontier.seedHits`, `Cslib.Circuits.Frontier.badInputs`: seed-hit count and bad
  input set for a sampler `E : α → Seed → Ω`.
* `Cslib.Circuits.Frontier.FlatSeededExtractor`: flat-source seeded extraction without division.
* `Cslib.Circuits.Frontier.Sampler`: small-set sampler for weak sources of min-entropy `≥ log₂ L`.
* `Cslib.Circuits.Frontier.neighborSet`, `Cslib.Circuits.Frontier.NeighborCoverage`: base-seed
  neighborhood and expansion lower bound for `Γ : Outer → Candidate → Base`.
* `Cslib.Circuits.Frontier.allHitSeeds`, `Cslib.Circuits.Frontier.somewhereBadInputs`,
  `Cslib.Circuits.Frontier.SomewhereSampler`: somewhere-sampler failure events and contract.

## Main results

* `Cslib.Circuits.Frontier.FlatSeededExtractor.card_badInputs_lt`,
  `Cslib.Circuits.Frontier.FlatSeededExtractor.sampler`: Zuckerman's seeded-extractor-to-sampler
  conversion.
* `Cslib.Circuits.Frontier.FlatSeededExtractor.neighborCoverage`: any flat seeded extractor yields
  neighbor coverage `1 - ε`.
* `Cslib.Circuits.Frontier.NeighborCoverage.card_allHitSeeds_lt`,
  `Cslib.Circuits.Frontier.Sampler.amplify`: somewhere-sampler amplification via neighbor coverage.
* `Cslib.Circuits.Frontier.sampler_seedProjection`,
  `Cslib.Circuits.Frontier.neighborCoverage_seedProjection`,
  `Cslib.Circuits.Frontier.somewhereSampler_seedProjection`: unconditional non-vacuity witnesses.

## References

* [E. Chattopadhyay and J.-J. Liao, *Extractors for Sum of Two Sources*][ChattopadhyayLiao2022]
* [E. Chattopadhyay, D. Zuckerman, *Explicit Two-Source Extractors*][ChattopadhyayZuckerman2019]
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

/-! ### Seeded extractors and averaging samplers -/

open Classical in
/-- Number of seeds `y : Seed` whose output `E x y` belongs to the test set `T`, at input `x`. -/
noncomputable def seedHits {α Seed Ω : Type*} [Fintype Seed]
    (E : α → Seed → Ω) (T : Finset Ω) (x : α) : ℕ :=
  (Finset.univ.filter fun y => E x y ∈ T).card

open Classical in
/-- Inputs `x : α` for which more than a `2 ε` fraction of seeds hit the test set `T`. -/
noncomputable def badInputs {α Seed Ω : Type*} [Fintype α] [Fintype Seed]
    (E : α → Seed → Ω) (T : Finset Ω) (ε : ℝ) : Finset α :=
  Finset.univ.filter fun x => 2 * ε * Fintype.card Seed < (seedHits E T x : ℝ)

/-- Seeded extraction from every uniform support `P : Finset α` of size at least `K`, with error
`ε`, stated without division by clearing `|P| * |Seed| * |Ω|`. -/
def FlatSeededExtractor {α Seed Ω : Type*} [Fintype Seed] [Fintype Ω]
    (E : α → Seed → Ω) (K : ℕ) (ε : ℝ) : Prop :=
  ∀ P : Finset α, K ≤ P.card → ∀ T : Finset Ω,
    |(∑ x ∈ P, (seedHits E T x : ℝ)) * Fintype.card Ω -
      (P.card : ℝ) * Fintype.card Seed * T.card| ≤
        ε * P.card * Fintype.card Seed * Fintype.card Ω

/-- Small-set sampling for every probability distribution `p` on `α` with point masses at most
`1 / L` (written `L * p x ≤ 1`): for every test `T` of density at most `ε`, the `p`-mass of
`badInputs E T ε` is at most `δ`. -/
def Sampler {α Seed Ω : Type*} [Fintype α] [Fintype Seed] [Fintype Ω]
    (E : α → Seed → Ω) (L ε δ : ℝ) : Prop :=
  ∀ T : Finset Ω, (T.card : ℝ) ≤ ε * Fintype.card Ω →
    ∀ p : α → ℝ, (∀ x, 0 ≤ p x) → (∑ x, p x) = 1 →
      (∀ x, L * p x ≤ 1) → ∑ x ∈ badInputs E T ε, p x ≤ δ

/-- **Bounded bad-input count for a flat seeded extractor:** fewer than `K` inputs can hit a test
`T` of density at most `ε` on more than a `2 ε` fraction of seeds. -/
theorem FlatSeededExtractor.card_badInputs_lt {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω]
    {E : α → Seed → Ω} {K : ℕ} {ε : ℝ}
    (extract : FlatSeededExtractor E K ε) (positive : 0 < K)
    (T : Finset Ω) (small : (T.card : ℝ) ≤ ε * Fintype.card Ω) :
    (badInputs E T ε).card < K := by
  classical
  by_contra hn
  have hK : K ≤ (badInputs E T ε).card := by omega
  have hne : (badInputs E T ε).Nonempty :=
    Finset.card_pos.mp (positive.trans_le hK)
  have hseed : (0 : ℝ) < Fintype.card Seed := by exact_mod_cast Fintype.card_pos
  have hout : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hlower : (badInputs E T ε).card * (2 * ε * Fintype.card Seed) <
      ∑ x ∈ badInputs E T ε, (seedHits E T x : ℝ) := by
    simpa using Finset.sum_lt_sum_of_nonempty hne (fun x hx =>
      (Finset.mem_filter.mp hx).2)
  have hupper := (abs_le.mp (extract (badInputs E T ε) hK T)).2
  have hscale := mul_le_mul_of_nonneg_left small
    (mul_nonneg (Nat.cast_nonneg (badInputs E T ε).card) hseed.le)
  have hstrict := mul_lt_mul_of_pos_right hlower hout
  nlinarith

/-- **Zuckerman's extractor-to-sampler conversion:** a flat `(K, ε)`-seeded extractor is an
`(L, ε, δ)`-sampler whenever `K ≤ δ * L`. -/
theorem FlatSeededExtractor.sampler {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω]
    {E : α → Seed → Ω} {K : ℕ} {L ε δ : ℝ}
    (extract : FlatSeededExtractor E K ε) (positive : 0 < K)
    (source : 0 < L) (budget : (K : ℝ) ≤ δ * L) : Sampler E L ε δ := by
  intro T small p _ _ cap
  have hcard : ((badInputs E T ε).card : ℝ) < K := by
    exact_mod_cast extract.card_badInputs_lt positive T small
  apply le_of_lt
  apply (mul_lt_mul_iff_right₀ source).mp
  calc
    L * (∑ x ∈ badInputs E T ε, p x) =
        ∑ x ∈ badInputs E T ε, L * p x := Finset.mul_sum ..
    _ ≤ ∑ _x ∈ badInputs E T ε, (1 : ℝ) :=
      Finset.sum_le_sum fun x _ => cap x
    _ = (badInputs E T ε).card := by simp
    _ < K := hcard
    _ ≤ L * δ := by simpa only [mul_comm] using budget

open Classical in
/-- On any flat source `P`, the fraction of inputs in `P` that are bad for `T` is at most `δ`
whenever `K ≤ δ * P.card`. -/
theorem FlatSeededExtractor.card_badInputs_inter_le {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω]
    {E : α → Seed → Ω} {K : ℕ} {ε δ : ℝ}
    (extract : FlatSeededExtractor E K ε) (positive : 0 < K)
    (P : Finset α) (budget : (K : ℝ) ≤ δ * P.card)
    (T : Finset Ω) (small : (T.card : ℝ) ≤ ε * Fintype.card Ω) :
    ((P ∩ badInputs E T ε).card : ℝ) ≤ δ * P.card := by
  classical
  have hcard : (P ∩ badInputs E T ε).card < K :=
    (Finset.card_le_card Finset.inter_subset_right).trans_lt
      (extract.card_badInputs_lt positive T small)
  exact (by exact_mod_cast hcard : ((P ∩ badInputs E T ε).card : ℝ) < K).le.trans budget

/-- Seed projection `fun _ y => y` is an `(L, ε, 0)`-sampler for every `ε ≥ 0`. -/
theorem sampler_seedProjection {α Seed : Type*}
    [Fintype α] [Fintype Seed] [Nonempty Seed] {L ε : ℝ} (hε : 0 ≤ ε) :
    Sampler (fun (_ : α) (y : Seed) => y) L ε 0 := by
  classical
  intro T small p _ _ _
  have hseed : (0 : ℝ) < Fintype.card Seed := by exact_mod_cast Fintype.card_pos
  have hbad : badInputs (fun (_ : α) (y : Seed) => y) T ε = ∅ := by
    ext x
    simp only [badInputs, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    have hits : seedHits (fun (_ : α) (y : Seed) => y) T x = T.card := by
      simp [seedHits]
    rw [hits]
    apply not_lt.mpr
    calc
      (T.card : ℝ) ≤ ε * Fintype.card Seed := small
      _ ≤ ε * Fintype.card Seed + ε * Fintype.card Seed :=
        le_add_of_nonneg_right (mul_nonneg hε hseed.le)
      _ = 2 * ε * Fintype.card Seed := by ring
  simp [hbad]

/-! ### Neighbor coverage and somewhere-sampler amplification -/

open Classical in
/-- All base seeds reached from a finite set `P` of outer seeds under
`Γ : Outer → Candidate → Base`. -/
noncomputable def neighborSet {Outer Candidate Base : Type*} [Fintype Candidate]
    (Γ : Outer → Candidate → Base) (P : Finset Outer) : Finset Base :=
  P.biUnion fun y => Finset.univ.image (Γ y)

/-- `NeighborCoverage Γ K ρ` states that every set `P` of at least `K` outer seeds reaches at least
a `ρ` fraction of all base seeds. -/
def NeighborCoverage {Outer Candidate Base : Type*} [Fintype Candidate] [Fintype Base]
    (Γ : Outer → Candidate → Base) (K : ℕ) (ρ : ℝ) : Prop :=
  ∀ P : Finset Outer, K ≤ P.card →
    ρ * Fintype.card Base ≤ ((neighborSet Γ P).card : ℝ)

open Classical in
/-- Outer seeds `y : Outer` for which every candidate `z : Candidate` lands in the test set `T`. -/
noncomputable def allHitSeeds {α Outer Candidate Ω : Type*} [Fintype Outer]
    (S : α → Outer → Candidate → Ω) (T : Finset Ω) (x : α) : Finset Outer :=
  Finset.univ.filter fun y => ∀ z, S x y z ∈ T

open Classical in
/-- Inputs `x : α` for which more than a `2 ε` fraction of outer seeds have all candidates in
`T`. -/
noncomputable def somewhereBadInputs {α Outer Candidate Ω : Type*}
    [Fintype α] [Fintype Outer] (S : α → Outer → Candidate → Ω)
    (T : Finset Ω) (ε : ℝ) : Finset α :=
  Finset.univ.filter fun x => 2 * ε * Fintype.card Outer < ((allHitSeeds S T x).card : ℝ)

/-- Small-set somewhere-sampling with a candidate list at each outer seed, for every probability
distribution `p` on `α` with point masses at most `1 / L`. -/
def SomewhereSampler {α Outer Candidate Ω : Type*}
    [Fintype α] [Fintype Outer] [Fintype Ω]
    (S : α → Outer → Candidate → Ω) (L ε δ : ℝ) : Prop :=
  ∀ T : Finset Ω, (T.card : ℝ) ≤ ε * Fintype.card Ω →
    ∀ p : α → ℝ, (∀ x, 0 ≤ p x) → (∑ x, p x) = 1 →
      (∀ x, L * p x ≤ 1) → ∑ x ∈ somewhereBadInputs S T ε, p x ≤ δ

/-- **Bounded all-hit outer seeds at a good base input:** if `x` hits `T` on at most a `2 ε₀`
fraction of base seeds and `Γ` has `(K, ρ)`-neighbor coverage with `2 ε₀ < ρ`, then fewer than `K`
outer seeds can have all their candidates hit `T`. -/
theorem NeighborCoverage.card_allHitSeeds_lt {α Outer Candidate Base Ω : Type*}
    [Fintype Outer] [Fintype Candidate] [Fintype Base] [Nonempty Base]
    {Γ : Outer → Candidate → Base} {K : ℕ} {ρ ε₀ : ℝ}
    (cover : NeighborCoverage Γ K ρ) (separate : 2 * ε₀ < ρ)
    (E : α → Base → Ω) (T : Finset Ω) (x : α)
    (good : (seedHits E T x : ℝ) ≤ 2 * ε₀ * Fintype.card Base) :
    (allHitSeeds (fun x y z => E x (Γ y z)) T x).card < K := by
  classical
  by_contra hn
  have hK : K ≤ (allHitSeeds (fun x y z => E x (Γ y z)) T x).card := by omega
  have hsub : neighborSet Γ (allHitSeeds (fun x y z => E x (Γ y z)) T x) ⊆
      Finset.univ.filter (fun y => E x y ∈ T) := by
    intro y hy
    obtain ⟨a, ha, hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hy
    simp only [allHitSeeds, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha z⟩
  have hcard : ((neighborSet Γ
      (allHitSeeds (fun x y z => E x (Γ y z)) T x)).card : ℝ) ≤ seedHits E T x := by
    exact_mod_cast Finset.card_le_card hsub
  have hbase : (0 : ℝ) < Fintype.card Base := by exact_mod_cast Fintype.card_pos
  have hupper := (cover _ hK).trans (hcard.trans good)
  exact (not_le_of_gt (mul_lt_mul_of_pos_right separate hbase)) hupper

/-- **Every flat `(K, ε)`-seeded extractor has `(K, 1 - ε)`-neighbor coverage.** -/
theorem FlatSeededExtractor.neighborCoverage {Outer Candidate Base : Type*}
    [Fintype Candidate] [Nonempty Candidate] [Fintype Base]
    {Γ : Outer → Candidate → Base} {K : ℕ} {ε : ℝ}
    (extract : FlatSeededExtractor Γ K ε) (positive : 0 < K) :
    NeighborCoverage Γ K (1 - ε) := by
  classical
  intro P hP
  have hits (y : Outer) (hy : y ∈ P) :
      seedHits Γ (neighborSet Γ P) y = Fintype.card Candidate := by
    have hall : Finset.univ.filter (fun z => Γ y z ∈ neighborSet Γ P) = Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro z _
      exact Finset.mem_biUnion.mpr ⟨y, hy,
        Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩⟩
    simp only [seedHits, hall, Finset.card_univ]
  have hsum : (∑ y ∈ P, (seedHits Γ (neighborSet Γ P) y : ℝ)) =
      (P.card : ℝ) * Fintype.card Candidate := by
    calc
      _ = ∑ _y ∈ P, (Fintype.card Candidate : ℝ) :=
        Finset.sum_congr rfl fun y hy => by rw [hits y hy]
      _ = _ := by simp
  have hdiscrepancy := (abs_le.mp (extract P hP (neighborSet Γ P))).2
  rw [hsum] at hdiscrepancy
  have hp : (0 : ℝ) < P.card := by exact_mod_cast positive.trans_le hP
  have hc : (0 : ℝ) < Fintype.card Candidate := by exact_mod_cast Fintype.card_pos
  apply (mul_le_mul_iff_right₀ (mul_pos hp hc)).mp
  nlinarith [hdiscrepancy]

/-- Every input that is bad for the amplified somewhere-sampler `fun x y z => E x (Γ y z)` is bad
for the base sampler `E`. -/
theorem NeighborCoverage.somewhereBadInputs_subset {α Outer Candidate Base Ω : Type*}
    [Fintype α] [Fintype Outer] [Fintype Candidate] [Fintype Base] [Nonempty Base]
    {Γ : Outer → Candidate → Base} {K : ℕ} {ρ ε₀ ε : ℝ}
    (cover : NeighborCoverage Γ K ρ) (separate : 2 * ε₀ < ρ)
    (budget : (K : ℝ) ≤ 2 * ε * Fintype.card Outer)
    (E : α → Base → Ω) (T : Finset Ω) :
    somewhereBadInputs (fun x y z => E x (Γ y z)) T ε ⊆ badInputs E T ε₀ := by
  classical
  intro x hx
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  by_contra hn
  have hcard : ((allHitSeeds (fun x y z => E x (Γ y z)) T x).card : ℝ) < K := by
    exact_mod_cast cover.card_allHitSeeds_lt separate E T x (le_of_not_gt hn)
  have hbad := (Finset.mem_filter.mp hx).2
  linarith

/-- **Somewhere-sampler amplification (`Sampler.amplify`):** composing an `(L, ε₀, δ)`-sampler `E`
with a `(K, ρ)`-neighbor-covering map `Γ` (`ε ≤ ε₀`, `2 ε₀ < ρ`, `K ≤ 2 ε |Outer|`) produces an
`(L, ε, δ)`-somewhere sampler. -/
theorem Sampler.amplify {α Outer Candidate Base Ω : Type*}
    [Fintype α] [Fintype Outer] [Fintype Candidate] [Fintype Base] [Fintype Ω]
    [Nonempty Base] {E : α → Base → Ω} {Γ : Outer → Candidate → Base}
    {K : ℕ} {L ε₀ ε δ ρ : ℝ}
    (sample : Sampler E L ε₀ δ) (cover : NeighborCoverage Γ K ρ)
    (small : ε ≤ ε₀) (separate : 2 * ε₀ < ρ)
    (budget : (K : ℝ) ≤ 2 * ε * Fintype.card Outer) :
    SomewhereSampler (fun x y z => E x (Γ y z)) L ε δ := by
  intro T hT p hp hmass hcap
  have hTbase : (T.card : ℝ) ≤ ε₀ * Fintype.card Ω :=
    hT.trans (mul_le_mul_of_nonneg_right small (Nat.cast_nonneg _))
  apply le_trans ?_ (sample T hTbase p hp hmass hcap)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (cover.somewhereBadInputs_subset separate budget E T) fun x _ _ => hp x

/-- Candidate projection `fun _ z => z` has `(K, 1)`-neighbor coverage for every `K > 0`. -/
theorem neighborCoverage_seedProjection {Outer Base : Type*} [Fintype Base]
    {K : ℕ} (positive : 0 < K) :
    NeighborCoverage (fun (_ : Outer) (z : Base) => z) K 1 := by
  classical
  intro P hP
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (positive.trans_le hP)
  have hall : neighborSet (fun (_ : Outer) (z : Base) => z) P = Finset.univ := by
    ext z
    constructor
    · intro _
      exact Finset.mem_univ _
    · intro _
      exact Finset.mem_biUnion.mpr ⟨y, hy,
        Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩⟩
  simp [hall]

/-- Candidate projection `fun _ _ z => z` is an `(L, ε, 0)`-somewhere sampler for every
`0 ≤ ε < 1`. -/
theorem somewhereSampler_seedProjection {α Outer Ω : Type*}
    [Fintype α] [Fintype Outer] [Fintype Ω] [Nonempty Ω]
    {L ε : ℝ} (nonneg : 0 ≤ ε) (small : ε < 1) :
    SomewhereSampler (fun (_ : α) (_ : Outer) (z : Ω) => z) L ε 0 := by
  classical
  intro T hT p _ _ _
  have hout : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hnot : ¬ ∀ z : Ω, z ∈ T := by
    intro h
    have hall : T = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    rw [hall, Finset.card_univ] at hT
    have hstrict := mul_lt_mul_of_pos_right small hout
    linarith
  have hits (x : α) :
      allHitSeeds (fun (_ : α) (_ : Outer) (z : Ω) => z) T x = ∅ := by
    simp [allHitSeeds, hnot]
  have hbad : somewhereBadInputs (fun (_ : α) (_ : Outer) (z : Ω) => z) T ε = ∅ := by
    ext x
    simp only [somewhereBadInputs, Finset.mem_filter, Finset.mem_univ, true_and,
      hits, Finset.card_empty, Nat.cast_zero, Finset.notMem_empty, iff_false]
    exact not_lt.mpr (mul_nonneg (mul_nonneg (by norm_num) nonneg) (Nat.cast_nonneg _))
  simp [hbad]

end Cslib.Circuits.Frontier
