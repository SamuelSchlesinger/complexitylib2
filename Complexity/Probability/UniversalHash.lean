/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Collision
public import Complexity.Probability.HashFamily
public import Complexity.Probability.StatisticalDistance
import Complexity.Probability.PMF.Map
import Complexity.Probability.PMF.Expect

/-!
# Universal hashing and the leftover hash lemma

A two-universal hash family has collision probability at most `1 / |Output|` on every pair of
distinct inputs. The seed is independent of the source and remains part of the output. The
leftover hash lemma compares this joint output to the same seed with an independent uniform value.

The statements allow any finite seed distribution satisfying the collision bound. They are
information-theoretic results; efficient sampling and evaluation require separate certificates.

## Main definitions

* `Cslib.Probability.IsTwoUniversal`: a pairwise collision bound for a sampled hash seed.
* `Cslib.Probability.seededHash`: reveal the independent hash seed and its digest together.

## Main results

* `Cslib.Probability.isTwoUniversal_iff_isUniversalHash`: two-universality is
  `1 / |Output|`-universality.
* `Cslib.Probability.IsTwoUniversal.collision_with_set_le`: isolation by a union bound.
* `Cslib.Probability.IsTwoUniversal.leftover_hash`: the strong leftover hash lemma.
* `Cslib.Probability.IsTwoUniversal.leftover_hash_conditional`: extraction with side information.

## References

* [T. Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*][Holenstein2006], Section 3.3, Lemma 1.
  Its collision argument generalizes from field hashing and uniform seeds to any seed
  distribution satisfying the two-universality bound.
* [I. Haitner, S. Vadhan, *The Many Entropies in One-Way Functions*][HaitnerVadhan2017],
  Section 2.4.1, Definition 4 and Lemma 8.

Adapted from Probability/UniversalHash.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the upstream finite-PMF distance.

-/

@[expose] public section

namespace Cslib.Probability

open Cslib.Probability.PMF
open scoped ENNReal

variable {Seed Input Output : Type*} [Fintype Seed] [Finite Input] [Fintype Output]

open Classical in
/-- Distinct inputs collide with probability at most the reciprocal output-space size. -/
def IsTwoUniversal (seed : PMF Seed) (hash : Seed → Input → Output) : Prop :=
  ∀ x y, x ≠ y → (∑ s, if hash s x = hash s y then (seed s).toReal else 0) ≤
    (Fintype.card Output : ℝ)⁻¹

omit [Finite Input] in
open Classical in
/-- Two-universality is `1 / |Output|`-universality in the sense of
`Cslib.Probability.IsUniversalHash`. -/
theorem isTwoUniversal_iff_isUniversalHash [Nonempty Output] {seed : PMF Seed}
    {hash : Seed → Input → Output} :
    IsTwoUniversal seed hash ↔ IsUniversalHash seed hash (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  have hinv : ((Fintype.card Output : ℝ≥0∞)⁻¹).toReal = (Fintype.card Output : ℝ)⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  refine ⟨fun hhash => ?_, fun hhash x y hxy => ?_⟩
  · have h := IsUniversalHash.of_sum_ite_toReal_le (seed := seed) (hash := hash) hhash
    rwa [ENNReal.ofReal_inv_of_pos (by exact_mod_cast Fintype.card_pos),
      ENNReal.ofReal_natCast] at h
  · rw [← hinv]
    exact hhash.sum_ite_toReal_le
      (ENNReal.inv_ne_top.mpr (by exact_mod_cast Fintype.card_ne_zero)) hxy

omit [Finite Input] in
/-- An injective input representation preserves two-universality. -/
theorem IsTwoUniversal.precompose {Input' : Type*}
    {seed : PMF Seed} {hash : Seed → Input → Output}
    (hhash : IsTwoUniversal seed hash) {encode : Input' → Input}
    (hinjective : Function.Injective encode) :
    IsTwoUniversal seed (fun key value => hash key (encode value)) :=
  fun _ _ hne => hhash _ _ (fun heq => hne (hinjective heq))

/-- Hash a source using an independent seed and reveal both the seed and the hash value. -/
noncomputable def seededHash (seed : PMF Seed) (source : PMF Input)
    (hash : Seed → Input → Output) : PMF (Seed × Output) :=
  seed.bind (fun s => source.map (fun x => (s, hash s x)))

omit [Fintype Seed] [Finite Input] [Fintype Output] in
/-- The independent source and public seed can be sampled in either order. -/
theorem seededHash_eq_bind (seed : PMF Seed) (source : PMF Input)
    (hash : Seed → Input → Output) :
    seededHash seed source hash = source.bind (fun x => seed.map (fun s => (s, hash s x))) := by
  simpa only [seededHash, PMF.map, Function.comp_def] using
    PMF.bind_comm seed source (fun s x => PMF.pure (s, hash s x))

omit [Finite Input] in
/-- Applying a shared public hash seed cannot increase distance between source distributions. -/
theorem dist_seededHash_le [Fintype Input] (seed : PMF Seed) (p q : PMF Input)
    (hash : Seed → Input → Output) :
    dist (seededHash seed p hash) (seededHash seed q hash) ≤ dist p q := by
  rw [seededHash_eq_bind, seededHash_eq_bind]
  exact dist_bind_le p q _

omit [Fintype Seed] [Finite Input] in
/-- An empty digest is already uniform. This exact case avoids charging an extraction error
when the source has too little entropy to supply even one prefix bit. -/
theorem seededHash_eq_uniform_of_subsingleton [Subsingleton Output] [Nonempty Output]
    (seed : PMF Seed) (source : PMF Input) (hash : Seed → Input → Output) :
    seededHash seed source hash =
      seed.bind (fun s => (PMF.uniformOfFintype Output).map (s, ·)) := by
  apply PMF.map_injective (f := Prod.fst)
    (fun _ _ h => Prod.ext h (Subsingleton.elim _ _))
  simp [seededHash, Function.comp_def, PMF.map, PMF.bind_const]

omit [Finite Input] in
/-- Re-encoding a seed preserves universality when its distribution is pushed forward. -/
theorem IsTwoUniversal.precompose_seed {Seed' : Type*} [Fintype Seed']
    (seed : PMF Seed') (prepare : Seed' → Seed) {hash : Seed → Input → Output}
    (hhash : IsTwoUniversal (seed.map prepare) hash) :
    IsTwoUniversal seed (fun s => hash (prepare s)) := by
  classical
  intro x y hxy
  have h := sum_map_mul seed prepare (fun s => if hash s x = hash s y then (1 : ℝ) else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [← h]
  exact hhash x y hxy

omit [Finite Input] in
open Classical in
/-- A hash fails to isolate a fixed input from a candidate set only if one of the other
candidates collides with it. Two-universality and the union bound control this probability. -/
theorem IsTwoUniversal.collision_with_set_le {seed : PMF Seed}
    {hash : Seed → Input → Output} (hhash : IsTwoUniversal seed hash)
    (candidates : Finset Input) (x : Input) :
    (∑ s, if ∃ y ∈ candidates, y ≠ x ∧ hash s y = hash s x then (seed s).toReal else 0) ≤
      ((candidates.erase x).card : ℝ) / Fintype.card Output := by
  have hpoint (s : Seed) :
      (if ∃ y ∈ candidates, y ≠ x ∧ hash s y = hash s x then (seed s).toReal else 0) ≤
        ∑ y ∈ candidates.erase x, if hash s y = hash s x then (seed s).toReal else 0 := by
    split_ifs with h
    · obtain ⟨y, hy, hyx, heq⟩ := h
      have hsum := Finset.single_le_sum (s := candidates.erase x) (a := y)
        (f := fun y => if hash s y = hash s x then (seed s).toReal else 0)
        (fun _ _ => by positivity) (Finset.mem_erase.mpr ⟨hyx, hy⟩)
      simpa only [heq, ite_true] using hsum
    · exact Finset.sum_nonneg (fun _ _ => by positivity)
  calc
    _ ≤ ∑ s, ∑ y ∈ candidates.erase x,
        if hash s y = hash s x then (seed s).toReal else 0 :=
      Finset.sum_le_sum (fun s _ => hpoint s)
    _ = ∑ y ∈ candidates.erase x, ∑ s,
        if hash s y = hash s x then (seed s).toReal else 0 := Finset.sum_comm
    _ ≤ ∑ _y ∈ candidates.erase x, (Fintype.card Output : ℝ)⁻¹ :=
      Finset.sum_le_sum (fun y hy => hhash y x (Finset.mem_erase.mp hy).1)
    _ = _ := by simp [div_eq_mul_inv]

/-- Two-universality bounds the average collision probability of the hashed source. -/
theorem IsTwoUniversal.collisionProbability_le {seed : PMF Seed}
    {hash : Seed → Input → Output} (hhash : IsTwoUniversal seed hash) (source : PMF Input) :
    ∑ s, (seed s).toReal * collisionProbability (source.map (hash s)) ≤
      collisionProbability source + (Fintype.card Output : ℝ)⁻¹ := by
  classical
  let := Fintype.ofFinite Input
  have hpair (x y : Input) :
      (∑ s, if hash s x = hash s y then (seed s).toReal else 0) ≤
        (if x = y then (1 : ℝ) else 0) + (Fintype.card Output : ℝ)⁻¹ := by
    by_cases hxy : x = y
    · subst y
      simp only [ite_true, sum_toReal]
      exact le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _))
    · simpa [hxy] using hhash x y hxy
  calc
    _ = ∑ x, ∑ y, (source x).toReal * (source y).toReal *
        (∑ s, if hash s x = hash s y then (seed s).toReal else 0) := by
      simp only [collisionProbability_map, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
      simp [mul_ite, ite_mul, mul_comm]
    _ ≤ ∑ x, ∑ y, (source x).toReal * (source y).toReal *
        ((if x = y then (1 : ℝ) else 0) + (Fintype.card Output : ℝ)⁻¹) := by
      gcongr with x _ y _
      exact hpair x y
    _ = collisionProbability source + (Fintype.card Output : ℝ)⁻¹ := by
      simp [mul_add, Finset.sum_add_distrib, mul_ite, ← Finset.sum_mul, ← Finset.mul_sum,
        sum_toReal, collisionProbability_eq_sum, sq]

/-- The strong leftover hash lemma, in squared form without logarithms or square roots. -/
theorem IsTwoUniversal.leftover_hash_sq [Nonempty Output] {seed : PMF Seed}
    {hash : Seed → Input → Output} (hhash : IsTwoUniversal seed hash) (source : PMF Input) :
    4 * dist (seededHash seed source hash)
        (seed.bind (fun s => (PMF.uniformOfFintype Output).map (s, ·))) ^ 2 ≤
      Fintype.card Output * collisionProbability source := by
  have hcard : (Fintype.card Output : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsq := dist_bind_pair_sq_le seed (fun s => source.map (hash s))
    (fun _ => PMF.uniformOfFintype Output)
  have hbound : ∑ s, (seed s).toReal *
      (4 * dist (source.map (hash s)) (PMF.uniformOfFintype Output) ^ 2) ≤
      Fintype.card Output * collisionProbability source := by
    calc
      _ ≤ ∑ s, (seed s).toReal *
          (Fintype.card Output * collisionProbability (source.map (hash s)) - 1) := by
        gcongr with s _
        exact dist_uniform_sq_le _
      _ = Fintype.card Output *
          (∑ s, (seed s).toReal * collisionProbability (source.map (hash s))) - 1 := by
        simp only [mul_sub, mul_one, Finset.sum_sub_distrib, sum_toReal,
          Finset.mul_sum, mul_left_comm]
      _ ≤ Fintype.card Output *
          (collisionProbability source + (Fintype.card Output : ℝ)⁻¹) - 1 := by
        gcongr
        exact hhash.collisionProbability_le source
      _ = _ := by field_simp; ring
  have hdistrib : (∑ s, (seed s).toReal *
      (4 * dist (source.map (hash s)) (PMF.uniformOfFintype Output) ^ 2)) =
      4 * ∑ s, (seed s).toReal *
        dist (source.map (hash s)) (PMF.uniformOfFintype Output) ^ 2 := by
    simp only [Finset.mul_sum, mul_left_comm]
  rw [hdistrib] at hbound
  simpa only [seededHash, PMF.map_comp, Function.comp_def] using
    (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 4)).trans hbound

/-- The strong leftover hash lemma: the seed stays public and independent uniform bits replace
the hash value, with error at most half the square root of output size times source collision. -/
theorem IsTwoUniversal.leftover_hash [Nonempty Output] {seed : PMF Seed}
    {hash : Seed → Input → Output} (hhash : IsTwoUniversal seed hash) (source : PMF Input) :
    dist (seededHash seed source hash)
        (seed.bind (fun s => (PMF.uniformOfFintype Output).map (s, ·))) ≤
      Real.sqrt (Fintype.card Output * collisionProbability source) / 2 := by
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  apply Real.le_sqrt_of_sq_le
  nlinarith [hhash.leftover_hash_sq source]

/-- A pointwise probability bound is sufficient for the leftover hash lemma. This is the
min-entropy form: use `mass = 2⁻ᵏ` for a source with at least `k` bits of min-entropy. -/
theorem IsTwoUniversal.leftover_hash_of_mass_le [Nonempty Output] {seed : PMF Seed}
    {hash : Seed → Input → Output} (hhash : IsTwoUniversal seed hash) (source : PMF Input)
    {mass : ℝ} (hmass : ∀ x, (source x).toReal ≤ mass) :
    dist (seededHash seed source hash)
        (seed.bind (fun s => (PMF.uniformOfFintype Output).map (s, ·))) ≤
      Real.sqrt (Fintype.card Output * mass) / 2 := by
  exact (hhash.leftover_hash source).trans (div_le_div_of_nonneg_right
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
      (collisionProbability_le_of_mass_le source hmass) (Nat.cast_nonneg _))) (by norm_num))

/-- Revealing side information costs the average collision probability of the conditional
sources. The hash seed is sampled independently of both the side information and the source. -/
theorem IsTwoUniversal.leftover_hash_conditional_sq [Nonempty Output]
    {Side : Type*} [Fintype Side] {seed : PMF Seed} {hash : Seed → Input → Output}
    (hhash : IsTwoUniversal seed hash) (side : PMF Side) (source : Side → PMF Input) :
    4 * dist
        (side.bind (fun info => (seededHash seed (source info) hash).map (info, ·)))
        (side.bind (fun info => (seed.bind
          (fun s => (PMF.uniformOfFintype Output).map (s, ·))).map (info, ·))) ^ 2 ≤
      Fintype.card Output * ∑ info, (side info).toReal * collisionProbability (source info) := by
  calc
    _ ≤ 4 * ∑ info, (side info).toReal * dist (seededHash seed (source info) hash)
        (seed.bind (fun s => (PMF.uniformOfFintype Output).map (s, ·))) ^ 2 :=
      mul_le_mul_of_nonneg_left (dist_bind_pair_sq_le _ _ _) (by norm_num)
    _ = ∑ info, (side info).toReal * (4 * dist (seededHash seed (source info) hash)
        (seed.bind (fun s => (PMF.uniformOfFintype Output).map (s, ·))) ^ 2) := by
      simp only [Finset.mul_sum, mul_left_comm]
    _ ≤ ∑ info, (side info).toReal *
        (Fintype.card Output * collisionProbability (source info)) := by
      apply Finset.sum_le_sum
      intro info _
      exact mul_le_mul_of_nonneg_left (hhash.leftover_hash_sq _) ENNReal.toReal_nonneg
    _ = _ := by simp only [Finset.mul_sum, mul_left_comm]

/-- Conditional leftover hashing in its usual square-root form. -/
theorem IsTwoUniversal.leftover_hash_conditional [Nonempty Output]
    {Side : Type*} [Fintype Side] {seed : PMF Seed} {hash : Seed → Input → Output}
    (hhash : IsTwoUniversal seed hash) (side : PMF Side) (source : Side → PMF Input) :
    dist (side.bind (fun info => (seededHash seed (source info) hash).map (info, ·)))
        (side.bind (fun info => (seed.bind
          (fun s => (PMF.uniformOfFintype Output).map (s, ·))).map (info, ·))) ≤
      Real.sqrt (Fintype.card Output *
        ∑ info, (side info).toReal * collisionProbability (source info)) / 2 := by
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  apply Real.le_sqrt_of_sq_le
  nlinarith [hhash.leftover_hash_conditional_sq side source]

end Cslib.Probability
