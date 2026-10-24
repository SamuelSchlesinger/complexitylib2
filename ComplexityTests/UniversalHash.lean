/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.HashIsolation

/-! Public-seed extraction, nonuniform seeds, empty digests and preimage isolation. -/

namespace ComplexityTests.UniversalHash

open Cslib.Probability Cslib.Probability.PMF

private def xorHash (seed value : Bool) : Bool := value ^^ seed

-- The seed distribution need not be uniform: every individual hash here is injective.
private theorem xor_twoUniversal (seed : PMF Bool) : IsTwoUniversal seed xorHash := by
  intro x y hxy
  cases x <;> cases y <;> simp_all [xorHash]

example : IsTwoUniversal (PMF.pure false) xorHash := xor_twoUniversal _

-- Choosing one of two coordinates is not injective; its collision bound can be tight.
private theorem coord_twoUniversal :
    IsTwoUniversal (PMF.uniformOfFintype Bool)
      (fun key (input : Bool × Bool) => if key then input.1 else input.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ hne
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [Fintype.sum_bool, PMF.uniformOfFintype_apply] at *

example : IsTwoUniversal (PMF.uniformOfFintype Bool)
    (fun key (input : Bool × Bool) => if key then input.1 else input.2) :=
  coord_twoUniversal

open scoped BigOperators in
example : (𝔼 key : Bool,
    if (if key then (false, false).1 else (false, false).2) =
        (if key then (true, false).1 else (true, false).2)
      then (1 : ℝ) else 0) ≤ (Fintype.card Bool : ℝ)⁻¹ :=
  coord_twoUniversal.expect_boole_le (by decide)

example : (∑ key : Bool,
    if (if key then (false, false).1 else (false, false).2) =
        (if key then (true, false).1 else (true, false).2)
      then (PMF.uniformOfFintype Bool key).toReal else 0) = (1 / 2 : ℝ) := by
  norm_num [Fintype.sum_bool, PMF.uniformOfFintype_apply]

-- A uniform source remains exactly uniform even with this maximally biased public seed.
example : seededHash (PMF.pure false) (PMF.uniformOfFintype Bool) xorHash =
    (PMF.pure false).bind (fun s => (PMF.uniformOfFintype Bool).map (s, ·)) := by
  simp [seededHash, xorHash]

-- The digest alone is uniform for a fixed source, but it equals the public seed.
example : (seededHash (PMF.uniformOfFintype Bool) (PMF.pure false) xorHash).map Prod.snd =
    PMF.uniformOfFintype Bool := by
  simp [seededHash, xorHash, PMF.map_bind, PMF.bind_pure]

-- Keeping that seed distinguishes the actual joint law from an independent uniform digest.
example : dist (seededHash (PMF.uniformOfFintype Bool) (PMF.pure false) xorHash)
    ((PMF.uniformOfFintype Bool).bind
      (fun s => (PMF.uniformOfFintype Bool).map (s, ·))) = 1 / 2 := by
  norm_num [dist_eq, seededHash, PMF.bind_apply, PMF.map_apply, PMF.pure_apply,
    PMF.uniformOfFintype_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool, xorHash]

-- A zero-bit digest is exactly uniform, even for a source on an infinite ambient type.
example (source : PMF (List Bool)) :
    seededHash (PMF.pure true) source (fun _ _ => fun i : Fin 0 => i.elim0) =
      (PMF.pure true).bind (fun s =>
        (PMF.uniformOfFintype (Fin 0 → Bool)).map (s, ·)) :=
  seededHash_eq_uniform_of_subsingleton _ _ _

-- Revealing an injective function image leaves no entropy in any seed-dependent predicate.
example (seed source : PMF Bool) :
    conditionalEntropy (seed.bind (fun s => source.map
      (fun x => ((s, x, xorHash s x), xorHash s x)))) = 0 := by
  apply le_antisymm _ (conditionalEntropy_nonneg _)
  simpa using (xor_twoUniversal seed).conditionalEntropy_hash_le source id xorHash

-- Conditional extraction retains both the correlated side information and the public seed.
example (side : PMF Bool) (source : Bool → PMF Bool) :
    4 * dist
      (side.bind (fun info => (seededHash (PMF.pure false) (source info) xorHash).map (info, ·)))
      (side.bind (fun info => ((PMF.pure false).bind
        (fun s => (PMF.uniformOfFintype Bool).map (s, ·))).map (info, ·))) ^ 2 ≤
      2 * ∑ info, (side info).toReal * collisionProbability (source info) := by
  simpa using (xor_twoUniversal (PMF.pure false)).leftover_hash_conditional_sq side source

end ComplexityTests.UniversalHash
