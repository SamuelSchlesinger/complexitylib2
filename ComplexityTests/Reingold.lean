/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.Reachability.Reingold
import Complexity.Foundations.Combinatorics.Expander.LowerBound

/-!
# Reingold's transformation tests

The concrete theorem `Cslib.Reachability.reachable_iff_exists_reingoldGraph` has no hypotheses
beyond decidability of adjacency; its two directions are exercised on the complete and the empty
graph on two vertices. The bundled hypotheses of the generic statements are discharged: the regular
rotation map of every simple graph has at least half self-loops at every vertex, the connected
component of a vertex is connected, the base graph has `λ ≤ 1 / 5`, and the depth and length
conditions hold for the concrete depth and walk length (inside the proof of the concrete theorem).
The complete graph with self-loops, of spectral expansion `0`, shows the hypothesis of
`Cslib.RotationMap.exists_neighbor_pow_eq` is satisfiable.
-/

namespace ComplexityTests.Reingold

open Cslib Cslib.RotationMap Cslib.Reachability

-- On the complete graph on two vertices, the vertex `1` is reached from `0` by a short walk.
example : ∃ k : Fin (reingoldLength 2) → ReingoldLabel,
    (((reingoldGraph (⊤ : SimpleGraph (Fin 2))).pow (reingoldLength 2)).neighbor
      (reingoldStart 0) k).root.1 = 1 :=
  (reachable_iff_exists_reingoldGraph ⊤ 0 1).1 (SimpleGraph.Adj.reachable (by decide))

-- On the empty graph on two vertices, no walk from `0` ends over `1`.
example (k : Fin (reingoldLength 2) → ReingoldLabel) :
    (((reingoldGraph (⊥ : SimpleGraph (Fin 2))).pow (reingoldLength 2)).neighbor
      (reingoldStart 0) k).root.1 ≠ 1 := by
  intro h
  have := (reachable_iff_exists_reingoldGraph ⊥ 0 1).2 ⟨k, h⟩
  rw [SimpleGraph.reachable_bot] at this
  exact absurd this (by decide)

-- The hypotheses of the generic statements are satisfiable: the base graph is a good expander.
example : reingoldBase.spectralExpansion ≤ 1 / 5 :=
  spectralExpansion_reingoldBase_le

-- The regular rotation map of any simple graph has at least half self-loops at every vertex.
example {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n × Fin n) :
    Fintype.card ReingoldLabel ≤ 2 * Finset.card {b | (reingoldInput G).neighbor v b = v} :=
  card_le_two_mul_card_filter_neighbor_reingoldInput_eq G v

-- The connected component of a vertex satisfies the connectivity hypothesis of the spectral gap.
example {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : Fin n × Fin n) :
    ((reingoldInput G).componentGraph s).toSimpleGraph.Preconnected :=
  (reingoldInput G).preconnected_componentGraph s

-- The walk hypothesis is satisfiable: in the complete graph with self-loops one step reaches
-- every vertex.
example (u v : Fin 3) : ∃ k : Fin 1 → Fin 3, ((complete (Fin 3)).pow 1).neighbor u k = v :=
  (complete (Fin 3)).exists_neighbor_pow_eq (by rw [spectralExpansion_complete]; norm_num) u v

/--
info: 'Cslib.Reachability.reachable_iff_exists_reingoldGraph' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Reachability.reachable_iff_exists_reingoldGraph

/--
info: 'Cslib.RotationMap.reachable_iff_exists_root_neighbor_pow_reingold' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.reachable_iff_exists_root_neighbor_pow_reingold

/--
info: 'Cslib.RotationMap.exists_neighbor_pow_reingold_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.exists_neighbor_pow_reingold_eq

/--
info: 'Cslib.RotationMap.min_pow_le_one_sub_spectralExpansion_reingold' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.min_pow_le_one_sub_spectralExpansion_reingold

/--
info: 'Cslib.RotationMap.spectralExpansion_le_of_preconnected' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_le_of_preconnected

/--
info: 'Cslib.RotationMap.exists_neighbor_pow_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.exists_neighbor_pow_eq

/--
info: 'Cslib.RotationMap.reachable_ofSimpleGraph_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.reachable_ofSimpleGraph_iff

end ComplexityTests.Reingold
