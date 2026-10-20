/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.AffineTower
public import Complexity.Foundations.Combinatorics.Expander.OfSimpleGraph
public import Complexity.Foundations.Combinatorics.Expander.Reingold
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Log
public import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.NormNum.Prime

/-!
# Undirected connectivity by short walks in an explicit graph

This is the combinatorial core of Reingold's theorem that undirected `s`–`t` connectivity is in
deterministic logarithmic space [Reingold, Theorem 4.1][Reingold2008]
[Arora and Barak, Section 21.4][AroraBarak09], with explicit constants. For a simple graph `G` on
`Fin n`:

1. the slot graph of `G` (`Cslib.RotationMap.ofSimpleGraph`, with the slots of a vertex in the
   cyclic order of `finRotate n`) is a `3`-regular multigraph on `Fin n × Fin n` with the
   connectivity of `G`; its labels are extended by self-loops to the `257 ^ 8` vertices of the base
   graph below, so that at least half of the edges at every vertex are self-loops
   (`Cslib.Reachability.reingoldInput`);
2. the base graph `Cslib.Reachability.reingoldBase` is the arithmetic zig-zag base graph over
   `ZMod 257` (`Cslib.RotationMap.affinePlaneTowerBase`), a `257 ^ 2`-regular multigraph on
   `257 ^ 8` vertices of spectral expansion at most `1 / 5`, computed by field arithmetic;
3. `reingoldDepth n = 16 ⌈log₂ n⌉ + 524` steps of Reingold's transformation
   (`Cslib.RotationMap.reingold`) make every connected component an expander with `λ ≤ 4 / 5`, and
   walks of length `reingoldLength n = 4 (2 ⌈log₂ n⌉ + 65 reingoldDepth n)` reach every vertex of a
   component.

So `t` is reachable from `s` exactly when some walk of length `reingoldLength n` in
`reingoldGraph G` from the vertex `reingoldStart s` over the slot `(s, s)` ends over a slot of `t`
(`Cslib.Reachability.reachable_iff_exists_reingoldGraph`). Both the depth and the walk length are
`O(log n)`, and the graph has constant degree `257 ^ 8`, so the walks can be enumerated with
`O(log n)` bits. Evaluating the rotation map of `reingoldGraph G` in logarithmic space, and the
resulting membership of undirected connectivity in `L`, are not proved here.

The constants are far from optimal: they come from the gap growth `γ ↦ min (6 γ / 5) (1 / 5)` of a
step that squares once (`Cslib.RotationMap.min_le_one_sub_spectralExpansion_reingoldStep`), from
the initial gap `1 / (2 N² |B|²)` given by Cheeger's inequality, and from rounding `log₂ (6 / 5)`
and `log₂ (5 / 4)` down to `1 / 4`.

## Main definitions

* `Cslib.Reachability.ReingoldLabel`, `Cslib.Reachability.reingoldBase`: the labels and the base
  graph.
* `Cslib.Reachability.reingoldInput`: the regular rotation map of a simple graph on `Fin n`.
* `Cslib.Reachability.reingoldDepth`, `Cslib.Reachability.reingoldLength`: the number of steps
  of the transformation and the walk length.
* `Cslib.Reachability.reingoldGraph`, `Cslib.Reachability.reingoldStart`: the transformed graph
  and the start vertex over `s`.

## Main results

* `Cslib.Reachability.spectralExpansion_reingoldBase_le`: the base graph has `λ ≤ 1 / 5`.
* `Cslib.Reachability.reachable_reingoldInput_iff`: the regular rotation map has the
  connectivity of the simple graph.
* `Cslib.Reachability.reachable_iff_exists_reingoldGraph`: undirected connectivity is decided by
  the walks of length `O(log n)` from one vertex of the constant-degree graph `reingoldGraph G`.

## References

* [O. Reingold, *Undirected connectivity in log-space*][Reingold2008]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002]
-/

@[expose] public section

namespace Cslib.Reachability

open RotationMap

/-- The labels of the graphs of Reingold's transformation: the `257 ^ 8` vertices of the base graph,
eight coordinates in `ZMod 257`. -/
abbrev ReingoldLabel : Type :=
  AffinePlaneTowerBaseVertex (ZMod 257)

/-- The labels of the base graph: pairs of elements of `ZMod 257`. -/
abbrev ReingoldBaseLabel : Type :=
  ZMod 257 × ZMod 257

/-- The base graph of the transformation: the arithmetic zig-zag base graph over `ZMod 257`, a
`257 ^ 2`-regular multigraph on `257 ^ 8` vertices. -/
def reingoldBase : RotationMap ReingoldLabel ReingoldBaseLabel :=
  have : Fact (Nat.Prime 257) := ⟨by norm_num⟩
  affinePlaneTowerBase (ZMod 257)

/-- The vertices of the base graph name the pairs of pairs of its labels. -/
def reingoldEquiv : ReingoldLabel ≃ (Fin 2 → ReingoldBaseLabel × ReingoldBaseLabel) :=
  affinePlaneTowerBaseEquiv (ZMod 257)

/-- There are `257 ^ 8` labels. -/
theorem card_reingoldLabel : Fintype.card ReingoldLabel = 257 ^ 8 := by
  simp only [ReingoldLabel, AffinePlaneTowerBaseVertex, Fintype.card_prod, ZMod.card]
  norm_num

/-- **The base graph is a good expander**: its spectral expansion is at most `1 / 5`. -/
theorem spectralExpansion_reingoldBase_le : reingoldBase.spectralExpansion ≤ 1 / 5 := by
  have : Fact (Nat.Prime 257) := ⟨by norm_num⟩
  exact spectralExpansion_affinePlaneTowerBase_le_one_div_five (ZMod 257)
    (by rw [ZMod.card]; norm_num)

/-- The three labels of the slot graph, as labels of the base graph. -/
def slotLabel : (Unit ⊕ Unit × (Unit × Bool)) ↪ ReingoldLabel where
  toFun
    | .inl () => ((((0, 0), (0, 0)), (0, 0)), (0, 0))
    | .inr ((), (), false) => ((((1, 0), (0, 0)), (0, 0)), (0, 0))
    | .inr ((), (), true) => ((((2, 0), (0, 0)), (0, 0)), (0, 0))
  inj' := Function.LeftInverse.injective
    (g := fun b ↦ if b.1.1.1.1 = 1 then .inr ((), (), false)
      else if b.1.1.1.1 = 2 then .inr ((), (), true) else .inl ())
    (by rintro (_ | ⟨_, _, _ | _⟩) <;> rfl)

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- The regular rotation map of a simple graph on `Fin n`: its slot graph, with the slots of a
vertex in the cyclic order of `finRotate n`, with self-loops added to reach the labels of the base
graph. -/
def reingoldInput : RotationMap (Fin n × Fin n) ReingoldLabel :=
  (ofSimpleGraph G (finRotate n)).extendLabels slotLabel

/-- All points of `Fin n` lie on the single cycle of `finRotate n`. -/
theorem sameCycle_finRotate (a b : Fin n) : (finRotate n).SameCycle a b := by
  rcases lt_or_ge n 2 with hn | hn
  · have : Subsingleton (Fin n) := by
      refine ⟨fun x y ↦ Fin.ext ?_⟩
      omega
    rw [Subsingleton.elim a b]
  · have hsupp (x : Fin n) : finRotate n x ≠ x := by
      rw [← Equiv.Perm.mem_support, support_finRotate_of_le hn]
      exact Finset.mem_univ x
    exact (isCycle_finRotate_of_le hn).sameCycle (hsupp a) (hsupp b)

/-- **The regular rotation map has the connectivity of the simple graph**: a slot `q` is reachable
from a slot `p` exactly when the vertex of `q` is reachable from the vertex of `p` in `G`. -/
theorem reachable_reingoldInput_iff {p q : Fin n × Fin n} :
    (reingoldInput G).toSimpleGraph.Reachable p q ↔ G.Reachable p.1 q.1 := by
  rw [reingoldInput, toSimpleGraph_extendLabels]
  exact reachable_ofSimpleGraph_iff G _ sameCycle_finRotate

/-- At least half of the edges at every vertex of the regular rotation map are self-loops. -/
theorem card_le_two_mul_card_filter_neighbor_reingoldInput_eq (v : Fin n × Fin n) :
    Fintype.card ReingoldLabel ≤ 2 * Finset.card {b | (reingoldInput G).neighbor v b = v} :=
  (ofSimpleGraph G (finRotate n)).card_le_two_mul_card_filter_neighbor_extendLabels_eq slotLabel
    (by rw [card_ofSimpleGraph_label, card_reingoldLabel]; norm_num) v

/-- The number of steps of the transformation: `16 ⌈log₂ n⌉ + 524`. -/
def reingoldDepth (n : ℕ) : ℕ :=
  16 * Nat.clog 2 n + 524

/-- The length of the walks: `4 (2 ⌈log₂ n⌉ + 65 reingoldDepth n)`. -/
def reingoldLength (n : ℕ) : ℕ :=
  4 * (2 * Nat.clog 2 n + 65 * reingoldDepth n)

/-- **Reingold's graph** of a simple graph on `Fin n`: `reingoldDepth n` steps of Reingold's
transformation applied to its regular rotation map, a `257 ^ 8`-regular multigraph. -/
def reingoldGraph : RotationMap (ReingoldVertex (Fin n × Fin n) ReingoldLabel (reingoldDepth n))
    ReingoldLabel :=
  reingold reingoldBase reingoldEquiv (reingoldInput G) (reingoldDepth n)

/-- The start vertex of the walks from `s`: the vertex `(⋯ ((s, s), 0) ⋯, 0)` of Reingold's graph,
over the slot `(s, s)`. -/
def reingoldStart (s : Fin n) : ReingoldVertex (Fin n × Fin n) ReingoldLabel (reingoldDepth n) :=
  ReingoldVertex.mk (s, s) 0 (reingoldDepth n)

/-- The number of steps suffices: `2 |V|² |B|² 5 ^ ℓ ≤ 5 · 6 ^ ℓ` for the `n ^ 2` slots and the
`257 ^ 8` labels. -/
private theorem depth_bound (n : ℕ) :
    2 * (n * n) ^ 2 * (257 ^ 8) ^ 2 * 5 ^ reingoldDepth n ≤ 5 * 6 ^ reingoldDepth n := by
  set a := Nat.clog 2 n
  set m := 4 * a + 131
  have hℓ : reingoldDepth n = 4 * m := by simp only [reingoldDepth, m, a]; ring
  have hn : n ≤ 2 ^ a := Nat.le_pow_clog (by norm_num) n
  have h₁ : 2 * (n * n) ^ 2 * (257 ^ 8) ^ 2 ≤ 2 ^ m :=
    calc 2 * (n * n) ^ 2 * (257 ^ 8) ^ 2 ≤ 2 * (2 ^ a * 2 ^ a) ^ 2 * 2 ^ 130 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.mul_le_mul hn hn) 2))
            (by norm_num)
      _ = 2 ^ m := by simp only [m]; ring
  rw [hℓ, pow_mul, pow_mul]
  calc 2 * (n * n) ^ 2 * (257 ^ 8) ^ 2 * (5 ^ 4) ^ m ≤ 2 ^ m * (5 ^ 4) ^ m := by gcongr
    _ = 1250 ^ m := by rw [← mul_pow]; norm_num
    _ ≤ 1296 ^ m := Nat.pow_le_pow_left (by norm_num) m
    _ = (6 ^ 4) ^ m := by norm_num
    _ ≤ 5 * (6 ^ 4) ^ m := Nat.le_mul_of_pos_left _ (by norm_num)

/-- The walk length suffices: `|V| |B| ^ ℓ 4 ^ T ≤ 5 ^ T` for the `n ^ 2` slots and the `257 ^ 8`
labels. -/
private theorem length_bound (n : ℕ) :
    n * n * (257 ^ 8) ^ reingoldDepth n * 4 ^ reingoldLength n ≤ 5 ^ reingoldLength n := by
  have hn : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) n
  rw [show reingoldLength n = 4 * (2 * Nat.clog 2 n + 65 * reingoldDepth n) from rfl]
  generalize Nat.clog 2 n = a at hn ⊢
  generalize reingoldDepth n = ℓ
  set m := 2 * a + 65 * ℓ with hm
  have h₁ : n * n * (257 ^ 8) ^ ℓ ≤ 2 ^ m :=
    calc n * n * (257 ^ 8) ^ ℓ ≤ 2 ^ a * 2 ^ a * (2 ^ 65) ^ ℓ :=
          Nat.mul_le_mul (Nat.mul_le_mul hn hn) (Nat.pow_le_pow_left (by norm_num) _)
      _ = 2 ^ m := by
          rw [← pow_add, ← pow_mul, ← pow_add, hm]
          congr 1
          ring
  rw [pow_mul, pow_mul]
  calc n * n * (257 ^ 8) ^ ℓ * (4 ^ 4) ^ m ≤ 2 ^ m * (4 ^ 4) ^ m := by gcongr
    _ = 512 ^ m := by rw [← mul_pow]; norm_num
    _ ≤ 625 ^ m := Nat.pow_le_pow_left (by norm_num) m
    _ = (5 ^ 4) ^ m := by norm_num

/-- **Undirected connectivity by short walks in Reingold's graph**, the combinatorial part of the
proof of [Reingold, Theorem 4.1][Reingold2008] [Arora and Barak, Section 21.4][AroraBarak09]: for
a simple graph `G` on `Fin n`, `t` is reachable from `s` exactly when some walk of length
`reingoldLength n = O(log n)` in the `257 ^ 8`-regular graph `reingoldGraph G` from
`reingoldStart s` ends at a vertex over a slot `(t, w)` of `t`. -/
theorem reachable_iff_exists_reingoldGraph (s t : Fin n) :
    G.Reachable s t ↔ ∃ k : Fin (reingoldLength n) → ReingoldLabel,
      (((reingoldGraph G).pow (reingoldLength n)).neighbor (reingoldStart s) k).root.1 = t := by
  have hloop := card_le_two_mul_card_filter_neighbor_reingoldInput_eq G
  have hV : Fintype.card (Fin n × Fin n) = n * n := by
    rw [Fintype.card_prod, Fintype.card_fin]
  have hℓ : 2 * Fintype.card (Fin n × Fin n) ^ 2 * Fintype.card ReingoldLabel ^ 2 *
      5 ^ reingoldDepth n ≤ 5 * 6 ^ reingoldDepth n := by
    rw [hV, card_reingoldLabel]
    exact depth_bound n
  have hT : Fintype.card (Fin n × Fin n) * Fintype.card ReingoldLabel ^ reingoldDepth n *
      4 ^ reingoldLength n ≤ 5 ^ reingoldLength n := by
    rw [hV, card_reingoldLabel]
    exact length_bound n
  have key := reachable_iff_exists_root_neighbor_pow_reingold reingoldBase reingoldEquiv
    spectralExpansion_reingoldBase_le (reingoldInput G) hloop hℓ hT (s, s) (t, t) 0
  refine ⟨fun h ↦ ?_, fun ⟨k, hk⟩ ↦ ?_⟩
  · obtain ⟨k, hk⟩ := key.1 ((reachable_reingoldInput_iff G).2 h)
    exact ⟨k, by rw [reingoldGraph, reingoldStart, hk]⟩
  · have h := reachable_root_neighbor_pow_reingold reingoldBase reingoldEquiv (reingoldInput G)
      (reingoldDepth n) (reingoldLength n) (reingoldStart s) k
    rw [reingoldStart, ReingoldVertex.root_mk] at h
    rw [← hk]
    exact (reachable_reingoldInput_iff G).1 h

end Cslib.Reachability
