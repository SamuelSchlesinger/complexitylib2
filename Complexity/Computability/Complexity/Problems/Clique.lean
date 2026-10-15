/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.IndependentSet

/-!
# Cliques

`Clique` is the set of graphs with a clique of a given number of their vertices [Arora and Barak,
Section 2.4][AroraBarak09]. A set of vertices is independent in a graph exactly when it is a clique
in the complement of the graph on its vertices (`Graph.compl`), so complementing the graph reduces
`IndependentSet` to `Clique` [Karp1972].

## Main definitions

* `Cslib.Complexity.Clique`, `Cslib.Complexity.Graph.compl`.

## Main results

* `Cslib.Complexity.Graph.compl_mem_Clique_iff`: `(G.compl, m) ∈ Clique ↔ (G, m) ∈ IndependentSet`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

@[expose] public section

namespace Cslib.Complexity

/-- The graphs with a clique of `m` of their vertices. -/
def Clique : Set (Graph × ℕ) :=
  {x | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.1.1) ∧ x.1.toSimpleGraph.IsNClique x.2 S}

namespace Graph

/-- The complement of a graph on its vertices: an edge between any two distinct vertices that are
not adjacent. -/
def compl (G : Graph) : Graph :=
  (G.1, G.1.flatMap fun u =>
    (G.1.filter fun v => decide (u ≠ v ∧ (u, v) ∉ G.2 ∧ (v, u) ∉ G.2)).map fun v => (u, v))

/-- On the vertices of a graph, adjacency in the complement is non-adjacency in the graph. -/
theorem compl_adj_iff {G : Graph} {u v : ℕ} (hu : u ∈ G.1) (hv : v ∈ G.1) :
    G.compl.toSimpleGraph.Adj u v ↔ u ≠ v ∧ ¬G.toSimpleGraph.Adj u v := by
  have hedge : ∀ {a b}, (a, b) ∈ G.compl.2 ↔ a ∈ G.1 ∧ b ∈ G.1 ∧
      (a ≠ b ∧ (a, b) ∉ G.2 ∧ (b, a) ∉ G.2) := by
    intro a b
    simp only [compl, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq,
      Prod.mk.injEq]
    constructor
    · rintro ⟨a', ha', b', ⟨hb', hne⟩, rfl, rfl⟩
      exact ⟨ha', hb', hne⟩
    · rintro ⟨ha, hb, hne⟩
      exact ⟨a, ha, b, ⟨hb, hne⟩, rfl, rfl⟩
  simp only [toSimpleGraph, SimpleGraph.fromRel_adj, ne_eq, hedge]
  constructor
  · rintro ⟨huv, ⟨-, -, -, h₁, h₂⟩ | ⟨-, -, -, h₁, h₂⟩⟩
    · exact ⟨huv, fun ⟨_, h⟩ => h.elim h₁ h₂⟩
    · exact ⟨huv, fun ⟨_, h⟩ => h.elim h₂ h₁⟩
  · rintro ⟨huv, h⟩
    refine ⟨huv, Or.inl ⟨hu, hv, huv, fun h₁ => h ⟨huv, Or.inl h₁⟩, fun h₂ => h ⟨huv, Or.inr h₂⟩⟩⟩

/-- **Independent sets are cliques of the complement.** -/
theorem compl_mem_Clique_iff (G : Graph) (m : ℕ) :
    (G.compl, m) ∈ Clique ↔ (G, m) ∈ IndependentSet := by
  refine exists_congr fun S => ?_
  simp only [compl]
  refine and_congr_right fun hS => ?_
  have hpair : (↑S : Set ℕ).Pairwise G.compl.toSimpleGraph.Adj ↔
      (↑S : Set ℕ).Pairwise fun u v => ¬G.toSimpleGraph.Adj u v := by
    refine ⟨fun h u hu v hv huv => ((compl_adj_iff (hS u hu) (hS v hv)).1 (h hu hv huv)).2,
      fun h u hu v hv huv => (compl_adj_iff (hS u hu) (hS v hv)).2 ⟨huv, h hu hv huv⟩⟩
  exact ⟨fun ⟨h₁, h₂⟩ => ⟨hpair.1 h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨hpair.2 h₁, h₂⟩⟩

end Graph

end Cslib.Complexity
