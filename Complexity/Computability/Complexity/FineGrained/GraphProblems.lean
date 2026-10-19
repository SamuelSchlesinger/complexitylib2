/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.Reduction
public import Complexity.Computability.Complexity.Problems.Clique
public import Complexity.Computability.Complexity.Problems.Coloring
public import Complexity.Computability.Complexity.Problems.IndependentSet.Sparse
public import Complexity.Computability.Complexity.Problems.VertexCover

/-!
# Exponential lower bounds for graph problems under the exponential time hypothesis

Under the exponential time hypothesis, 3-coloring, independent set and vertex cover are not
decidable in time `2 ^ o(|V| + |E|)`, and independent set and clique are not decidable in time
`2 ^ o(|V|)` [ImpagliazzoPaturiZane2001] [CyganEtAl2015, Chapter 14]
[LokshtanovMarxSaurabh2011]. Each follows from a polynomial-time reduction from 3SAT whose graph
has `O(m)` vertices and edges on formulas with `m` clauses
(`Cslib.Complexity.ETH.not_decidableInSubexpTime_of_reduction`), together with the sparsification
lemma, which rules out subexponential time in `m` under the exponential time hypothesis:

* for 3-coloring, the gadget reduction `Cslib.Complexity.SAT.toThreeColoring`, whose graph has at
  most `(24 k + 12) m + 9` vertices and edges on clauses of at most `k` literals
  (`Cslib.Complexity.SAT.length_toThreeColoring_le`);
* for independent set, the reduction with variable edges
  `Cslib.Complexity.SAT.toSparseIndependentSet`, with at most `(k ^ 2 + 5 k) m`
  (`Cslib.Complexity.SAT.length_toSparseIndependentSet_le`). Karp's reduction
  `Cslib.Complexity.SAT.toIndependentSet` has at most `3 m` vertices on formulas with clauses of
  at most three literals, but can have quadratically many edges;
* for vertex cover, the same graph with the complementary target
  (`Cslib.Complexity.IndependentSet.toVertexCover`);
* for clique, the complement of the same graph on its vertices (`Cslib.Complexity.Graph.compl`),
  which has as many vertices but can have quadratically many edges.

A graph (`Cslib.Complexity.Graph`) is a list of declared vertices and a list of edges, and the
measures `|V|` and `|E|` are the lengths of these lists. They are at least the numbers of distinct
vertices and edges, so the lower bounds for them imply the lower bounds for the distinct counts
(`Cslib.Complexity.DecidableInSubexpTime.mono_measure`). As for `ETH` itself, time is measured up
to a polynomial in the length of the encoded instance, and a lower bound says: for some `δ > 0`, no
decider runs within time `2 ^ (δ μ)` times a polynomial.

The diamond reduction to Hamiltonian paths and cycles (`Cslib.Complexity.SAT.toDirHamPath`) has a
row of `3 m + 3` vertices for each variable occurrence, so up to `Θ(m ^ 2)` vertices and edges on
formulas with `m` clauses of three literals. Through it the exponential time hypothesis rules out
only time `2 ^ o(√(|V| + |E|))`; this is not stated here.

## Main results

* `Cslib.Complexity.SAT.length_toThreeColoring_le`: the 3-coloring reduction has linear size.
* `Cslib.Complexity.ETH.not_decidableInSubexpTime_ThreeColoring`: no `2 ^ o(|V| + |E|)` algorithm
  for 3-coloring.
* `Cslib.Complexity.ETH.not_decidableInSubexpTime_IndependentSet`,
  `Cslib.Complexity.ETH.not_decidableInSubexpTime_IndependentSet_vertices`: no `2 ^ o(|V| + |E|)`
  and no `2 ^ o(|V|)` algorithm for independent set.
* `Cslib.Complexity.ETH.not_decidableInSubexpTime_VertexCover`: no `2 ^ o(|V| + |E|)` algorithm
  for vertex cover.
* `Cslib.Complexity.ETH.not_decidableInSubexpTime_Clique`: no `2 ^ o(|V|)` algorithm for clique.

## References

* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
* [D. Lokshtanov, D. Marx, S. Saurabh, *Lower bounds based on the Exponential Time
  Hypothesis*][LokshtanovMarxSaurabh2011]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### The size of the 3-coloring reduction -/

private theorem length_flatMap_le {α β : Type*} {l : List α} {f : α → List β} {k : ℕ}
    (h : ∀ a ∈ l, (f a).length ≤ k) : (l.flatMap f).length ≤ k * l.length := by
  rw [List.length_flatMap, mul_comm]
  simpa using List.sum_le_length_nsmul (l.map fun a => (f a).length) k (by simpa using h)

/-- **The 3-coloring reduction has linear size.** On formulas with `m` clauses of at most `k`
literals, the graph of `SAT.toThreeColoring` has at most `(24 k + 12) m + 9` vertices and edges in
total, counted as listed. -/
theorem SAT.length_toThreeColoring_le {k : ℕ} {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ k) :
    (toThreeColoring φ).1.length + (toThreeColoring φ).2.length ≤ (24 * k + 12) * φ.length + 9 := by
  have hzip : ∀ c ∈ φ.zipIdx, c.1.length ≤ k := fun c hc => by
    obtain ⟨hi, hcl⟩ := List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 hc)
    exact hcl ▸ hφ _ (List.getElem_mem hi)
  have hvars : φ.vars.length ≤ k * φ.length := by
    rw [CNF.length_vars, mul_comm]
    simpa using List.sum_le_length_nsmul (φ.map List.length) k (by simpa using hφ)
  have h₁ : (φ.vars.flatMap (variableEdges φ)).length ≤ 3 * φ.vars.length :=
    length_flatMap_le fun _ _ => by simp [variableEdges]
  have h₂ : (φ.zipIdx.flatMap fun c => clauseEdges φ c.2 c.1).length ≤
      (5 * k + 4) * φ.length := by
    simpa using length_flatMap_le (l := φ.zipIdx) fun c hc => by
      have hst := length_flatMap_le (l := c.1.zipIdx) (k := 5)
        (f := fun l => stageEdges φ c.2 l.2 l.1) fun _ _ => by simp [stageEdges]
      simp only [List.length_zipIdx] at hst
      simp only [clauseEdges, List.length_append, List.length_cons, List.length_nil]
      have := hzip c hc
      nlinarith
  have hE : (coloringEdges φ).length ≤ (8 * k + 4) * φ.length + 3 := by
    simp only [coloringEdges, List.length_append, List.length_cons, List.length_nil]
    nlinarith
  have hV : (toThreeColoring φ).1.length = 2 * (coloringEdges φ).length := by
    simp only [toThreeColoring, List.length_flatMap, List.length_cons, List.length_nil,
      List.map_const', List.sum_replicate, smul_eq_mul]
    ring
  rw [hV]
  simp only [toThreeColoring]
  nlinarith

/-! ### Lower bounds -/

/-- **No `2 ^ o(|V| + |E|)` algorithm for 3-coloring under ETH** [CyganEtAl2015, Chapter 14]:
for some `δ > 0`, `ThreeColoring` is not decidable within time `2 ^ (δ (|V| + |E|))` times any
polynomial in the length of the encoded graph, for graphs with `|V|` declared vertices and `|E|`
edges. -/
theorem ETH.not_decidableInSubexpTime_ThreeColoring (h : ETH) :
    ¬DecidableInSubexpTime ThreeColoring encGraph fun G => G.1.length + G.2.length :=
  h.not_decidableInSubexpTime_of_reduction SAT.computableTidilyInPolyTime_toThreeColoring
    (fun φ _ => SAT.toThreeColoring_mem_iff φ) (k := 84 + 9) fun φ hφ => by
      have := SAT.length_toThreeColoring_le hφ
      nlinarith

/-- **No `2 ^ o(|V| + |E|)` algorithm for independent set under ETH** [CyganEtAl2015, Chapter 14]:
for some `δ > 0`, `IndependentSet` is not decidable within time `2 ^ (δ (|V| + |E|))` times any
polynomial in the length of the encoded instance, for graphs with `|V|` declared vertices and `|E|`
edges. -/
theorem ETH.not_decidableInSubexpTime_IndependentSet (h : ETH) :
    ¬DecidableInSubexpTime IndependentSet (encPair encGraph encNat)
      fun x => x.1.1.length + x.1.2.length :=
  h.not_decidableInSubexpTime_of_reduction SAT.computableTidilyInPolyTime_toSparseIndependentSet
    (fun φ _ => SAT.toSparseIndependentSet_mem_iff φ) (k := 24) fun φ hφ => by
      have := SAT.length_toSparseIndependentSet_le hφ
      omega

/-- **No `2 ^ o(|V|)` algorithm for independent set under ETH** [CyganEtAl2015, Chapter 14]: for
some `δ > 0`, `IndependentSet` is not decidable within time `2 ^ (δ |V|)` times any polynomial in
the length of the encoded instance, for graphs with `|V|` declared vertices. -/
theorem ETH.not_decidableInSubexpTime_IndependentSet_vertices (h : ETH) :
    ¬DecidableInSubexpTime IndependentSet (encPair encGraph encNat) fun x => x.1.1.length :=
  h.not_decidableInSubexpTime_of_reduction SAT.computableTidilyInPolyTime_toSparseIndependentSet
    (fun φ _ => SAT.toSparseIndependentSet_mem_iff φ) (k := 24) fun φ hφ => by
      have := SAT.length_toSparseIndependentSet_le hφ
      omega

/-- **No `2 ^ o(|V| + |E|)` algorithm for vertex cover under ETH** [CyganEtAl2015, Chapter 14]:
for some `δ > 0`, `VertexCover` is not decidable within time `2 ^ (δ (|V| + |E|))` times any
polynomial in the length of the encoded instance, for graphs with `|V|` declared vertices and `|E|`
edges. -/
theorem ETH.not_decidableInSubexpTime_VertexCover (h : ETH) :
    ¬DecidableInSubexpTime VertexCover (encPair encGraph encNat)
      fun x => x.1.1.length + x.1.2.length :=
  h.not_decidableInSubexpTime_of_reduction
    (IndependentSet.computableTidilyInPolyTime_toVertexCover.comp
      SAT.computableTidilyInPolyTime_toSparseIndependentSet)
    (fun φ _ => (IndependentSet.toVertexCover_mem_iff _).trans
      (SAT.toSparseIndependentSet_mem_iff φ)) (k := 24) fun φ hφ => by
      have := SAT.length_toSparseIndependentSet_le hφ
      simp only [Function.comp, IndependentSet.toVertexCover] at this ⊢
      omega

/-- **No `2 ^ o(|V|)` algorithm for clique under ETH** [CyganEtAl2015, Chapter 14]: for some
`δ > 0`, `Clique` is not decidable within time `2 ^ (δ |V|)` times any polynomial in the length of
the encoded instance, for graphs with `|V|` declared vertices. -/
theorem ETH.not_decidableInSubexpTime_Clique (h : ETH) :
    ¬DecidableInSubexpTime Clique (encPair encGraph encNat) fun x => x.1.1.length :=
  h.not_decidableInSubexpTime_of_reduction (f := fun φ =>
      ((SAT.toSparseIndependentSet φ).1.compl, (SAT.toSparseIndependentSet φ).2))
    ((show ComputableTidilyInPolyTime (fun x : Graph × ℕ => (x.1.compl, x.2))
      (encPair encGraph encNat) (encPair encGraph encNat) by fun_prop).comp
        SAT.computableTidilyInPolyTime_toSparseIndependentSet)
    (fun φ _ => (Graph.compl_mem_Clique_iff _ _).trans (SAT.toSparseIndependentSet_mem_iff φ))
    (k := 24) fun φ hφ => by
      have := SAT.length_toSparseIndependentSet_le hφ
      simp only [Graph.compl] at this ⊢
      omega

end Cslib.Complexity
