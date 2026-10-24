/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Graph isomorphism

`GraphIsomorphism` is the set of pairs of graphs, in the encoding of `IndependentSet`, that are
isomorphic: the simple graphs induced on their declared vertices are isomorphic in the sense of
Mathlib's `SimpleGraph.Iso`. Repeated vertex entries are ignored, and so are edges with an
endpoint outside the declared vertices. `GraphNonIsomorphism` is its complement
[Arora and Barak, Section 8.1.3][AroraBarak09].

Positions in the list `Graph.distinctVertices` of declared vertices without repetitions enumerate
the vertices, and `Graph.adjIndex` reads adjacency through positions. Two graphs are isomorphic
exactly when a bijection of positions preserves `adjIndex` (`mem_GraphIsomorphism_iff`).

`GraphIsomorphism ∈ NP`: a certificate lists, for each position `i` of the first graph, a block of
bits whose first set bit selects a position of the second graph, and the verifier checks that the
selected positions form an injective map preserving adjacency between graphs with equally many
vertices.

## Main definitions

* `Cslib.Complexity.Graph.induced`, `Cslib.Complexity.Graph.adjIndex`.
* `Cslib.Complexity.GraphIsomorphism`, `Cslib.Complexity.GraphNonIsomorphism`.
* `Cslib.Complexity.GraphIsomorphism.verifier`.

## Main results

* `Cslib.Complexity.mem_GraphIsomorphism_iff`: isomorphism through positions.
* `Cslib.Complexity.length_distinctVertices_eq_of_mem_GraphIsomorphism`,
  `Cslib.Complexity.mem_GraphIsomorphism_iff_exists_perm`: isomorphic graphs have equally many
  vertices, and are then related by a permutation of positions.
* `Cslib.Complexity.GraphIsomorphism.isVerifier`, `Cslib.Complexity.GraphIsomorphism.mem_NP`:
  `GraphIsomorphism ∈ NP (encPair encGraph encGraph)`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableTidilyInPolyTime

namespace Graph

/-- The simple graph induced by `G` on its declared vertices. -/
def induced (G : Graph) : SimpleGraph {v // v ∈ G.1} :=
  G.toSimpleGraph.induce {v | v ∈ G.1}

/-- Adjacency of the vertices at positions `i` and `j` of `G.distinctVertices`. -/
def adjIndex (G : Graph) (i j : ℕ) : Bool :=
  G.adjBool (G.distinctVertices.getD i 0) (G.distinctVertices.getD j 0)

/-- Positions in `G.distinctVertices` enumerate the declared vertices. -/
def vertexEquiv (G : Graph) : Fin G.distinctVertices.length ≃ {v // v ∈ G.1} :=
  (G.nodup_distinctVertices.getEquiv _).trans
    (Equiv.subtypeEquivRight fun _ => mem_distinctVertices)

theorem vertexEquiv_apply (G : Graph) (i : Fin G.distinctVertices.length) :
    (G.vertexEquiv i : ℕ) = G.distinctVertices.getD i 0 := by
  simp [vertexEquiv, List.Nodup.getEquiv, List.getD_eq_getElem?_getD]

theorem induced_adj_vertexEquiv (G : Graph) (i j : Fin G.distinctVertices.length) :
    G.induced.Adj (G.vertexEquiv i) (G.vertexEquiv j) ↔ G.adjIndex i j = true := by
  rw [induced, SimpleGraph.induce_adj, adjIndex, adjBool_eq_true_iff, vertexEquiv_apply,
    vertexEquiv_apply]

/-- Adjacency of computed positions in a computed graph is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_adjIndex {γ : Type} {input : γ ↪ List Bool} {G : γ → Graph}
    {i j : γ → ℕ} (hG : ComputableTidilyInPolyTime G input encGraph)
    (hi : ComputableTidilyInPolyTime i input encUnary)
    (hj : ComputableTidilyInPolyTime j input encUnary) :
    ComputableTidilyInPolyTime (fun x => (G x).adjIndex (i x) (j x)) input encBool := by
  have hV := computableTidilyInPolyTime_distinctVertices.comp hG
  exact computableTidilyInPolyTime_adjBool.comp ((hG.prod
    ((listGetD (encA := encNat) 0).comp (hV.prod hi))).prod
    ((listGetD (encA := encNat) 0).comp (hV.prod hj)))

end Graph

/-- The pairs of isomorphic graphs: the graphs induced on the declared vertices are isomorphic
[Arora and Barak, Section 8.1.3][AroraBarak09]. -/
def GraphIsomorphism : Set (Graph × Graph) := {x | Nonempty (x.1.induced ≃g x.2.induced)}

/-- The pairs of non-isomorphic graphs [Arora and Barak, Section 8.1.3][AroraBarak09]. -/
def GraphNonIsomorphism : Set (Graph × Graph) := GraphIsomorphismᶜ

/-- Two graphs are isomorphic exactly when a bijection between the positions of their distinct
vertices preserves adjacency. -/
theorem mem_GraphIsomorphism_iff {x : Graph × Graph} : x ∈ GraphIsomorphism ↔
    ∃ σ : Fin x.1.distinctVertices.length ≃ Fin x.2.distinctVertices.length,
      ∀ i j, x.2.adjIndex (σ i) (σ j) = x.1.adjIndex i j := by
  constructor
  · rintro ⟨φ⟩
    refine ⟨x.1.vertexEquiv.trans (φ.toEquiv.trans x.2.vertexEquiv.symm), fun i j => ?_⟩
    rw [Bool.eq_iff_iff, ← Graph.induced_adj_vertexEquiv, ← Graph.induced_adj_vertexEquiv]
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    exact φ.map_adj_iff
  · rintro ⟨σ, hσ⟩
    refine ⟨⟨x.1.vertexEquiv.symm.trans (σ.trans x.2.vertexEquiv), fun {u v} => ?_⟩⟩
    obtain ⟨i, rfl⟩ := x.1.vertexEquiv.surjective u
    obtain ⟨j, rfl⟩ := x.1.vertexEquiv.surjective v
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [Graph.induced_adj_vertexEquiv, Graph.induced_adj_vertexEquiv, hσ]

/-- Isomorphic graphs have equally many distinct vertices. -/
theorem length_distinctVertices_eq_of_mem_GraphIsomorphism {G₀ G₁ : Graph}
    (h : (G₀, G₁) ∈ GraphIsomorphism) :
    G₁.distinctVertices.length = G₀.distinctVertices.length := by
  obtain ⟨σ, -⟩ := mem_GraphIsomorphism_iff.1 h
  exact (Fin.equiv_iff_eq.1 ⟨σ⟩).symm

/-- Graphs with equally many distinct vertices are isomorphic exactly when a permutation of the
positions of the first carries its adjacency to the adjacency of the second. -/
theorem mem_GraphIsomorphism_iff_exists_perm {G₀ G₁ : Graph}
    (h : G₁.distinctVertices.length = G₀.distinctVertices.length) :
    (G₀, G₁) ∈ GraphIsomorphism ↔ ∃ τ : Equiv.Perm (Fin G₀.distinctVertices.length),
      ∀ i j, G₁.adjIndex (τ i) (τ j) = G₀.adjIndex i j := by
  rw [mem_GraphIsomorphism_iff]
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ.trans (finCongr h), fun i j => hσ i j⟩
  · rintro ⟨τ, hτ⟩
    exact ⟨τ.trans (finCongr h.symm), fun i j => hτ i j⟩

namespace GraphIsomorphism

/-! ### Verification -/

/-- The position of the second graph selected by a certificate `w` for position `i` of the first,
for graphs with `n` distinct vertices: the first `j < n` with bit `i * n + j` of `w` set, or `0`
when there is none. -/
def image (n : ℕ) (w : List Bool) (i : ℕ) : ℕ :=
  ((List.range n).filter fun j => w.getD (i * n + j) false).headD 0

theorem image_lt {n : ℕ} (w : List Bool) (i : ℕ) (hn : 0 < n) : image n w i < n := by
  unfold image
  cases h : (List.range n).filter (fun j => w.getD (i * n + j) false) with
  | nil => exact hn
  | cons j l =>
    have : j ∈ (List.range n).filter (fun j => w.getD (i * n + j) false) :=
      h ▸ List.mem_cons_self
    simpa using (List.mem_filter.1 this).1

/-- A block with exactly one set bit selects its position. -/
theorem image_eq {n : ℕ} {w : List Bool} {i c : ℕ} (hc : c < n)
    (hw : ∀ j < n, w.getD (i * n + j) false = decide (j = c)) : image n w i = c := by
  unfold image
  rw [List.filter_congr (fun j hj => hw j (List.mem_range.1 hj)), List.filter_eq,
    List.count_eq_one_of_mem List.nodup_range (List.mem_range.2 hc), List.replicate_one]
  rfl

/-- The test of positions `i` and `i'` of `G` under the certificate `w`: their selected positions
are distinct when they are, and adjacent in `H` exactly when they are adjacent in `G`. -/
def pairTest (G H : Graph) (w : List Bool) (i i' : ℕ) : Bool :=
  (decide (i = i') ||
      decide (image G.distinctVertices.length w i ≠ image G.distinctVertices.length w i')) &&
    G.adjIndex i i' ==
      H.adjIndex (image G.distinctVertices.length w i) (image G.distinctVertices.length w i')

/-- Accept a certificate when the graphs have equally many distinct vertices and the selected
positions form an injective map preserving adjacency. -/
def verifier (x : (Graph × Graph) × List Bool) : Bool :=
  decide (x.1.2.distinctVertices.length = x.1.1.distinctVertices.length) &&
    (List.range x.1.1.distinctVertices.length).all fun i =>
      (List.range x.1.1.distinctVertices.length).all fun i' => pairTest x.1.1 x.1.2 x.2 i i'

@[fun_prop]
theorem computableTidilyInPolyTime_image {γ : Type} {input : γ ↪ List Bool} {n i : γ → ℕ}
    {w : γ → List Bool} (hn : ComputableTidilyInPolyTime n input encUnary)
    (hw : ComputableTidilyInPolyTime w input encBits)
    (hi : ComputableTidilyInPolyTime i input encUnary) :
    ComputableTidilyInPolyTime (fun x => image (n x) (w x) (i x)) input encUnary := by
  unfold image
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_pairTest {γ : Type} {input : γ ↪ List Bool} {G H : γ → Graph}
    {w : γ → List Bool} {i i' : γ → ℕ} (hG : ComputableTidilyInPolyTime G input encGraph)
    (hH : ComputableTidilyInPolyTime H input encGraph)
    (hw : ComputableTidilyInPolyTime w input encBits)
    (hi : ComputableTidilyInPolyTime i input encUnary)
    (hi' : ComputableTidilyInPolyTime i' input encUnary) :
    ComputableTidilyInPolyTime (fun x => pairTest (G x) (H x) (w x) (i x) (i' x)) input
      encBool := by
  have hn : ComputableTidilyInPolyTime (fun x => (G x).distinctVertices.length) input encUnary :=
    (length_list encNat).comp (Graph.computableTidilyInPolyTime_distinctVertices.comp hG)
  unfold pairTest
  fun_prop

/-- The verifier is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_verifier :
    ComputableTidilyInPolyTime verifier (encPair (encPair encGraph encGraph) encBits) encBool := by
  unfold verifier
  fun_prop

/-- `verifier` is a verifier for `GraphIsomorphism` with certificates whose length is the square
of the length of the encoded pair of graphs. -/
theorem isVerifier :
    IsVerifier (encPair encGraph encGraph) (Polynomial.X ^ 2) verifier GraphIsomorphism := by
  rintro ⟨G, H⟩
  simp only [Polynomial.eval_pow, Polynomial.eval_X]
  rw [mem_GraphIsomorphism_iff]
  have hnL : G.distinctVertices.length ≤ (encPair encGraph encGraph (G, H)).length := by
    have := G.length_distinctVertices_le
    simp only [length_encPair]
    omega
  set L := (encPair encGraph encGraph (G, H)).length
  set n := G.distinctVertices.length
  constructor
  · rintro ⟨σ, hσ⟩
    have hcard : H.distinctVertices.length = n := (Fin.equiv_iff_eq.1 ⟨σ⟩).symm
    let f : ℕ → ℕ := fun i => if h : i < n then σ ⟨i, h⟩ else 0
    have hfσ : ∀ i (h : i < n), f i = σ ⟨i, h⟩ := fun i h => by simp [f, h]
    have hf : ∀ i < n, f i < n := fun i h => (hfσ i h).trans_lt
      (lt_of_lt_of_eq (σ ⟨i, h⟩).isLt hcard)
    let w := (List.range (L ^ 2)).map fun k => decide (k < n * n ∧ f (k / n) = k % n)
    refine ⟨w, by simp [w], ?_⟩
    have himage : ∀ i < n, image n w i = f i := fun i hi => image_eq (hf i hi) fun j hj => by
      have hk : i * n + j < n * n := by nlinarith
      have hkL : i * n + j < L ^ 2 := lt_of_lt_of_le hk (by nlinarith)
      have hdiv : (i * n + j) / n = i := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, zero_add]
      have hmod : (i * n + j) % n = j := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
      simp only [w, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hkL,
        Option.map_some, Option.getD_some, hk, true_and, hdiv, hmod, eq_comm (a := f i)]
    simp only [verifier, pairTest, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range, Bool.or_eq_true, beq_iff_eq]
    refine ⟨hcard, fun i hi i' hi' => ⟨?_, ?_⟩⟩ <;>
      rw [himage i hi, himage i' hi', hfσ i hi, hfσ i' hi']
    · by_cases hii : i = i'
      · exact Or.inl hii
      · exact Or.inr fun h => hii (by simpa using σ.injective (Fin.ext h))
    · exact (hσ ⟨i, hi⟩ ⟨i', hi'⟩).symm
  · rintro ⟨w, -, hw⟩
    simp only [verifier, pairTest, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range, Bool.or_eq_true, beq_iff_eq] at hw
    obtain ⟨hcard, hpair⟩ := hw
    let g : Fin n → Fin H.distinctVertices.length := fun i =>
      ⟨image n w i, hcard ▸ image_lt w i (Nat.zero_lt_of_lt i.isLt)⟩
    have hg : Function.Injective g := by
      intro i i' h
      by_contra hii
      rcases (hpair i i.isLt i' i'.isLt).1 with h' | h'
      · exact hii (Fin.ext h')
      · exact h' (congrArg Fin.val h)
    have hbij : Function.Bijective g :=
      (Fintype.bijective_iff_injective_and_card g).2 ⟨hg, by simp [hcard, n]⟩
    exact ⟨Equiv.ofBijective g hbij, fun i i' => ((hpair i i.isLt i' i'.isLt).2).symm⟩

/-- **`GraphIsomorphism ∈ NP`.** -/
theorem mem_NP : GraphIsomorphism ∈ NP (encPair encGraph encGraph) :=
  ⟨Polynomial.X ^ 2, verifier, .of_tidy computableTidilyInPolyTime_verifier, isVerifier⟩

end GraphIsomorphism

end Cslib.Complexity
