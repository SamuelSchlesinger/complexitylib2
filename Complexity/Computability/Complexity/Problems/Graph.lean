/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP.Witness
public import Mathlib.Combinatorics.SimpleGraph.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Graphs given by vertex and edge lists

The graph problems (`IndependentSet`, `Clique`, `VertexCover`, `KColoring`, the Hamiltonian
problems, `GraphIsomorphism`, …) take a graph (`Cslib.Complexity.Graph`) as a list of declared
vertices, possibly with repetitions, and a list of edges, encoded in binary
(`Cslib.Complexity.encGraph`). Its mathematical reading is a Mathlib simple graph on `ℕ`
(`Cslib.Complexity.Graph.toSimpleGraph`): two distinct vertices are adjacent when an edge joins
them in either direction.

This module holds the tools these problems share:

* adjacency is tested in polynomial time (`Cslib.Complexity.Graph.adjBool`);
* a vertex subset problem with a pairwise condition, such as independent set or clique, is
  verified by selecting distinct declared vertices with a certificate mask
  (`Cslib.Complexity.Graph.verifySubset`, an instance of `Cslib.Complexity.subsetVerifier`);
* the distinct declared vertices (`Cslib.Complexity.Graph.distinctVertices`) are listed in
  polynomial time by selecting every first occurrence (`Cslib.Complexity.selectDistinct`);
* explicit verifiers with fixed certificate lengths write numbers in unary blocks of a certificate
  (`Cslib.Complexity.unaryBlocks`): each number, at most `m`, gets its own block of `m` bits, and
  it is read back by counting the set bits of its block (`Cslib.Complexity.countP_unaryBlocks`).

## Main definitions

* `Cslib.Complexity.Graph`, `Cslib.Complexity.encGraph`, `Cslib.Complexity.Graph.toSimpleGraph`.
* `Cslib.Complexity.Graph.adjBool`: executable adjacency.
* `Cslib.Complexity.Graph.verifySubset`: the verifier of a vertex subset problem.
* `Cslib.Complexity.Graph.distinctVertices`: the declared vertices without repetitions.
* `Cslib.Complexity.unaryBlocks`: numbers written in unary blocks of a certificate.

## Main results

* `Cslib.Complexity.Graph.toSimpleGraph_adj`, `Cslib.Complexity.Graph.adjBool_eq_true_iff`:
  adjacency.
* `Cslib.Complexity.Graph.isVerifier_verifySubset`,
  `Cslib.Complexity.Graph.computableTidilyInPolyTime_verifySubset`: the subset verifier is a
  polynomial-time verifier.
* `Cslib.Complexity.Graph.length_vertices_le_encGraph`: a graph has no more declared vertices than
  the length of its encoding.
* `Cslib.Complexity.countP_unaryBlocks`: counting the set bits of a block reads its number.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 2.4][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableTidilyInPolyTime

/-- A graph on natural numbers, given by its vertices and its edges. -/
abbrev Graph : Type := List ℕ × List (ℕ × ℕ)

/-- Graphs encoded by framed lists of binary vertex labels and binary edge pairs. -/
def encGraph : Graph ↪ List Bool :=
  encPair (encList encNat) (encList (encPair encNat encNat))

/-- The simple graph of an edge list: two distinct vertices are adjacent when an edge joins them,
in either direction. -/
def Graph.toSimpleGraph (G : Graph) : SimpleGraph ℕ := SimpleGraph.fromRel fun u v => (u, v) ∈ G.2


/-- Adjacency in the simple graph of an edge list: two distinct vertices joined by an edge in
either direction. It is not a `simp` lemma, so that the adjacency stays folded until a proof
unfolds it. -/
theorem Graph.toSimpleGraph_adj {G : Graph} {u v : ℕ} :
    G.toSimpleGraph.Adj u v ↔ u ≠ v ∧ ((u, v) ∈ G.2 ∨ (v, u) ∈ G.2) :=
  SimpleGraph.fromRel_adj _ _ _

namespace Graph

/-! ### Subset verification on encoded graphs -/

/-- Executable adjacency test on an edge list: two distinct vertices are adjacent when an edge
joins them in either direction. -/
def adjBool (G : Graph) (u v : ℕ) : Bool :=
  decide (u ≠ v) &&
    (G.2.any (fun e => decide (e = (u, v))) || G.2.any (fun e => decide (e = (v, u))))

@[simp]
theorem adjBool_eq_true_iff (G : Graph) (u v : ℕ) :
    G.adjBool u v = true ↔ G.toSimpleGraph.Adj u v := by
  simp [adjBool, toSimpleGraph, SimpleGraph.fromRel_adj]

@[simp]
theorem adjBool_eq_false_iff (G : Graph) (u v : ℕ) :
    G.adjBool u v = false ↔ ¬G.toSimpleGraph.Adj u v := by
  rw [← Bool.not_eq_true, ← adjBool_eq_true_iff, Bool.not_eq_true]

/-- Testing adjacency in an encoded graph is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_adjBool :
    ComputableTidilyInPolyTime (fun p : (Graph × ℕ) × ℕ => p.1.1.adjBool p.1.2 p.2)
      (encPair (encPair encGraph encNat) encNat) encBool := by
  unfold adjBool encGraph
  fun_prop

/-- Select distinct declared vertices from `V` using the certificate mask `w`: position `i` of `V`
is kept when bit `i` of `w` is `true` and `i` is the first occurrence of that vertex in `V`. This is
`Cslib.Complexity.selectDistinct` on vertex lists (`selectVertices_eq_selectDistinct`). -/
def selectVertices (V : List ℕ) (w : List Bool) : List ℕ :=
  (V.zipIdx.filter fun p => w.getD p.2 false && decide (V.idxOf p.1 = p.2)).map Prod.fst

theorem selectVertices_eq_selectDistinct : selectVertices = selectDistinct := rfl

theorem mem_selectVertices {V : List ℕ} {w : List Bool} {v : ℕ} :
    v ∈ selectVertices V w ↔ v ∈ V ∧ w.getD (V.idxOf v) false = true :=
  mem_selectDistinct

theorem nodup_selectVertices (V : List ℕ) (w : List Bool) : (selectVertices V w).Nodup :=
  nodup_selectDistinct V w

/-- Selecting distinct declared vertices from a certificate mask is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_selectVertices :
    ComputableTidilyInPolyTime (fun p : List ℕ × List Bool => selectVertices p.1 p.2)
      (encPair (encList encNat) encBits) (encList encNat) :=
  computableTidilyInPolyTime_selectDistinct encNat

/-- Verify a cardinality-`m` vertex subset problem with pairwise relation `rel`: select distinct
declared vertices from `G.1` by the certificate mask, compare the selected count with `m` in
binary, and test `rel` on all distinct selected pairs. -/
def verifySubset (rel : Graph → ℕ → ℕ → Bool) : (Graph × ℕ) × List Bool → Bool :=
  subsetVerifier (fun x => x.1.1) fun y =>
    decide (y.2.length = y.1.2) && y.2.all fun u => y.2.all fun v => decide (u = v) || rel y.1.1 u v

/-- A graph has no more declared vertices than the length of its encoded instance. -/
theorem length_vertices_le (x : Graph × ℕ) :
    x.1.1.length ≤ (encPair encGraph encNat x).length := by
  calc x.1.1.length
      ≤ (encList encNat x.1.1).length := length_le_length_encList encNat x.1.1
    _ ≤ (encGraph x.1).length := by
        simp only [encGraph, length_encPair]
        omega
    _ ≤ (encPair encGraph encNat x).length := by
        simp only [length_encPair]
        omega

/-- `verifySubset` is a polynomial-length verifier for any graph subset problem whose pairwise
relation agrees with `rel` on distinct vertices. -/
theorem isVerifier_verifySubset {rel : Graph → ℕ → ℕ → Bool} {P : Graph → ℕ → ℕ → Prop}
    (hrel : ∀ G u v, u ≠ v → (rel G u v = true ↔ P G u v)) :
    IsVerifier (encPair encGraph encNat) Polynomial.X (verifySubset rel)
      {x | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.1.1) ∧ (S : Set ℕ).Pairwise (P x.1) ∧ S.card = x.2} := by
  refine isVerifier_subsetVerifier (fun x => by simpa using length_vertices_le x)
    fun x l hl _ => ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    List.toFinset_card_of_nodup hl, List.coe_toFinset]
  refine ⟨fun ⟨hlen, h⟩ => ⟨fun u hu v hv huv => ?_, hlen⟩,
    fun ⟨h, hlen⟩ => ⟨hlen, fun u hu v hv => ?_⟩⟩
  · exact (hrel x.1 u v huv).1 ((h u hu v hv).resolve_left huv)
  · by_cases huv : u = v
    · exact Or.inl huv
    · exact Or.inr ((hrel x.1 u v huv).2 (h hu hv huv))

@[fun_prop]
private theorem bool_or' {α : Type} {encA : α ↪ List Bool} {left right : α → Bool}
    (hleft : ComputableTidilyInPolyTime left encA encBool)
    (hright : ComputableTidilyInPolyTime right encA encBool) :
    ComputableTidilyInPolyTime (fun a => left a || right a) encA encBool :=
  bool_or.comp (hleft.prod hright)

/-- `verifySubset` is computable in polynomial time whenever the pairwise test `rel` is. -/
@[fun_prop]
theorem computableTidilyInPolyTime_verifySubset {rel : Graph → ℕ → ℕ → Bool}
    (hrel : ComputableTidilyInPolyTime (fun p : (Graph × ℕ) × ℕ => rel p.1.1 p.1.2 p.2)
      (encPair (encPair encGraph encNat) encNat) encBool) :
    ComputableTidilyInPolyTime (verifySubset rel)
      (encPair (encPair encGraph encNat) encBits) encBool := by
  refine computableTidilyInPolyTime_subsetVerifier (encγ := encNat)
    (by unfold encGraph; fun_prop) (bool_and' ?_ ?_)
  · exact (((ComputableInPolyTime.length_list_binary encNat).tidy.comp (snd _ _)).decide_eq'
      (by fun_prop))
  · apply allWithInput (snd _ _)
    apply allWithInput ((snd _ _).comp (fst _ _))
    have hproj : ComputableTidilyInPolyTime
        (fun p : (((Graph × ℕ) × List ℕ) × ℕ) × ℕ => ((p.1.1.1.1, p.1.2), p.2))
        (encPair (encPair (encPair (encPair encGraph encNat) (encList encNat)) encNat) encNat)
        (encPair (encPair encGraph encNat) encNat) := by fun_prop
    exact bool_or' (by fun_prop) (hrel.comp hproj)

end Graph

namespace Graph

/-! ### Declared vertices -/

/-- A graph has no more declared vertices than the length of its encoding. -/
theorem length_vertices_le_encGraph (G : Graph) : G.1.length ≤ (encGraph G).length := by
  calc G.1.length ≤ (encList encNat G.1).length := length_le_length_encList encNat G.1
    _ ≤ (encGraph G).length := by
        simp only [encGraph, length_encPair]
        omega

/-- The declared vertices of `G` without repetitions, in the order of their first occurrences. -/
def distinctVertices (G : Graph) : List ℕ := selectDistinct G.1 (List.replicate G.1.length true)

/-- The distinct declared vertices are the declared vertices. -/
theorem mem_distinctVertices {G : Graph} {v : ℕ} : v ∈ G.distinctVertices ↔ v ∈ G.1 :=
  mem_selectDistinct_replicate

/-- The distinct declared vertices are listed without repetitions. -/
theorem nodup_distinctVertices (G : Graph) : G.distinctVertices.Nodup := nodup_selectDistinct _ _

/-- The distinct declared vertices are as many as the elements of the vertex list. -/
theorem length_distinctVertices (G : Graph) : G.distinctVertices.length = G.1.toFinset.card :=
  length_selectDistinct_replicate G.1

/-- A graph has no more distinct vertices than the length of its encoding. -/
theorem length_distinctVertices_le (G : Graph) :
    G.distinctVertices.length ≤ (encGraph G).length := by
  rw [length_distinctVertices]
  exact G.1.toFinset_card_le.trans G.length_vertices_le_encGraph

/-- Listing the distinct vertices is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_distinctVertices :
    ComputableTidilyInPolyTime distinctVertices encGraph (encList encNat) := by
  unfold distinctVertices encGraph
  fun_prop

end Graph

/-! ### Unary blocks -/

/-- The certificate of `N` bits writing the numbers `f a` in unary blocks of width `m`: bit
`m * a + c` is set when `c < f a`. -/
def unaryBlocks (m N : ℕ) (f : ℕ → ℕ) : List Bool :=
  (List.range N).map fun j => decide (j % m < f (j / m))

@[simp]
theorem length_unaryBlocks (m N : ℕ) (f : ℕ → ℕ) : (unaryBlocks m N f).length = N := by
  simp [unaryBlocks]

/-- Counting the set bits of block `a` of `unaryBlocks m N f` reads `f a`, when `f a` fits in the
block and the block fits in the certificate. -/
theorem countP_unaryBlocks {m N a : ℕ} {f : ℕ → ℕ} (hf : f a ≤ m) (hN : m * (a + 1) ≤ N) :
    ((List.range m).countP fun c => (unaryBlocks m N f).getD (m * a + c) false) = f a := by
  have hcount : ∀ k, (List.range k).countP (fun c => decide (c < f a)) = min (f a) k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [List.range_succ, List.countP_append, ih, List.countP_singleton,
        decide_eq_true_eq]
      split_ifs <;> omega
  rw [← min_eq_left hf, ← hcount]
  refine List.countP_congr fun c hc => ?_
  rw [List.mem_range] at hc
  have hm : 0 < m := by omega
  have hlt : m * a + c < N := by
    calc m * a + c < m * (a + 1) := by rw [Nat.mul_succ]; omega
      _ ≤ N := hN
  have hdiv : (m * a + c) / m = a := by rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hc, Nat.add_zero]
  have hmod : (m * a + c) % m = c := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc]
  simp only [unaryBlocks, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt,
    Option.map_some, Option.getD_some, hdiv, hmod]

end Cslib.Complexity
