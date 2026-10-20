/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Vertex covers

`VertexCover` is the set of graphs, given by a list of vertices and a list of edges, together with
a number `k`, such that `k` of the declared vertices meet every edge between declared vertices
[Karp1972]. Graphs are read through `Cslib.Complexity.Graph.toSimpleGraph` restricted to the
declared vertices (`SimpleGraph.induce`), and covers through `SimpleGraph.IsVertexCover`. Edges
with an undeclared endpoint and self-loops are therefore ignored, and repeated vertex entries
count once.

The cover has exactly `k` distinct vertices, matching `IndependentSet`. Since a set of declared
vertices containing a cover is a cover, this agrees with the textbook formulation "a cover of at
most `k` vertices" for every `k` up to the number `n` of distinct declared vertices, and
`VertexCover` rejects every `k > n` (`mem_VertexCover_iff_exists_card_le`). In particular a graph
without declared vertices belongs to `VertexCover` only with `k = 0`.

A set of declared vertices is a vertex cover exactly when the remaining declared vertices form an
independent set (`SimpleGraph.isIndepSet_compl_iff_isVertexCover`), so
`IndependentSet.toVertexCover` maps `(G, m)` to `(G, n - m)`, where `n` is the number of distinct
declared vertices; a target `m > n` is mapped to the unsatisfiable target `n + 1` [Karp1972].

The same problem as a class of finite structures, closed under isomorphism and without an
encoding, with the target size given by a unary relation, is
`Cslib.Logic.FO.sizedGraph.VertexCover`. There loops are ignored, edges need not be symmetric,
and the reductions between independent set, clique and vertex cover are quantifier-free
first-order interpretations.

## Main definitions

* `Cslib.Complexity.VertexCover`.
* `Cslib.Complexity.VertexCover.verifier`.
* `Cslib.Complexity.IndependentSet.toVertexCover`.
* `Cslib.Complexity.Graph.vertexCoverNum`: the vertex cover number.

## Main results

* `Cslib.Complexity.mem_VertexCover_iff_exists_card_le`: covers of exactly `k` vertices versus
  covers of at most `k` vertices.
* `Cslib.Complexity.IndependentSet.toVertexCover_mem_iff`:
  `toVertexCover x ∈ VertexCover ↔ x ∈ IndependentSet`.
* `Cslib.Complexity.Graph.vertexCoverNum_eq_card_sub_indepNum`: the vertex cover number is the
  number of distinct declared vertices minus the independence number.
* `Cslib.Complexity.IndependentSet.computableTidilyInPolyTime_toVertexCover`: the reduction is
  polynomial-time, with targets in binary.
* `Cslib.Complexity.VertexCover.isVerifier`, `Cslib.Complexity.VertexCover.mem_NP`:
  `VertexCover ∈ NP (encPair encGraph encNat)`.
* `Cslib.Complexity.polyTimeReducible_IndependentSet_VertexCover`,
  `Cslib.Complexity.VertexCover_npHard`, `Cslib.Complexity.VertexCover_npComplete`:
  `VertexCover` is `NP`-complete.

## References

* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979]
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableTidilyInPolyTime

/-- The graphs with a vertex cover of `k` of their vertices: `k` declared vertices meeting every
edge between two declared vertices. -/
def VertexCover : Set (Graph × ℕ) :=
  {x | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.1.1) ∧
    (x.1.toSimpleGraph.induce {v | v ∈ x.1.1}).IsVertexCover {v | ↑v ∈ S} ∧ S.card = x.2}

/-- Membership in `VertexCover` as a finite set of `k` declared vertices meeting every edge between
declared vertices. -/
theorem mem_VertexCover_iff {G : Graph} {k : ℕ} :
    (G, k) ∈ VertexCover ↔ ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ G.1) ∧
      (∀ u ∈ G.1, ∀ v ∈ G.1, G.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = k := by
  refine exists_congr fun S => and_congr_right fun _ => and_congr_left fun _ => ?_
  exact ⟨fun h u hu v hv huv => @h ⟨u, hu⟩ ⟨v, hv⟩ huv, fun h u v huv => h u u.2 v v.2 huv⟩

/-- `VertexCover` through covers of at most `k` vertices: `(G, k) ∈ VertexCover` exactly when `k`
is at most the number of distinct declared vertices and some cover has at most `k` vertices. -/
theorem mem_VertexCover_iff_exists_card_le {G : Graph} {k : ℕ} :
    (G, k) ∈ VertexCover ↔ k ≤ G.1.toFinset.card ∧ ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ G.1) ∧
      (∀ u ∈ G.1, ∀ v ∈ G.1, G.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card ≤ k := by
  rw [mem_VertexCover_iff]
  constructor
  · rintro ⟨S, hSV, hS, rfl⟩
    exact ⟨Finset.card_le_card fun v hv => List.mem_toFinset.2 (hSV v hv), S, hSV, hS, le_rfl⟩
  · rintro ⟨hk, S, hSV, hS, hcard⟩
    obtain ⟨T, hST, hTV, hT⟩ := Finset.exists_subsuperset_card_eq
      (fun v hv => List.mem_toFinset.2 (hSV v hv)) hcard hk
    exact ⟨T, fun v hv => List.mem_toFinset.1 (hTV hv),
      fun u hu v hv huv => (hS u hu v hv huv).imp (@hST u) (@hST v), hT⟩

namespace IndependentSet

/-! ### Reduction from independent sets -/

/-- The reduction from `IndependentSet` to `VertexCover`: keep the graph and replace the target
`m` by `n - m`, where `n` is the number of distinct declared vertices, or by `n + 1` when `m > n`.
-/
def toVertexCover (x : Graph × ℕ) : Graph × ℕ :=
  (x.1, if x.2 ≤ x.1.1.toFinset.card then x.1.1.toFinset.card - x.2 else x.1.1.toFinset.card + 1)

/-- **Independent sets are complements of vertex covers.** -/
theorem toVertexCover_mem_iff (x : Graph × ℕ) :
    toVertexCover x ∈ VertexCover ↔ x ∈ IndependentSet := by
  classical
  obtain ⟨G, m⟩ := x
  simp only [toVertexCover, mem_VertexCover_iff]
  have hsub : ∀ {S : Finset ℕ}, (∀ v ∈ S, v ∈ G.1) → S ⊆ G.1.toFinset :=
    fun hS v hv => List.mem_toFinset.2 (hS v hv)
  split_ifs with hm
  · constructor
    · rintro ⟨T, hTV, hT, hcard⟩
      refine ⟨G.1.toFinset \ T, fun v hv => List.mem_toFinset.1 (Finset.mem_sdiff.1 hv).1,
        ⟨fun u hu v hv huv hadj => ?_, ?_⟩⟩
      · simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, List.mem_toFinset] at hu hv
        rcases hT u hu.1 v hv.1 hadj with h | h
        · exact hu.2 h
        · exact hv.2 h
      · rw [Finset.card_sdiff_of_subset (hsub hTV), hcard]
        omega
    · rintro ⟨S, hSV, hS, hcard⟩
      refine ⟨G.1.toFinset \ S, fun v hv => List.mem_toFinset.1 (Finset.mem_sdiff.1 hv).1,
        fun u hu v hv hadj => ?_, ?_⟩
      · by_contra h
        simp only [Finset.mem_sdiff, List.mem_toFinset, not_or, not_and, not_not] at h
        exact hS (h.1 hu) (h.2 hv) hadj.ne hadj
      · rw [Finset.card_sdiff_of_subset (hsub hSV), hcard]
  · refine ⟨fun ⟨T, hTV, _, hcard⟩ => ?_, fun ⟨S, hSV, hS⟩ => ?_⟩
    · have := Finset.card_le_card (hsub hTV)
      omega
    · have := Finset.card_le_card (hsub hSV)
      rw [hS.card_eq] at this
      exact (hm this).elim

/-- The reduction `toVertexCover` is polynomial-time: the vertex count is computed in unary, and
the binary target is compared with it by saturating decoding. -/
@[fun_prop]
theorem computableTidilyInPolyTime_toVertexCover :
    ComputableTidilyInPolyTime toVertexCover (encPair encGraph encNat)
      (encPair encGraph encNat) := by
  have hn : ComputableTidilyInPolyTime (fun x : Graph × ℕ => x.1.1.toFinset.card)
      (encPair encGraph encNat) encUnary := by
    simp_rw [← Graph.length_distinctVertices]
    exact (length_list encNat).comp
      (Graph.computableTidilyInPolyTime_distinctVertices.comp (fst _ _))
  -- `min n m`, decoded from the binary target under the unary cap `n`.
  have hmin : ComputableTidilyInPolyTime
      (fun x : Graph × ℕ => Cslib.BitString.boundedBinaryValue x.1.1.toFinset.card
        (encNat x.2).reverse) (encPair encGraph encNat) encUnary :=
    bitsBoundedBinaryValueWithInput hn (bitsReverse.comp ((encode encNat).comp (snd _ _)))
  have heq : toVertexCover = fun x : Graph × ℕ =>
      (x.1, if Cslib.BitString.boundedBinaryValue x.1.1.toFinset.card (encNat x.2).reverse = x.2
        then x.1.1.toFinset.card -
          Cslib.BitString.boundedBinaryValue x.1.1.toFinset.card (encNat x.2).reverse
        else x.1.1.toFinset.card + 1) := by
    funext x
    simp only [toVertexCover, encNat_apply, Cslib.BitString.boundedBinaryValue_eq,
      Cslib.BitString.binaryValue_reverse_bits, min_eq_right_iff]
    split_ifs with h
    · rw [min_eq_right h]
    · rfl
  rw [heq]
  refine (fst _ _).prod (ite_decide ((unary_to_binary.comp hmin).decide_eq' (snd _ _))
    (unary_to_binary.comp (unary_sub.comp (hn.prod hmin)))
    (unary_to_binary.comp (unary_add.comp (hn.prod (const 1)))))

end IndependentSet

namespace VertexCover

/-- The verifier for `VertexCover`, a subset verifier (`Cslib.Complexity.subsetVerifier`): select
distinct declared vertices by the certificate mask, check that their count equals `k`, and check
that every edge between declared vertices has a selected endpoint. -/
def verifier : (Graph × ℕ) × List Bool → Bool :=
  subsetVerifier (fun x => x.1.1) fun y =>
    decide (y.2.length = y.1.2) && y.1.1.1.all fun u => y.1.1.1.all fun v =>
      !(y.1.1.adjBool u v && !y.2.any (fun w => decide (w = u)) &&
        !y.2.any (fun w => decide (w = v)))

/-- `VertexCover.verifier` verifies `VertexCover` with certificates as long as the encoded
instance. -/
theorem isVerifier :
    IsVerifier (encPair encGraph encNat) Polynomial.X verifier VertexCover := by
  have hset : VertexCover = {x | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.1.1) ∧
      (∀ u ∈ x.1.1, ∀ v ∈ x.1.1, x.1.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = x.2} :=
    Set.ext fun _ => mem_VertexCover_iff
  rw [hset]
  refine isVerifier_subsetVerifier (fun x => by simpa using Graph.length_vertices_le x)
    fun x l hl _ => ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, Bool.not_eq_false', List.any_eq_true, exists_eq_right,
    Graph.adjBool_eq_false_iff, List.mem_toFinset, List.toFinset_card_of_nodup hl]
  refine and_comm.trans (and_congr_left' ⟨fun h u hu v hv huv => ?_, fun h u hu v hv => ?_⟩)
  · rcases h u hu v hv with (h | h) | h
    · exact (h huv).elim
    · exact Or.inl h
    · exact Or.inr h
  · by_cases huv : x.1.toSimpleGraph.Adj u v
    · exact (h u hu v hv huv).elim (fun h => Or.inl (Or.inr h)) Or.inr
    · exact Or.inl (Or.inl huv)

/-- The `VertexCover` verifier is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_verifier :
    ComputableTidilyInPolyTime verifier (encPair (encPair encGraph encNat) encBits) encBool := by
  have hV : ComputableTidilyInPolyTime (fun y : (Graph × ℕ) × List ℕ => y.1.1.1)
      (encPair (encPair encGraph encNat) (encList encNat)) (encList encNat) := by
    unfold encGraph
    fun_prop
  have hproj : ComputableTidilyInPolyTime
      (fun p : (((Graph × ℕ) × List ℕ) × ℕ) × ℕ => ((p.1.1.1.1, p.1.2), p.2))
      (encPair (encPair (encPair (encPair encGraph encNat) (encList encNat)) encNat) encNat)
      (encPair (encPair encGraph encNat) encNat) := by fun_prop
  have hadj := Graph.computableTidilyInPolyTime_adjBool.comp hproj
  refine computableTidilyInPolyTime_subsetVerifier (encγ := encNat) (by unfold encGraph; fun_prop)
    (bool_and' ?_ (allWithInput hV (allWithInput (hV.comp (fst _ _)) ?_)))
  · exact (unary_to_binary.comp ((length_list encNat).comp (snd _ _))).decide_eq' (by fun_prop)
  · fun_prop

/-- `VertexCover` belongs to `NP`. -/
theorem mem_NP : VertexCover ∈ NP (encPair encGraph encNat) :=
  ⟨Polynomial.X, verifier, computableTidilyInPolyTime_verifier, isVerifier⟩

end VertexCover

/-- `IndependentSet` reduces to `VertexCover` in polynomial time via
`IndependentSet.toVertexCover`. -/
theorem polyTimeReducible_IndependentSet_VertexCover :
    PolyTimeReducible (encPair encGraph encNat) (encPair encGraph encNat) IndependentSet
      VertexCover :=
  ⟨IndependentSet.toVertexCover, IndependentSet.computableTidilyInPolyTime_toVertexCover,
    fun x => (IndependentSet.toVertexCover_mem_iff x).symm⟩

/-- `VertexCover` is `NP`-hard. -/
theorem VertexCover_npHard : NPHard (encPair encGraph encNat) VertexCover :=
  IndependentSet_npHard.trans polyTimeReducible_IndependentSet_VertexCover

/-- **`VertexCover` is NP-complete.** -/
theorem VertexCover_npComplete : NPComplete (encPair encGraph encNat) VertexCover :=
  ⟨VertexCover.mem_NP, VertexCover_npHard⟩

/-! ### The vertex cover number -/

namespace Graph

/-- The **vertex cover number** of a graph: the least number of declared vertices meeting every
edge between declared vertices. -/
noncomputable def vertexCoverNum (G : Graph) : ℕ := sInf {k | (G, k) ∈ VertexCover}

/-- **A vertex cover is the complement of an independent set**: the vertex cover number is the
number of distinct declared vertices minus the independence number. -/
theorem vertexCoverNum_eq_card_sub_indepNum (G : Graph) :
    G.vertexCoverNum = G.1.toFinset.card - G.indepNum := by
  have hα := indepNum_mem_IndependentSet G
  have hαn := indepNum_le_card G
  have hvc : (G, G.1.toFinset.card - G.indepNum) ∈ VertexCover := by
    have := (IndependentSet.toVertexCover_mem_iff (G, G.indepNum)).2 hα
    rwa [IndependentSet.toVertexCover, ite_eq_left hαn] at this
  refine le_antisymm (Nat.sInf_le hvc) ?_
  have hτ : (G, G.vertexCoverNum) ∈ VertexCover :=
    Nat.sInf_mem (s := {k | (G, k) ∈ VertexCover}) ⟨_, hvc⟩
  have hτn : G.vertexCoverNum ≤ G.1.toFinset.card := (mem_VertexCover_iff_exists_card_le.1 hτ).1
  have hIS : (G, G.1.toFinset.card - G.vertexCoverNum) ∈ IndependentSet := by
    refine (IndependentSet.toVertexCover_mem_iff _).1 ?_
    rwa [IndependentSet.toVertexCover, ite_eq_left (Nat.sub_le _ _), Nat.sub_sub_self hτn]
  have := le_indepNum_iff.2 hIS
  omega

end Graph

end Cslib.Complexity
