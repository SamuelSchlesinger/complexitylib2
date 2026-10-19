/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.IndependentSet
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

A set of declared vertices is a vertex cover exactly when the remaining declared vertices form an
independent set (`SimpleGraph.isIndepSet_compl_iff_isVertexCover`), so
`IndependentSet.toVertexCover` maps `(G, m)` to `(G, n - m)`, where `n` is the number of distinct
declared vertices; a target `m > n` is mapped to the unsatisfiable target `n + 1` [Karp1972].

## Main definitions

* `Cslib.Complexity.VertexCover`.
* `Cslib.Complexity.VertexCover.verifier`.
* `Cslib.Complexity.IndependentSet.toVertexCover`.

## Main results

* `Cslib.Complexity.IndependentSet.toVertexCover_mem_iff`:
  `toVertexCover x ∈ VertexCover ↔ x ∈ IndependentSet`.
* `Cslib.Complexity.IndependentSet.computableTidilyInPolyTime_toVertexCover`: the reduction is
  polynomial-time, with targets in binary.
* `Cslib.Complexity.VertexCover.isVerifier`, `Cslib.Complexity.VertexCover.mem_NP`:
  `VertexCover ∈ NP (encPair encGraph encNat)`.
* `Cslib.Complexity.polyTimeReducible_IndependentSet_VertexCover`,
  `Cslib.Complexity.VertexCover_npHard`, `Cslib.Complexity.VertexCover_npComplete`:
  `VertexCover` is `NP`-complete.

## References

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

theorem mem_VertexCover_iff {G : Graph} {k : ℕ} :
    (G, k) ∈ VertexCover ↔ ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ G.1) ∧
      (∀ u ∈ G.1, ∀ v ∈ G.1, G.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = k := by
  refine exists_congr fun S => and_congr_right fun _ => and_congr_left fun _ => ?_
  exact ⟨fun h u hu v hv huv => @h ⟨u, hu⟩ ⟨v, hv⟩ huv, fun h u v huv => h u u.2 v v.2 huv⟩

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

/-- The number of distinct declared vertices is the length of the deduplicated vertex list. -/
private theorem card_toFinset_eq (V : List ℕ) :
    V.toFinset.card = (Graph.selectVertices V (List.replicate V.length true)).length := by
  rw [← List.toFinset_card_of_nodup (Graph.nodup_selectVertices V _)]
  congr 1
  ext v
  simp only [List.mem_toFinset, Graph.mem_selectVertices, iff_self_and]
  intro hv
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate,
    ite_eq_left (List.idxOf_lt_length_iff.2 hv), Option.getD_some]

/-- The reduction `toVertexCover` is polynomial-time: the vertex count is computed in unary, and
the binary target is compared with it by saturating decoding. -/
@[fun_prop]
theorem computableTidilyInPolyTime_toVertexCover :
    ComputableTidilyInPolyTime toVertexCover (encPair encGraph encNat)
      (encPair encGraph encNat) := by
  have hn : ComputableTidilyInPolyTime (fun x : Graph × ℕ => x.1.1.toFinset.card)
      (encPair encGraph encNat) encUnary := by
    simp_rw [card_toFinset_eq]
    have := bitsReplicate true
    unfold encGraph
    fun_prop
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

/-- The verifier for `VertexCover`: select distinct declared vertices from the certificate mask,
check that their count equals `k`, and check that every edge between declared vertices has a
selected endpoint. A declared vertex is selected exactly when the mask bit at its first
occurrence is set. -/
def verifier (x : (Graph × ℕ) × List Bool) : Bool :=
  decide ((Graph.selectVertices x.1.1.1 x.2).length = x.1.2) &&
    x.1.1.1.all fun u => x.1.1.1.all fun v =>
      !(x.1.1.adjBool u v && !x.2.getD (x.1.1.1.idxOf u) false &&
        !x.2.getD (x.1.1.1.idxOf v) false)

/-- `VertexCover.verifier` verifies `VertexCover` with certificates as long as the encoded
instance. -/
theorem isVerifier :
    IsVerifier (encPair encGraph encNat) Polynomial.X verifier VertexCover := by
  classical
  rintro ⟨G, k⟩
  simp only [mem_VertexCover_iff, Polynomial.eval_X, verifier, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    Bool.not_eq_false', Graph.adjBool_eq_false_iff]
  constructor
  · rintro ⟨S, hSV, hS, hcard⟩
    let w := G.1.map (fun v => decide (v ∈ S)) ++
      List.replicate ((encPair encGraph encNat (G, k)).length - G.1.length) false
    have hw : ∀ v ∈ G.1, w.getD (G.1.idxOf v) false = decide (v ∈ S) := by
      intro v hv
      have hlt : G.1.idxOf v < G.1.length := List.idxOf_lt_length_iff.2 hv
      have hlt' : G.1.idxOf v < (G.1.map fun u => decide (u ∈ S)).length := by simpa using hlt
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt', List.getElem?_map,
        List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]
      rfl
    have htoFinset : (Graph.selectVertices G.1 w).toFinset = S := by
      ext v
      rw [List.mem_toFinset, Graph.mem_selectVertices]
      refine ⟨fun ⟨hv, h⟩ => ?_, fun hv => ⟨hSV v hv, ?_⟩⟩
      · rw [hw v hv] at h
        exact of_decide_eq_true h
      · rw [hw v (hSV v hv)]
        exact decide_eq_true hv
    refine ⟨w, ?_, ?_, fun u hu v hv => ?_⟩
    · simp only [w, List.length_append, List.length_map, List.length_replicate]
      exact Nat.add_sub_cancel' (Graph.length_vertices_le (G, k))
    · rw [← List.toFinset_card_of_nodup (Graph.nodup_selectVertices G.1 w), htoFinset, hcard]
    · rw [hw u hu, hw v hv]
      by_cases hadj : G.toSimpleGraph.Adj u v
      · rcases hS u hu v hv hadj with h | h <;> simp [h]
      · exact Or.inl (Or.inl hadj)
  · rintro ⟨w, -, hlen, hw⟩
    refine ⟨(Graph.selectVertices G.1 w).toFinset,
      fun v hv => (Graph.mem_selectVertices.1 (List.mem_toFinset.1 hv)).1,
      fun u hu v hv hadj => ?_, ?_⟩
    · simp only [List.mem_toFinset, Graph.mem_selectVertices]
      rcases hw u hu v hv with (h | h) | h
      · exact (h hadj).elim
      · exact Or.inl ⟨hu, h⟩
      · exact Or.inr ⟨hv, h⟩
    · rw [List.toFinset_card_of_nodup (Graph.nodup_selectVertices G.1 w), hlen]

/-- The `VertexCover` verifier is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_verifier :
    ComputableTidilyInPolyTime verifier (encPair (encPair encGraph encNat) encBits) encBool := by
  have hV : ComputableTidilyInPolyTime (fun x : (Graph × ℕ) × List Bool => x.1.1.1)
      (encPair (encPair encGraph encNat) encBits) (encList encNat) := by
    unfold encGraph
    fun_prop
  have hS : ComputableTidilyInPolyTime
      (fun x : (Graph × ℕ) × List Bool => Graph.selectVertices x.1.1.1 x.2)
      (encPair (encPair encGraph encNat) encBits) (encList encNat) := by
    unfold encGraph
    fun_prop
  have hcard : ComputableTidilyInPolyTime
      (fun x : (Graph × ℕ) × List Bool =>
        decide ((Graph.selectVertices x.1.1.1 x.2).length = x.1.2))
      (encPair (encPair encGraph encNat) encBits) encBool :=
    (unary_to_binary.comp ((length_list encNat).comp hS)).decide_eq'
      (by unfold encGraph; fun_prop)
  have hproj : ComputableTidilyInPolyTime
      (fun p : (((Graph × ℕ) × List Bool) × ℕ) × ℕ => ((p.1.1.1.1, p.1.2), p.2))
      (encPair (encPair (encPair (encPair encGraph encNat) encBits) encNat) encNat)
      (encPair (encPair encGraph encNat) encNat) := by fun_prop
  have hadj := Graph.computableTidilyInPolyTime_adjBool.comp hproj
  refine hcard.bool_and' (allWithInput hV (allWithInput (hV.comp (fst _ _)) ?_))
  unfold encGraph at hadj ⊢
  fun_prop

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

end Cslib.Complexity
