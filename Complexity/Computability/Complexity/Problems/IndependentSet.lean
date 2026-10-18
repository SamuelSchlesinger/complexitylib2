/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Computability.Complexity.Reduction
public import Mathlib.Combinatorics.SimpleGraph.Clique
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Independent sets

`IndependentSet` is the set of graphs, given by a list of vertices and a list of edges, together
with a number `m`, such that the graph has an independent set of `m` vertices [Arora and Barak,
Section 2.4][AroraBarak09]. Graphs are read through Mathlib's `SimpleGraph.fromRel`, and independent
sets through `SimpleGraph.IsNIndepSet`.

The reduction `SAT.toIndependentSet` from `SAT` is Karp's: one vertex for each occurrence of a
literal, edges between occurrences in the same clause and between complementary occurrences, and
`m` the number of clauses [Karp1972]. An independent set with one vertex in each clause picks a
literal in each clause without contradictions, which is exactly a satisfying assignment.

Vertices and target sizes use binary encoding (`encNat`). A certificate masks the declared vertex
list at first occurrences so duplicate vertex entries cannot inflate the selected set, and checks
the selected count in binary without unary expansion of `m`.

## Main definitions

* `Cslib.Complexity.Graph.toSimpleGraph`, `Cslib.Complexity.encGraph`,
  `Cslib.Complexity.IndependentSet`.
* `Cslib.Complexity.Graph.adjBool`, `Cslib.Complexity.Graph.selectVertices`,
  `Cslib.Complexity.Graph.verifySubset`.
* `Cslib.Complexity.IndependentSet.verifier`.
* `Cslib.Complexity.SAT.toIndependentSet`.

## Main results

* `Cslib.Complexity.SAT.toIndependentSet_mem_iff`: `toIndependentSet φ ∈ IndependentSet ↔ φ ∈ SAT`.
* `Cslib.Complexity.SAT.computableTidilyInPolyTime_toIndependentSet`: Karp's reduction is
  polynomial-time.
* `Cslib.Complexity.IndependentSet.isVerifier`, `Cslib.Complexity.IndependentSet.mem_NP`:
  `IndependentSet ∈ NP (encPair encGraph encNat)`.
* `Cslib.Complexity.polyTimeReducible_SAT_IndependentSet`,
  `Cslib.Complexity.IndependentSet_npHard`, `Cslib.Complexity.IndependentSet_npComplete`:
  `IndependentSet` is `NP`-complete.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM ComputableTidilyInPolyTime

/-- A graph on natural numbers, given by its vertices and its edges. -/
abbrev Graph : Type := List ℕ × List (ℕ × ℕ)

/-- Graphs encoded by framed lists of binary vertex labels and binary edge pairs. -/
def encGraph : Graph ↪ List Bool :=
  encPair (encList encNat) (encList (encPair encNat encNat))

/-- The simple graph of an edge list: two distinct vertices are adjacent when an edge joins them,
in either direction. -/
def Graph.toSimpleGraph (G : Graph) : SimpleGraph ℕ := SimpleGraph.fromRel fun u v => (u, v) ∈ G.2

/-- The graphs with an independent set of `m` of their vertices. -/
def IndependentSet : Set (Graph × ℕ) :=
  {x | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.1.1) ∧ x.1.toSimpleGraph.IsNIndepSet x.2 S}

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
is kept when bit `i` of `w` is `true` and `i` is the first occurrence of that vertex in `V`. -/
def selectVertices (V : List ℕ) (w : List Bool) : List ℕ :=
  (V.zipIdx.filter fun p => w.getD p.2 false && decide (V.idxOf p.1 = p.2)).map Prod.fst

theorem mem_selectVertices {V : List ℕ} {w : List Bool} {v : ℕ} :
    v ∈ selectVertices V w ↔ v ∈ V ∧ w.getD (V.idxOf v) false = true := by
  simp only [selectVertices, List.mem_map, List.mem_filter, List.mem_zipIdx_iff_getElem?,
    Bool.and_eq_true, decide_eq_true_eq, Prod.exists]
  constructor
  · rintro ⟨u, i, ⟨hi, hw, hidx⟩, rfl⟩
    exact ⟨List.mem_of_getElem? hi, hidx ▸ hw⟩
  · rintro ⟨hv, hw⟩
    have hlt : V.idxOf v < V.length := List.idxOf_lt_length_iff.2 hv
    exact ⟨v, V.idxOf v, ⟨by simp [hlt], hw, rfl⟩, rfl⟩

theorem nodup_selectVertices (V : List ℕ) (w : List Bool) : (selectVertices V w).Nodup := by
  have hzip : V.zipIdx.Nodup := by
    rw [List.Nodup, List.pairwise_iff_getElem]
    intro i j hi hj hij h
    have := congrArg Prod.snd h
    simp only [List.getElem_zipIdx, Nat.zero_add] at this
    omega
  have hfilter := hzip.filter (fun p => w.getD p.2 false && decide (V.idxOf p.1 = p.2))
  refine hfilter.map_on ?_
  rintro ⟨u, i⟩ hu ⟨v, j⟩ hv (rfl : u = v)
  simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hu hv
  rw [← hu.2.2, ← hv.2.2]

/-- Selecting distinct declared vertices from a certificate mask is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_selectVertices :
    ComputableTidilyInPolyTime (fun p : List ℕ × List Bool => selectVertices p.1 p.2)
      (encPair (encList encNat) encBits) (encList encNat) := by
  unfold selectVertices
  fun_prop

/-- Verify a cardinality-`m` vertex subset problem with pairwise relation `rel`: select distinct
declared vertices from `G.1`, compare the selected count with `m` in binary, and test `rel` on all
distinct selected pairs. -/
def verifySubset (rel : Graph → ℕ → ℕ → Bool) (x : (Graph × ℕ) × List Bool) : Bool :=
  let S := selectVertices x.1.1.1 x.2
  decide (S.length = x.1.2) &&
    S.all fun u => S.all fun v => decide (u = v) || rel x.1.1 u v

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
  classical
  rintro ⟨G, m⟩
  simp only [Set.mem_ofPred_eq, Polynomial.eval_X, verifySubset]
  constructor
  · rintro ⟨S, hSV, hpair, hcard⟩
    let w := G.1.map (fun v => decide (v ∈ S)) ++
      List.replicate ((encPair encGraph encNat (G, m)).length - G.1.length) false
    have hw_len : w.length = (encPair encGraph encNat (G, m)).length := by
      dsimp only [w]
      rw [List.length_append, List.length_map, List.length_replicate,
        Nat.add_sub_cancel' (length_vertices_le (G, m))]
    have htoFinset : (selectVertices G.1 w).toFinset = S := by
      ext v
      rw [List.mem_toFinset, mem_selectVertices]
      constructor
      · rintro ⟨hv, hw⟩
        have hlt : G.1.idxOf v < G.1.length := List.idxOf_lt_length_iff.2 hv
        have hlt' : G.1.idxOf v < (G.1.map fun u => decide (u ∈ S)).length := by simpa using hlt
        dsimp only [w] at hw
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt', List.getElem?_map,
          List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt] at hw
        exact of_decide_eq_true hw
      · intro hv
        have hvG : v ∈ G.1 := hSV v hv
        have hlt : G.1.idxOf v < G.1.length := List.idxOf_lt_length_iff.2 hvG
        have hlt' : G.1.idxOf v < (G.1.map fun u => decide (u ∈ S)).length := by simpa using hlt
        refine ⟨hvG, ?_⟩
        dsimp only [w]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt', List.getElem?_map,
          List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]
        exact decide_eq_true hv
    have hlen_eq : (selectVertices G.1 w).length = m := by
      rw [← List.toFinset_card_of_nodup (nodup_selectVertices G.1 w), htoFinset, hcard]
    refine ⟨w, hw_len, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true]
    refine ⟨hlen_eq, fun u hu v hv => ?_⟩
    by_cases huv : u = v
    · exact Or.inl huv
    · have huS : u ∈ S := htoFinset ▸ List.mem_toFinset.2 hu
      have hvS : v ∈ S := htoFinset ▸ List.mem_toFinset.2 hv
      exact Or.inr ((hrel G u v huv).2 (hpair huS hvS huv))
  · rintro ⟨w, -, hw⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at hw
    obtain ⟨hlen, hpair⟩ := hw
    refine ⟨(selectVertices G.1 w).toFinset, fun v hv => ?_, ?_, ?_⟩
    · exact (mem_selectVertices.1 (List.mem_toFinset.1 hv)).1
    · intro u hu v hv huv
      have hu' : u ∈ selectVertices G.1 w := List.mem_toFinset.1 hu
      have hv' : v ∈ selectVertices G.1 w := List.mem_toFinset.1 hv
      rcases hpair u hu' v hv' with rfl | h
      · exact (huv rfl).elim
      · exact (hrel G u v huv).1 h
    · rw [List.toFinset_card_of_nodup (nodup_selectVertices G.1 w), hlen]

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
  have hS : ComputableTidilyInPolyTime
      (fun x : (Graph × ℕ) × List Bool => selectVertices x.1.1.1 x.2)
      (encPair (encPair encGraph encNat) encBits) (encList encNat) := by
    unfold encGraph
    fun_prop
  have hlen : ComputableTidilyInPolyTime
      (fun x : (Graph × ℕ) × List Bool => (selectVertices x.1.1.1 x.2).length)
      (encPair (encPair encGraph encNat) encBits) encNat :=
    unary_to_binary.comp ((length_list encNat).comp hS)
  have hcard : ComputableTidilyInPolyTime
      (fun x : (Graph × ℕ) × List Bool => decide ((selectVertices x.1.1.1 x.2).length = x.1.2))
      (encPair (encPair encGraph encNat) encBits) encBool :=
    hlen.decide_eq' (by unfold encGraph; fun_prop)
  have hpair : ComputableTidilyInPolyTime
      (fun x : (Graph × ℕ) × List Bool =>
        (selectVertices x.1.1.1 x.2).all fun u =>
          (selectVertices x.1.1.1 x.2).all fun v => decide (u = v) || rel x.1.1 u v)
      (encPair (encPair encGraph encNat) encBits) encBool := by
    apply allWithInput hS
    apply allWithInput (hS.comp (fst _ _))
    have hproj : ComputableTidilyInPolyTime
        (fun p : (((Graph × ℕ) × List Bool) × ℕ) × ℕ => ((p.1.1.1.1, p.1.2), p.2))
        (encPair (encPair (encPair (encPair encGraph encNat) encBits) encNat) encNat)
        (encPair (encPair encGraph encNat) encNat) := by fun_prop
    apply bool_or'
    · fun_prop
    · exact hrel.comp hproj
  exact hcard.bool_and' hpair

end Graph

namespace SAT

/-! ### Karp's reduction -/

/-- An occurrence of a literal: its clause, its position in the clause, and the literal. -/
abbrev Occurrence : Type := ℕ × ℕ × Literal ℕ

/-- The occurrences of literals in a formula. -/
def occurrences (φ : CNF ℕ) : List Occurrence :=
  φ.zipIdx.flatMap fun c => c.1.zipIdx.map fun l => (c.2, l.2, l.1)

/-- The vertex of an occurrence. -/
def Occurrence.vertex (o : Occurrence) : ℕ := Nat.pair o.1 o.2.1

/-- Two occurrences conflict when they are in the same clause or are complementary. -/
def Occurrence.Conflict (o o' : Occurrence) : Prop :=
  (o.1 = o'.1 ∧ o.2.1 ≠ o'.2.1) ∨ (o.2.2.1 = o'.2.2.1 ∧ o.2.2.2 ≠ o'.2.2.2)

instance : DecidableRel Occurrence.Conflict := fun _ _ => by
  unfold Occurrence.Conflict; infer_instance

/-- Karp's reduction from `SAT` to `IndependentSet`. -/
def toIndependentSet (φ : CNF ℕ) : Graph × ℕ :=
  (((occurrences φ).map Occurrence.vertex,
    (occurrences φ).flatMap fun o =>
      ((occurrences φ).filter fun o' => decide (o.Conflict o')).map
        fun o' => (o.vertex, o'.vertex)),
    φ.length)

theorem mem_occurrences {φ : CNF ℕ} {o : Occurrence} :
    o ∈ occurrences φ ↔ ∃ (h₁ : o.1 < φ.length) (h₂ : o.2.1 < φ[o.1].length),
      o.2.2 = φ[o.1][o.2.1] := by
  obtain ⟨i, j, l⟩ := o
  simp only [occurrences, List.mem_flatMap, List.mem_map, List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨⟨c, i'⟩, hc, ⟨l', j'⟩, hl, he⟩
    simp only [Prod.mk.injEq] at he hc hl
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨hi, hci⟩ := List.getElem?_eq_some_iff.1 hc
    subst hci
    obtain ⟨hj, hlj⟩ := List.getElem?_eq_some_iff.1 hl
    exact ⟨hi, hj, hlj.symm⟩
  · rintro ⟨hi, hj, hl⟩
    exact ⟨(φ[i], i), by simp [hi], (φ[i][j], j), by simp [hj], by rw [hl]⟩

theorem Occurrence.Conflict.symm {o o' : Occurrence} (h : o.Conflict o') : o'.Conflict o := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨h₁.symm, h₂.symm⟩
  · exact Or.inr ⟨h₁.symm, h₂.symm⟩

theorem Occurrence.Conflict.ne {o o' : Occurrence} (h : o.Conflict o') : o ≠ o' := by
  rintro rfl
  rcases h with ⟨-, h⟩ | ⟨-, h⟩ <;> exact h rfl

/-- An occurrence is determined by its vertex. -/
theorem vertex_injOn {φ : CNF ℕ} {o o' : Occurrence} (ho : o ∈ occurrences φ)
    (ho' : o' ∈ occurrences φ) (h : o.vertex = o'.vertex) : o = o' := by
  obtain ⟨i, j, l⟩ := o
  obtain ⟨i', j', l'⟩ := o'
  simp only [Occurrence.vertex, Nat.pair_eq_pair] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨h₁, h₂, hl⟩ := mem_occurrences.1 ho
  obtain ⟨h₁', h₂', hl'⟩ := mem_occurrences.1 ho'
  simp only at hl hl'
  rw [hl, hl']

/-- In the graph of Karp's reduction, two occurrences are adjacent exactly when they conflict. -/
theorem adj_toIndependentSet_iff {φ : CNF ℕ} {o o' : Occurrence} (ho : o ∈ occurrences φ)
    (ho' : o' ∈ occurrences φ) :
    (toIndependentSet φ).1.toSimpleGraph.Adj o.vertex o'.vertex ↔ o.Conflict o' := by
  have hedge : ∀ {p p'}, p ∈ occurrences φ → p' ∈ occurrences φ →
      ((p.vertex, p'.vertex) ∈ (toIndependentSet φ).1.2 ↔ p.Conflict p') := by
    intro p p' hp hp'
    simp only [toIndependentSet, List.mem_flatMap, List.mem_map, List.mem_filter,
      decide_eq_true_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨q, hq, q', ⟨hq', hc⟩, h₁, h₂⟩
      rwa [← vertex_injOn hq hp h₁, ← vertex_injOn hq' hp' h₂]
    · intro hc
      exact ⟨p, hp, p', ⟨hp', hc⟩, rfl, rfl⟩
  simp only [Graph.toSimpleGraph, SimpleGraph.fromRel_adj, ne_eq, hedge ho ho', hedge ho' ho]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact h.symm
  · intro h
    exact ⟨fun hv => h.ne (vertex_injOn ho ho' hv), Or.inl h⟩

/-- **Correctness of Karp's reduction.** A formula is satisfiable exactly when its graph has an
independent set with as many vertices as the formula has clauses. -/
theorem toIndependentSet_mem_iff (φ : CNF ℕ) : toIndependentSet φ ∈ IndependentSet ↔ φ ∈ SAT := by
  classical
  constructor
  · rintro ⟨S, hSV, hS⟩
    -- Every vertex of `S` is an occurrence.
    have hocc : ∀ v ∈ S, ∃ o ∈ occurrences φ, o.vertex = v := fun v hv => by
      simpa [toIndependentSet] using hSV v hv
    choose! occ hocc_mem hocc_vertex using hocc
    have hadj : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬(occ u).Conflict (occ v) := by
      intro u hu v hv huv hc
      have := (adj_toIndependentSet_iff (hocc_mem u hu) (hocc_mem v hv)).2 hc
      rw [hocc_vertex u hu, hocc_vertex v hv] at this
      exact hS.isIndepSet hu hv huv this
    -- Each clause holds exactly one vertex of `S`.
    have hinj : Set.InjOn (fun v => (occ v).1) S := by
      intro u hu v hv h
      by_contra huv
      refine hadj u hu v hv huv (Or.inl ⟨h, fun hj => huv ?_⟩)
      rw [← hocc_vertex u hu, ← hocc_vertex v hv]
      simp [Occurrence.vertex, h, hj]
    have himage : S.image (fun v => (occ v).1) = Finset.range φ.length := by
      refine Finset.eq_of_subset_of_card_le (fun i hi => ?_) ?_
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hi
        exact Finset.mem_range.2 (mem_occurrences.1 (hocc_mem v hv)).1
      · rw [Finset.card_image_of_injOn hinj, hS.card_eq, Finset.card_range]
        exact le_rfl
    -- The assignment making the chosen positive literals true.
    let σ : ℕ → Bool := fun x => decide (∃ v ∈ S, (occ v).2.2 = (x, true))
    refine ⟨σ, (CNF.eval_eq_true_iff _ _).2 fun c hc => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    obtain ⟨v, hv, hvi⟩ := Finset.mem_image.1 (himage ▸ Finset.mem_range.2 hi : i ∈ _)
    have hov := hocc_mem v hv
    rcases hocc : occ v with ⟨i', j, x, b⟩
    rw [hocc] at hov hvi
    simp only at hvi
    subst hvi
    obtain ⟨hi', hj, hl⟩ := mem_occurrences.1 hov
    have hl' : (x, b) = φ[i'][j] := hl
    rw [Clause.eval_eq_true_iff]
    refine ⟨(x, b), by rw [hl']; exact List.getElem_mem hj, ?_⟩
    cases b
    · simp only [σ, decide_eq_false_iff_not, not_exists, not_and]
      intro v' hv' hv'x
      have hne : v ≠ v' := by
        rintro rfl
        rw [hocc] at hv'x
        simp at hv'x
      refine hadj v hv v' hv' hne ?_
      rw [hocc]
      exact Or.inr ⟨by simp [hv'x], by simp [hv'x]⟩
    · exact decide_eq_true ⟨v, hv, by rw [hocc]⟩
  · rintro ⟨σ, hσ⟩
    have hcl : ∀ i : Fin φ.length, ∃ j : Fin φ[i].length, σ φ[i][j].1 = φ[i][j].2 := by
      intro i
      obtain ⟨l, hl, hσl⟩ := (Clause.eval_eq_true_iff _ _).1
        ((CNF.eval_eq_true_iff _ _).1 hσ φ[i] (List.getElem_mem i.2))
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
      exact ⟨⟨j, hj⟩, hσl⟩
    choose J hJ using hcl
    let o : Fin φ.length → Occurrence := fun i => (i, J i, φ[i][J i])
    have ho : ∀ i, o i ∈ occurrences φ := fun i => mem_occurrences.2 ⟨i.2, (J i).2, rfl⟩
    have hoinj : Function.Injective fun i => (o i).vertex := by
      intro i i' h
      simp only [o, Occurrence.vertex, Nat.pair_eq_pair] at h
      exact Fin.ext h.1
    refine ⟨Finset.univ.image fun i => (o i).vertex, fun v hv => ?_, ⟨?_, ?_⟩⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      simp only [toIndependentSet, List.mem_map]
      exact ⟨o i, ho i, rfl⟩
    · intro u hu w hw huw hadj
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨i', -, rfl⟩ := Finset.mem_image.1 hw
      have hii' : i ≠ i' := fun h => huw (by rw [h])
      rcases (adj_toIndependentSet_iff (ho i) (ho i')).1 hadj with ⟨h, -⟩ | ⟨hx, hb⟩
      · exact hii' (Fin.ext h)
      · have h₁ := hJ i
        have h₂ := hJ i'
        simp only [o] at hx hb
        rw [hx] at h₁
        exact hb (h₁.symm.trans h₂)
    · rw [Finset.card_image_of_injective _ hoinj, Finset.card_univ, Fintype.card_fin]
      rfl

/-! ### Polynomial-time reduction -/

/-- Encoding of a literal occurrence: unary clause and position indices with a binary-numbered
literal. -/
def encOccurrence : Occurrence ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encNat encBool))

/-- Enumerating the literal occurrences of a CNF formula is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_occurrences :
    ComputableTidilyInPolyTime occurrences encCNF (encList encOccurrence) := by
  unfold occurrences encCNF encOccurrence
  fun_prop

/-- Computing the binary vertex label of an occurrence from its unary indices is polynomial-time. -/
@[fun_prop]
theorem Occurrence.computableTidilyInPolyTime_vertex :
    ComputableTidilyInPolyTime Occurrence.vertex encOccurrence encNat := by
  unfold Occurrence.vertex encOccurrence
  exact unary_to_binary.comp (by fun_prop)

/-- Testing whether two occurrences conflict is polynomial-time. -/
@[fun_prop]
theorem Occurrence.computableTidilyInPolyTime_conflict :
    ComputableTidilyInPolyTime (fun p : Occurrence × Occurrence => decide (p.1.Conflict p.2))
      (encPair encOccurrence encOccurrence) encBool := by
  unfold Occurrence.Conflict encOccurrence
  fun_prop

/-- Karp's reduction `toIndependentSet` is computable in polynomial time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_toIndependentSet :
    ComputableTidilyInPolyTime toIndependentSet encCNF (encPair encGraph encNat) := by
  have hlen : ComputableTidilyInPolyTime (fun φ : CNF ℕ => φ.length) encCNF encNat :=
    unary_to_binary.comp (length_list _)
  unfold toIndependentSet encGraph
  fun_prop

end SAT

namespace IndependentSet

/-- The verifier for `IndependentSet`: select distinct declared vertices from the certificate mask,
check that their count equals `m`, and check that no two distinct selected vertices are adjacent. -/
def verifier : (Graph × ℕ) × List Bool → Bool :=
  Graph.verifySubset fun G u v => !G.adjBool u v

/-- `IndependentSet.verifier` verifies `IndependentSet` with certificates as long as the encoded
instance. -/
theorem isVerifier :
    IsVerifier (encPair encGraph encNat) Polynomial.X verifier IndependentSet := by
  have h := Graph.isVerifier_verifySubset (P := fun G u v => ¬G.toSimpleGraph.Adj u v)
    (fun G u v _ => by rw [Bool.not_eq_true', Graph.adjBool_eq_false_iff])
  intro x
  simpa only [IndependentSet, Set.mem_ofPred_eq, SimpleGraph.isNIndepSet_iff,
    SimpleGraph.IsIndepSet, verifier] using h x

/-- The `IndependentSet` verifier is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_verifier :
    ComputableTidilyInPolyTime verifier
      (encPair (encPair encGraph encNat) encBits) encBool :=
  Graph.computableTidilyInPolyTime_verifySubset (by fun_prop)

/-- `IndependentSet` belongs to `NP`. -/
theorem mem_NP : IndependentSet ∈ NP (encPair encGraph encNat) :=
  ⟨Polynomial.X, verifier, computableTidilyInPolyTime_verifier, isVerifier⟩

end IndependentSet

/-- `SAT` reduces to `IndependentSet` in polynomial time via `SAT.toIndependentSet`. -/
theorem polyTimeReducible_SAT_IndependentSet :
    PolyTimeReducible encCNF (encPair encGraph encNat) SAT IndependentSet :=
  ⟨SAT.toIndependentSet, SAT.computableTidilyInPolyTime_toIndependentSet,
    fun φ => (SAT.toIndependentSet_mem_iff φ).symm⟩

/-- `IndependentSet` is `NP`-hard. -/
theorem IndependentSet_npHard : NPHard (encPair encGraph encNat) IndependentSet :=
  CookLevin.SAT_npHard.trans polyTimeReducible_SAT_IndependentSet

/-- **`IndependentSet` is NP-complete.** -/
theorem IndependentSet_npComplete : NPComplete (encPair encGraph encNat) IndependentSet :=
  ⟨IndependentSet.mem_NP, IndependentSet_npHard⟩

end Cslib.Complexity
