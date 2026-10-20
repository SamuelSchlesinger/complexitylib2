/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP.Witness
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
the selected count in binary without unary expansion of `m`. The verifier is an instance of the
subset-witness verifier `Cslib.Complexity.subsetVerifier`, which handles the certificate length.

## Main definitions

* `Cslib.Complexity.Graph.toSimpleGraph`, `Cslib.Complexity.encGraph`,
  `Cslib.Complexity.IndependentSet`.
* `Cslib.Complexity.Graph.adjBool`, `Cslib.Complexity.Graph.selectVertices`,
  `Cslib.Complexity.Graph.verifySubset`.
* `Cslib.Complexity.IndependentSet.verifier`.
* `Cslib.Complexity.SAT.toIndependentSet`.
* `Cslib.Complexity.Graph.indepNum`: the independence number.

## Main results

* `Cslib.Complexity.SAT.toIndependentSet_mem_iff`: `toIndependentSet φ ∈ IndependentSet ↔ φ ∈ SAT`.
* `Cslib.Complexity.SAT.exists_card_add_countUnsat_le`: an independent set of Karp's graph gives an
  assignment satisfying as many clauses.
* `Cslib.Complexity.Graph.le_indepNum_iff`: the independence number is the largest target of
  `IndependentSet`.
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
  · exact (unary_to_binary.comp ((length_list encNat).comp (snd _ _))).decide_eq' (by fun_prop)
  · apply allWithInput (snd _ _)
    apply allWithInput ((snd _ _).comp (fst _ _))
    have hproj : ComputableTidilyInPolyTime
        (fun p : (((Graph × ℕ) × List ℕ) × ℕ) × ℕ => ((p.1.1.1.1, p.1.2), p.2))
        (encPair (encPair (encPair (encPair encGraph encNat) (encList encNat)) encNat) encNat)
        (encPair (encPair encGraph encNat) encNat) := by fun_prop
    exact bool_or' (by fun_prop) (hrel.comp hproj)

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

/-- The variables of the occurrences, in order, are the variables of the formula. -/
theorem map_occurrences (φ : CNF ℕ) : (occurrences φ).map (fun o => o.2.2.1) = φ.vars := by
  have hc : ∀ c : Clause ℕ × ℕ, (c.1.zipIdx.map fun l => (c.2, l.2, l.1).2.2.1) =
      c.1.map Prod.fst := fun c => by
    calc (c.1.zipIdx.map fun l => (c.2, l.2, l.1).2.2.1) =
        (c.1.zipIdx.map Prod.fst).map Prod.fst := by rw [List.map_map]; rfl
      _ = c.1.map Prod.fst := by rw [List.zipIdx_map_fst]
  calc (occurrences φ).map (fun o => o.2.2.1)
      = φ.zipIdx.flatMap fun c => c.1.map Prod.fst := by
        simp only [occurrences, List.map_flatMap, List.map_map, Function.comp_def, hc]
    _ = (φ.zipIdx.map Prod.fst).flatMap fun c => c.map Prod.fst := by rw [List.flatMap_map]
    _ = φ.vars := by
        rw [List.zipIdx_map_fst, CNF.vars, List.map_flatten, List.flatMap_def]

/-- A formula has one occurrence for each occurrence of a variable. -/
theorem length_occurrences (φ : CNF ℕ) : (occurrences φ).length = φ.vars.length := by
  rw [← map_occurrences, List.length_map]

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

/-- **An independent set of Karp's graph gives an assignment satisfying as many clauses**: the
assignment making the chosen positive literals true satisfies the clause of every chosen
occurrence, and distinct chosen occurrences lie in distinct clauses. -/
theorem exists_card_add_countUnsat_le {φ : CNF ℕ} {S : Finset ℕ}
    (hSV : ∀ v ∈ S, v ∈ (toIndependentSet φ).1.1)
    (hS : (toIndependentSet φ).1.toSimpleGraph.IsIndepSet (S : Set ℕ)) :
    ∃ σ : ℕ → Bool, S.card + φ.countUnsat σ ≤ φ.length := by
  classical
  have hocc : ∀ v ∈ S, ∃ o ∈ occurrences φ, o.vertex = v := fun v hv => by
    simpa [toIndependentSet] using hSV v hv
  choose! occ hocc_mem hocc_vertex using hocc
  have hadj : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬(occ u).Conflict (occ v) := by
    intro u hu v hv huv hc
    have := (adj_toIndependentSet_iff (hocc_mem u hu) (hocc_mem v hv)).2 hc
    rw [hocc_vertex u hu, hocc_vertex v hv] at this
    exact hS hu hv huv this
  -- Distinct chosen occurrences lie in distinct clauses.
  have hinj : Set.InjOn (fun v => (occ v).1) S := by
    intro u hu v hv h
    by_contra huv
    refine hadj u hu v hv huv (Or.inl ⟨h, fun hj => huv ?_⟩)
    rw [← hocc_vertex u hu, ← hocc_vertex v hv]
    simp [Occurrence.vertex, h, hj]
  -- The assignment making the chosen positive literals true.
  let σ : ℕ → Bool := fun x => decide (∃ v ∈ S, (occ v).2.2 = (x, true))
  -- It satisfies the clause of every chosen occurrence.
  have hsat : ∀ v ∈ S, ((φ.zipIdx.filter fun c => c.1.eval σ).map Prod.snd).contains
      (occ v).1 = true := by
    intro v hv
    have hov := hocc_mem v hv
    rcases hocc : occ v with ⟨i, j, x, b⟩
    rw [hocc] at hov
    obtain ⟨hi, hj, hl⟩ := mem_occurrences.1 hov
    have hl' : (x, b) = φ[i][j] := hl
    have heval : φ[i].eval σ = true := by
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
      · simp only [σ, decide_eq_true_eq]
        exact ⟨v, hv, by rw [hocc]⟩
    simp only [List.contains_iff_mem, List.mem_map, List.mem_filter]
    exact ⟨(φ[i], i), ⟨List.mem_zipIdx_iff_getElem?.2 (by simp [hi]), heval⟩, rfl⟩
  refine ⟨σ, ?_⟩
  have hcard : S.card ≤ φ.countP fun c => c.eval σ := by
    calc S.card = (S.image fun v => (occ v).1).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ ((φ.zipIdx.filter fun c => c.1.eval σ).map Prod.snd).toFinset.card := by
          refine Finset.card_le_card fun i hi => ?_
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hi
          exact List.mem_toFinset.2 (List.contains_iff_mem.1 (hsat v hv))
      _ ≤ ((φ.zipIdx.filter fun c => c.1.eval σ).map Prod.snd).length :=
          List.toFinset_card_le _
      _ = φ.countP fun c => c.eval σ := by
          rw [List.length_map, ← List.countP_eq_length_filter]
          conv_rhs => rw [← List.zipIdx_map_fst 0 φ]
          rw [List.countP_map]
          rfl
  have hsplit := List.length_eq_countP_add_countP (fun c : Clause ℕ => c.eval σ) (l := φ)
  have hunsat : φ.countUnsat σ = φ.countP fun c => ¬(c.eval σ = true) := by
    rw [CNF.countUnsat]
    exact List.countP_congr fun c _ => by simp
  omega

/-- **Correctness of Karp's reduction.** A formula is satisfiable exactly when its graph has an
independent set with as many vertices as the formula has clauses. -/
theorem toIndependentSet_mem_iff (φ : CNF ℕ) : toIndependentSet φ ∈ IndependentSet ↔ φ ∈ SAT := by
  constructor
  · rintro ⟨S, hSV, hS⟩
    obtain ⟨σ, hσ⟩ := exists_card_add_countUnsat_le hSV hS.isIndepSet
    have hcard : S.card = φ.length := hS.card_eq
    exact ⟨σ, CNF.countUnsat_eq_zero_iff.1 (by omega)⟩
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

/-! ### The independence number -/

namespace Graph

/-- The **independence number** of a graph: the largest number of declared vertices that are
pairwise non-adjacent. -/
noncomputable def indepNum (G : Graph) : ℕ := sSup {k | (G, k) ∈ IndependentSet}

variable {G : Graph} {k k' : ℕ}

/-- Fewer vertices of an independent set are independent. -/
theorem mem_IndependentSet_of_le (h : (G, k) ∈ IndependentSet) (hk : k' ≤ k) :
    (G, k') ∈ IndependentSet := by
  obtain ⟨S, hSV, hS⟩ := h
  have hc : S.card = k := hS.card_eq
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (hc ▸ hk)
  exact ⟨T, fun v hv => hSV v (hTS hv), ⟨hS.isIndepSet.mono (Finset.coe_subset.2 hTS), hT⟩⟩

/-- An independent set has at most as many vertices as the distinct declared vertices. -/
theorem le_card_of_mem_IndependentSet (h : (G, k) ∈ IndependentSet) :
    k ≤ G.1.toFinset.card := by
  obtain ⟨S, hSV, hS⟩ := h
  have hc : S.card = k := hS.card_eq
  rw [← hc]
  exact Finset.card_le_card fun v hv => List.mem_toFinset.2 (hSV v hv)

/-- **The independence number is the largest target of `IndependentSet`.** -/
theorem le_indepNum_iff : k ≤ G.indepNum ↔ (G, k) ∈ IndependentSet := by
  have hbdd : BddAbove {k | (G, k) ∈ IndependentSet} :=
    ⟨_, fun _ => le_card_of_mem_IndependentSet⟩
  have h0 : (G, 0) ∈ IndependentSet := ⟨∅, by simp, ⟨by simp, rfl⟩⟩
  exact ⟨fun hk => mem_IndependentSet_of_le (Nat.sSup_mem ⟨0, h0⟩ hbdd) hk,
    fun hk => le_csSup hbdd hk⟩

/-- The independence number is the size of an independent set. -/
theorem indepNum_mem_IndependentSet (G : Graph) : (G, G.indepNum) ∈ IndependentSet :=
  le_indepNum_iff.1 le_rfl

/-- The independence number is at most the number of distinct declared vertices. -/
theorem indepNum_le_card (G : Graph) : G.indepNum ≤ G.1.toFinset.card :=
  le_card_of_mem_IndependentSet (indepNum_mem_IndependentSet G)

end Graph

end Cslib.Complexity
