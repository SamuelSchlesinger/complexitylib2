/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT
public import Mathlib.Combinatorics.SimpleGraph.Clique

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

## Main definitions

* `Cslib.Complexity.Graph.toSimpleGraph`, `Cslib.Complexity.IndependentSet`.
* `Cslib.Complexity.SAT.toIndependentSet`.

## Main results

* `Cslib.Complexity.SAT.toIndependentSet_mem_iff`: `toIndependentSet φ ∈ IndependentSet ↔ φ ∈ SAT`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL

/-- A graph on natural numbers, given by its vertices and its edges. -/
abbrev Graph : Type := List ℕ × List (ℕ × ℕ)

/-- The simple graph of an edge list: two distinct vertices are adjacent when an edge joins them,
in either direction. -/
def Graph.toSimpleGraph (G : Graph) : SimpleGraph ℕ := SimpleGraph.fromRel fun u v => (u, v) ∈ G.2

/-- The graphs with an independent set of `m` of their vertices. -/
def IndependentSet : Set (Graph × ℕ) :=
  {x | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.1.1) ∧ x.1.toSimpleGraph.IsNIndepSet x.2 S}

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

end SAT

end Cslib.Complexity
