/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.IndependentSet
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Data.List.Cycle

/-!
# Hamiltonian paths and cycles

A graph, given by a list of vertices and a list of edges, is read as a directed graph through its
arcs `(u, v) ∈ G.2`, or as an undirected graph through `Cslib.Complexity.Graph.toSimpleGraph`
restricted to the declared vertices (`SimpleGraph.induce`). In both readings the vertices are the
declared ones: repeated vertex entries count once, and edges with an undeclared endpoint are never
used.

* `DirHamPath` is the set of triples `(G, s, t)` such that the directed graph `G` has a
  Hamiltonian path from `s` to `t` [Sipser, Section 7.3][Sipser2013]. Mathlib's `Digraph` has no
  walks, so the path is a list of vertices (`Graph.IsDirHamPath`).
* `DirHamCycle` is the set of directed graphs with a Hamiltonian cycle (`Graph.IsDirHamCycle`):
  a nonempty list of the vertices whose consecutive vertices, read cyclically (`Cycle.Chain`), are
  joined by arcs. A single vertex therefore needs a self-loop, and two vertices need arcs both
  ways.
* `HamPath` and `HamCycle` are the undirected versions, stated with Mathlib's
  `SimpleGraph.Walk.IsHamiltonian` and `SimpleGraph.Walk.IsHamiltonianCycle`. A Hamiltonian cycle
  is a cycle, so it has at least three vertices; unlike `SimpleGraph.IsHamiltonian`, no convention
  makes the one-vertex graph Hamiltonian. `mem_HamPath_iff` and `mem_HamCycle_iff` restate them
  with lists of vertices.

## Main definitions

* `Cslib.Complexity.Graph.IsDirHamPath`, `Cslib.Complexity.DirHamPath`.
* `Cslib.Complexity.Graph.IsDirHamCycle`, `Cslib.Complexity.DirHamCycle`.
* `Cslib.Complexity.HamPath`, `Cslib.Complexity.HamCycle`.

## Main results

* `Cslib.Complexity.mem_HamPath_iff`: undirected Hamiltonian paths as lists of vertices.
* `Cslib.Complexity.mem_HamCycle_iff`: undirected Hamiltonian cycles as lists of vertices.

## References

* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

namespace Graph

/-- `p` is a Hamiltonian path of the directed graph `G` from `s` to `t`: it lists every declared
vertex exactly once, starts at `s`, ends at `t`, and consecutive vertices are joined by arcs. -/
def IsDirHamPath (G : Graph) (s t : ℕ) (p : List ℕ) : Prop :=
  p.Nodup ∧ (∀ v, v ∈ p ↔ v ∈ G.1) ∧ p.head? = some s ∧ p.getLast? = some t ∧
    p.IsChain fun u v => (u, v) ∈ G.2

/-- `p` is a Hamiltonian cycle of the directed graph `G`: a nonempty list of every declared vertex
exactly once whose consecutive vertices, read cyclically, are joined by arcs. -/
def IsDirHamCycle (G : Graph) (p : List ℕ) : Prop :=
  p.Nodup ∧ (∀ v, v ∈ p ↔ v ∈ G.1) ∧ p ≠ [] ∧ (p : Cycle ℕ).Chain fun u v => (u, v) ∈ G.2

end Graph

/-- The directed graphs with a Hamiltonian path from `s` to `t`. -/
def DirHamPath : Set (Graph × ℕ × ℕ) := {x | ∃ p, x.1.IsDirHamPath x.2.1 x.2.2 p}

/-- The directed graphs with a Hamiltonian cycle. -/
def DirHamCycle : Set Graph := {G | ∃ p, G.IsDirHamCycle p}

/-- The graphs with a Hamiltonian path from `s` to `t` through their declared vertices. -/
def HamPath : Set (Graph × ℕ × ℕ) :=
  {x | ∃ (hs : x.2.1 ∈ x.1.1) (ht : x.2.2 ∈ x.1.1)
    (p : (x.1.toSimpleGraph.induce {v | v ∈ x.1.1}).Walk ⟨x.2.1, hs⟩ ⟨x.2.2, ht⟩),
    p.IsHamiltonian}

/-- The graphs with a Hamiltonian cycle through their declared vertices. -/
def HamCycle : Set Graph :=
  {G | ∃ (a : {v | v ∈ G.1}) (p : (G.toSimpleGraph.induce {v | v ∈ G.1}).Walk a a),
    p.IsHamiltonianCycle}

/-! ### Lists of vertices -/

/-- A list is a closed chain exactly when appending its first element gives a chain. -/
theorem _root_.Cycle.chain_coe_iff_isChain_append_take_one {α : Type*} {R : α → α → Prop}
    {p : List α} : (p : Cycle α).Chain R ↔ (p ++ p.take 1).IsChain R := by
  cases p with
  | nil => simp
  | cons a l => rw [Cycle.chain_coe_cons]; simp

/-- Lift a list of declared vertices to the vertex type of the induced graph. -/
private def liftVertices (G : Graph) (p : List ℕ) (h : ∀ v ∈ p, v ∈ G.1) :
    List {v | v ∈ G.1} :=
  p.pmap Subtype.mk h

private theorem map_val_liftVertices (G : Graph) (p : List ℕ) (h : ∀ v ∈ p, v ∈ G.1) :
    (liftVertices G p h).map Subtype.val = p := by
  simp [liftVertices, List.map_pmap]

private theorem isChain_liftVertices {G : Graph} {p : List ℕ} (h : ∀ v ∈ p, v ∈ G.1)
    (hp : p.IsChain G.toSimpleGraph.Adj) :
    (liftVertices G p h).IsChain (G.toSimpleGraph.induce {v | v ∈ G.1}).Adj :=
  List.isChain_pmap_of_isChain (S := (G.toSimpleGraph.induce {v | v ∈ G.1}).Adj)
    (f := fun a ha => (⟨a, ha⟩ : {v | v ∈ G.1})) (fun _ _ _ _ hab => hab) hp h

private theorem nodup_liftVertices {G : Graph} {p : List ℕ} (h : ∀ v ∈ p, v ∈ G.1)
    (hp : p.Nodup) : (liftVertices G p h).Nodup :=
  hp.pmap fun _ _ _ _ hab => congrArg Subtype.val hab

private theorem mem_liftVertices {G : Graph} {p : List ℕ} (h : ∀ v ∈ p, v ∈ G.1)
    (v : {v | v ∈ G.1}) : v ∈ liftVertices G p h ↔ v.1 ∈ p := by
  refine ⟨fun hv => ?_, fun hv => List.mem_pmap.2 ⟨v.1, hv, rfl⟩⟩
  have := List.mem_map_of_mem (f := Subtype.val) hv
  rwa [map_val_liftVertices] at this

/-- Undirected Hamiltonian paths as lists of vertices. -/
theorem mem_HamPath_iff {G : Graph} {s t : ℕ} :
    (G, s, t) ∈ HamPath ↔ ∃ p : List ℕ, p.Nodup ∧ (∀ v, v ∈ p ↔ v ∈ G.1) ∧
      p.head? = some s ∧ p.getLast? = some t ∧ p.IsChain G.toSimpleGraph.Adj := by
  constructor
  · rintro ⟨hs, ht, w, hw⟩
    refine ⟨w.support.map Subtype.val, hw.isPath.support_nodup.map Subtype.val_injective,
      fun v => ⟨fun hv => ?_, fun hv => ?_⟩, ?_, ?_, ?_⟩
    · obtain ⟨u, -, rfl⟩ := List.mem_map.1 hv
      exact u.2
    · exact List.mem_map.2 ⟨⟨v, hv⟩, hw.mem_support _, rfl⟩
    · rw [List.head?_map, w.support.head?_eq_some_head w.support_ne_nil, w.head_support]
      rfl
    · rw [List.getLast?_map, w.support.getLast?_eq_some_getLast w.support_ne_nil,
        w.getLast_support]
      rfl
    · exact List.isChain_map_of_isChain (S := G.toSimpleGraph.Adj) Subtype.val
        (fun _ _ hab => hab) w.isChain_adj_support
  · rintro ⟨p, hnd, hcov, hs, ht, hch⟩
    have hV : ∀ v ∈ p, v ∈ G.1 := fun v hv => (hcov v).1 hv
    have hne : p ≠ [] := by rintro rfl; simp at hs
    have hne' : liftVertices G p hV ≠ [] := by simpa [liftVertices] using hne
    have hhead : (liftVertices G p hV).head hne' = ⟨s, (hcov s).1 (List.mem_of_head? hs)⟩ := by
      have h := congrArg List.head? (map_val_liftVertices G p hV)
      rw [List.head?_map, List.head?_eq_some_head hne', hs] at h
      exact Subtype.ext (Option.some_injective _ h)
    have hlast : (liftVertices G p hV).getLast hne' =
        ⟨t, (hcov t).1 (List.mem_of_getLast? ht)⟩ := by
      have h := congrArg List.getLast? (map_val_liftVertices G p hV)
      rw [List.getLast?_map, List.getLast?_eq_some_getLast hne', ht] at h
      exact Subtype.ext (Option.some_injective _ h)
    refine ⟨(hcov s).1 (List.mem_of_head? hs), (hcov t).1 (List.mem_of_getLast? ht),
      (SimpleGraph.Walk.ofSupport _ hne' (isChain_liftVertices hV hch)).copy hhead hlast, ?_⟩
    intro v
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_ofSupport]
    exact @List.count_eq_one_of_mem _ instBEqOfDecidableEq _ _ _ (nodup_liftVertices hV hnd)
      ((mem_liftVertices hV v).2 ((hcov v).2 v.2))

/-- Undirected Hamiltonian cycles as lists of vertices. -/
theorem mem_HamCycle_iff {G : Graph} :
    G ∈ HamCycle ↔ ∃ p : List ℕ, p.Nodup ∧ (∀ v, v ∈ p ↔ v ∈ G.1) ∧ 3 ≤ p.length ∧
      (p : Cycle ℕ).Chain G.toSimpleGraph.Adj := by
  simp_rw [Cycle.chain_coe_iff_isChain_append_take_one]
  constructor
  · rintro ⟨a, w, hw⟩
    have hnil := hw.isCycle.not_nil
    refine ⟨w.support.dropLast.map Subtype.val,
      hw.isCycle.nodup_dropLast_support.map Subtype.val_injective,
      fun v => ⟨fun hv => ?_, fun hv => ?_⟩, ?_, ?_⟩
    · obtain ⟨u, -, rfl⟩ := List.mem_map.1 hv
      exact u.2
    · refine List.mem_map.2 ⟨⟨v, hv⟩, ?_, rfl⟩
      rw [← SimpleGraph.Walk.support_dropLast hnil]
      exact hw.isHamiltonian_dropLast.mem_support _
    · rw [List.length_map, List.length_dropLast, SimpleGraph.Walk.length_support]
      simpa using hw.isCycle.three_le_length
    · cases w with
      | nil => exact (hnil SimpleGraph.Walk.Nil.nil).elim
      | cons h q =>
        have hq : q.support ≠ [] := q.support_ne_nil
        have hsupp : q.support.dropLast ++ [a] = q.support := by
          conv_rhs => rw [← List.dropLast_append_getLast hq]
          rw [q.getLast_support]
        have heq : (a :: q.support).dropLast.map Subtype.val ++
            ((a :: q.support).dropLast.map Subtype.val).take 1 =
            (a :: q.support).map Subtype.val := by
          rw [List.dropLast_cons_of_ne_nil hq, List.map_cons, List.take_succ_cons, List.take_zero,
            List.cons_append, List.map_cons]
          conv_rhs => rw [← hsupp]
          rw [List.map_append, List.map_singleton]
        rw [SimpleGraph.Walk.support_cons, heq]
        exact List.isChain_map_of_isChain (S := G.toSimpleGraph.Adj) Subtype.val
          (fun _ _ hab => hab) (SimpleGraph.Walk.cons h q).isChain_adj_support
  · rintro ⟨p, hnd, hcov, hlen, hch⟩
    have hV : ∀ v ∈ p, v ∈ G.1 := fun v hv => (hcov v).1 hv
    have hne : p ≠ [] := by rintro rfl; simp at hlen
    set L := liftVertices G p hV with hL
    have hLne : L ≠ [] := by simpa [L, liftVertices] using hne
    set a := L.head hLne with ha
    have hav : a.1 = p.head hne := by
      have h := congrArg List.head? (map_val_liftVertices G p hV)
      rw [List.head?_map, List.head?_eq_some_head hLne, List.head?_eq_some_head hne] at h
      exact Option.some_injective _ h
    have hmap : (L ++ [a]).map Subtype.val = p ++ p.take 1 := by
      rw [List.map_append, map_val_liftVertices, List.map_singleton, hav,
        List.take_one, List.head?_eq_some_head hne]
      rfl
    have hchain : (L ++ [a]).IsChain (G.toSimpleGraph.induce {v | v ∈ G.1}).Adj := by
      have := (List.isChain_map (R := G.toSimpleGraph.Adj) Subtype.val).1 (hmap ▸ hch)
      exact this
    have hne' : L ++ [a] ≠ [] := by simp
    have hhead : (L ++ [a]).head hne' = a := by
      rw [List.head_append_of_ne_nil hLne]
    have hlast : (L ++ [a]).getLast hne' = a := List.getLast_concat
    let w := (SimpleGraph.Walk.ofSupport _ hne' hchain).copy hhead hlast
    have hsupp : w.support = L ++ [a] := by
      simp [w, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_ofSupport]
    have hlenw : w.length = p.length := by
      rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_ofSupport]
      simp [L, liftVertices]
    have hnil : ¬w.Nil := fun h => by
      have := SimpleGraph.Walk.length_eq_zero_iff.2 h
      omega
    have hdrop : w.dropLast.support = L := by
      rw [SimpleGraph.Walk.support_dropLast hnil, hsupp, List.dropLast_concat]
    refine ⟨a, w, SimpleGraph.Walk.isHamiltonianCycle_isCycle_and_isHamiltonian_tail.2
      ⟨SimpleGraph.Walk.isCycle_iff_isPath_dropLast_and_le_length.2 ⟨?_, by omega⟩,
        SimpleGraph.Walk.isHamiltonian_dropLast_iff.1 fun v => ?_⟩⟩
    · rw [SimpleGraph.Walk.isPath_def, hdrop]
      exact nodup_liftVertices hV hnd
    · rw [hdrop]
      exact @List.count_eq_one_of_mem _ instBEqOfDecidableEq _ _ _ (nodup_liftVertices hV hnd)
        ((mem_liftVertices hV v).2 ((hcov v).2 v.2))

end Cslib.Complexity
