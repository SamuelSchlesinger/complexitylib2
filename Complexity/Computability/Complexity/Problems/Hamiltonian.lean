/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Data.List.Cycle
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Data.List.GetD

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

All four problems are in `NP`. A certificate names an ordering of the distinct declared vertices:
for a vertex list of length `m`, it is read as one block of `m` bits for each distinct declared
vertex, and each block names the entry of the vertex list whose position is its number of set bits
(`Graph.decodeVertexList`). The verifiers check that the decoded list contains every declared
vertex exactly once and nothing else (`Graph.verifyOrdering`), and then the endpoint, length and
edge conditions. Every ordering has a certificate of length `n ^ 2` for instances of encoded
length `n`. Path instances `(G, s, t)` are encoded by `encPair encGraph (encPair encNat encNat)`,
cycle instances by `encGraph`.

## Main definitions

* `Cslib.Complexity.Graph.IsDirHamPath`, `Cslib.Complexity.DirHamPath`.
* `Cslib.Complexity.Graph.IsDirHamCycle`, `Cslib.Complexity.DirHamCycle`.
* `Cslib.Complexity.HamPath`, `Cslib.Complexity.HamCycle`.
* `Cslib.Complexity.Graph.arcBool`, `Cslib.Complexity.Graph.chainBool`,
  `Cslib.Complexity.Graph.cycleChainBool`, `Cslib.Complexity.Graph.enumeratesBool`: executable
  tests on lists of vertices.
* `Cslib.Complexity.Graph.decodeVertexList`, `Cslib.Complexity.Graph.verifyOrdering`: verifying
  orderings of the declared vertices.
* `Cslib.Complexity.DirHamPath.verifier`, `Cslib.Complexity.DirHamCycle.verifier`,
  `Cslib.Complexity.HamPath.verifier`, `Cslib.Complexity.HamCycle.verifier`.

## Main results

* `Cslib.Complexity.mem_HamPath_iff`: undirected Hamiltonian paths as lists of vertices.
* `Cslib.Complexity.mem_HamCycle_iff`: undirected Hamiltonian cycles as lists of vertices.
* `Cslib.Complexity.Graph.mem_DirHamCycle_cons_iff`: closing a Hamiltonian path with an arc back
  to its start gives a Hamiltonian cycle, when no other arc enters the start.
* `Cslib.Complexity.Graph.exists_decodeVertexList_eq`,
  `Cslib.Complexity.Graph.isVerifier_verifyOrdering`: every ordering of the declared vertices has
  a certificate of quadratic length, so `verifyOrdering` verifies existence of an ordering with a
  decidable property.
* `Cslib.Complexity.DirHamPath.isVerifier`, `Cslib.Complexity.DirHamPath.mem_NP`:
  `DirHamPath ∈ NP (encPair encGraph (encPair encNat encNat))`.
* `Cslib.Complexity.DirHamCycle.isVerifier`, `Cslib.Complexity.DirHamCycle.mem_NP`:
  `DirHamCycle ∈ NP encGraph`.
* `Cslib.Complexity.HamPath.isVerifier`, `Cslib.Complexity.HamPath.mem_NP`:
  `HamPath ∈ NP (encPair encGraph (encPair encNat encNat))`.
* `Cslib.Complexity.HamCycle.isVerifier`, `Cslib.Complexity.HamCycle.mem_NP`:
  `HamCycle ∈ NP encGraph`.

## References

* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979]
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

/-! ### Closing a path into a cycle -/

namespace Graph

/-- A cycle through a vertex can be rotated to start at it. -/
private theorem exists_rotated_cons {q : List ℕ} {s : ℕ} (hs : s ∈ q) :
    ∃ rest : List ℕ, (q : Cycle ℕ) = (s :: rest : List ℕ) ∧ (s :: rest).Nodup = q.Nodup ∧
      ∀ v, v ∈ s :: rest ↔ v ∈ q := by
  have hlt : q.idxOf s < q.length := List.idxOf_lt_length_iff.2 hs
  have hrot : q.rotate (q.idxOf s) = s :: (q.drop (q.idxOf s + 1) ++ q.take (q.idxOf s)) := by
    rw [List.rotate_eq_drop_append_take hlt.le, List.drop_eq_getElem_cons hlt,
      List.getElem_idxOf hlt, List.cons_append]
  refine ⟨q.drop (q.idxOf s + 1) ++ q.take (q.idxOf s), ?_, ?_, fun v => ?_⟩
  · rw [← hrot]
    exact Cycle.coe_eq_coe.2 ⟨_, rfl⟩
  · rw [← hrot]
    exact propext List.nodup_rotate
  · rw [← hrot]
    exact List.mem_rotate

/-- Closing a Hamiltonian path with an arc back to its start. If no arc of `G` enters the declared
vertex `s`, then adding the arc `(t, s)` creates a Hamiltonian cycle exactly when `G` has a
Hamiltonian path from `s` to `t`. -/
theorem mem_DirHamCycle_cons_iff {G : Graph} {s t : ℕ} (hs : s ∈ G.1)
    (hin : ∀ u, (u, s) ∉ G.2) : (G.1, (t, s) :: G.2) ∈ DirHamCycle ↔ (G, s, t) ∈ DirHamPath := by
  constructor
  · rintro ⟨q, hnd, hcov, -, hch⟩
    obtain ⟨rest, hq, hnd', hmem'⟩ := exists_rotated_cons ((hcov s).2 hs)
    rw [hq, Cycle.chain_coe_cons] at hch
    have hnd₀ : (s :: rest).Nodup := hnd' ▸ hnd
    have hchain := (List.isChain_append.1 (show (s :: rest ++ [s]).IsChain _ from hch))
    refine ⟨s :: rest, hnd₀, fun v => (hmem' v).trans (hcov v), rfl, ?_, ?_⟩
    · -- The closing arc enters `s`, so it is the added arc.
      have hlast := hchain.2.2 _ (List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)) s rfl
      rcases List.mem_cons.1 hlast with h | h
      · rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)]
        simp only [Prod.mk.injEq] at h
        rw [h.1]
      · exact (hin _ h).elim
    · -- No other arc enters `s`, so the path uses only arcs of `G`.
      refine hchain.1.imp_of_mem_tail_imp fun a b _ hb hab => ?_
      rcases List.mem_cons.1 hab with h | h
      · simp only [Prod.mk.injEq] at h
        rw [h.2, List.tail_cons] at hb
        exact ((List.nodup_cons.1 hnd₀).1 hb).elim
      · exact h
  · rintro ⟨p, hnd, hcov, hhead, hlast, hch⟩
    obtain ⟨rest, rfl⟩ : ∃ rest, p = s :: rest := by
      cases p with
      | nil => simp at hhead
      | cons a rest =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        exact ⟨rest, by rw [hhead]⟩
    refine ⟨s :: rest, hnd, hcov, List.cons_ne_nil _ _, ?_⟩
    rw [Cycle.chain_coe_cons, ← List.cons_append]
    refine List.isChain_append.2 ⟨hch.imp fun a b h => List.mem_cons_of_mem _ h,
      List.IsChain.singleton _, fun x hx y hy => ?_⟩
    rw [hlast, Option.mem_def, Option.some.injEq] at hx
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    rw [← hx, ← hy]
    exact List.mem_cons_self

end Graph

/-! ### Verifying lists of vertices -/

open Turing.MultiTapeTM ComputableTidilyInPolyTime

namespace Graph

/-- Executable arc test of a directed graph: `(u, v)` is an edge of `G`. -/
def arcBool (G : Graph) (u v : ℕ) : Bool := G.2.any fun e => decide (e = (u, v))

/-- `arcBool` decides whether `(u, v)` is an edge of the list. -/
@[simp]
theorem arcBool_eq_true_iff (G : Graph) (u v : ℕ) : G.arcBool u v = true ↔ (u, v) ∈ G.2 := by
  simp [arcBool]

/-- Testing for an arc in an encoded graph is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_arcBool :
    ComputableTidilyInPolyTime (fun p : (Graph × ℕ) × ℕ => p.1.1.arcBool p.1.2 p.2)
      (encPair (encPair encGraph encNat) encNat) encBool := by
  unfold arcBool encGraph
  fun_prop

/-- Executable test that `r` holds between all consecutive entries of `p`. -/
def chainBool (r : ℕ → ℕ → Bool) (p : List ℕ) : Bool :=
  (List.range (p.length - 1)).all fun i => r (p.getD i 0) (p.getD (i + 1) 0)

/-- `chainBool r` decides `List.IsChain R` when `r` decides `R`. -/
theorem chainBool_eq_true_iff {r : ℕ → ℕ → Bool} {R : ℕ → ℕ → Prop}
    (hr : ∀ u v, r u v = true ↔ R u v) {p : List ℕ} : chainBool r p = true ↔ p.IsChain R := by
  rw [List.isChain_iff_getElem]
  simp only [chainBool, List.all_eq_true, List.mem_range, hr]
  constructor
  · intro h i hi
    have := h i (by omega)
    rwa [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi] at this
  · intro h i hi
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    exact h i (by omega)

/-- Executable test that `r` holds between all consecutive entries of `p` read cyclically: from
each entry to the next one, and from the last entry to the first. -/
def cycleChainBool (r : ℕ → ℕ → Bool) (p : List ℕ) : Bool :=
  (List.range p.length).all fun i =>
    r (p.getD i 0) (p.getD (if i + 1 = p.length then 0 else i + 1) 0)

/-- `cycleChainBool r` decides `Cycle.Chain R` when `r` decides `R`: the empty list passes, and a
one-entry list `[a]` passes exactly when `R a a`. -/
theorem cycleChainBool_eq_true_iff {r : ℕ → ℕ → Bool} {R : ℕ → ℕ → Prop}
    (hr : ∀ u v, r u v = true ↔ R u v) {p : List ℕ} :
    cycleChainBool r p = true ↔ (p : Cycle ℕ).Chain R := by
  rw [Cycle.chain_coe_iff_isChain_append_take_one, List.isChain_iff_getElem]
  simp only [cycleChainBool, List.all_eq_true, List.mem_range, hr]
  cases p with
  | nil => simp
  | cons a l =>
    simp only [List.take_succ_cons, List.take_zero]
    have hlen : (a :: l ++ [a]).length = (a :: l).length + 1 := List.length_append
    have key : ∀ i (hi : i < (a :: l).length),
        (a :: l ++ [a])[i]'(by omega) = (a :: l).getD i 0 ∧
        (a :: l ++ [a])[i + 1]'(by omega) =
          (a :: l).getD (if i + 1 = (a :: l).length then 0 else i + 1) 0 := by
      intro i hi
      refine ⟨by rw [List.getElem_append_left hi, List.getD_eq_getElem _ _ hi], ?_⟩
      split_ifs with h
      · rw [List.getElem_append_right (by omega)]
        simp [h]
      · rw [List.getElem_append_left (by omega), List.getD_eq_getElem _ _ (by omega)]
    constructor
    · intro h i hi
      have hi' : i < (a :: l).length := by omega
      rw [(key i hi').1, (key i hi').2]
      exact h i hi'
    · intro h i hi
      rw [← (key i hi).1, ← (key i hi).2]
      exact h i (by omega)

/-- Executable test that `p` lists every vertex of `V` exactly once and nothing else. -/
def enumeratesBool (V p : List ℕ) : Bool :=
  (V.all fun v => p.any fun u => decide (u = v)) &&
    (p.all fun u => V.any fun v => decide (v = u)) &&
    p.zipIdx.all fun e => decide (p.idxOf e.1 = e.2)

/-- `enumeratesBool V p` holds exactly when `p` lists the members of `V` without repetition. -/
theorem enumeratesBool_eq_true_iff {V p : List ℕ} :
    enumeratesBool V p = true ↔ p.Nodup ∧ ∀ v, v ∈ p ↔ v ∈ V := by
  have hnodup : (∀ e ∈ p.zipIdx, p.idxOf e.1 = e.2) ↔ p.Nodup := by
    constructor
    · intro h
      rw [List.nodup_iff_injective_get]
      rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simp only [List.get_eq_getElem] at hij
      have hi' : p.idxOf p[i] = i := h (p[i], i) (List.mem_zipIdx_iff_getElem?.2 (by simp))
      have hj' : p.idxOf p[j] = j := h (p[j], j) (List.mem_zipIdx_iff_getElem?.2 (by simp))
      rw [hij] at hi'
      exact Fin.ext (hi'.symm.trans hj')
    · intro hnd e he
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 he)
      rw [← heq, hnd.idxOf_getElem]
  simp only [enumeratesBool, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq, hnodup]
  constructor
  · rintro ⟨⟨hV, hp⟩, hnd⟩
    refine ⟨hnd, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · obtain ⟨u, hu, rfl⟩ := hp v hv
      exact hu
    · obtain ⟨u, hu, rfl⟩ := hV v hv
      exact hu
  · rintro ⟨hnd, hmem⟩
    exact ⟨⟨fun v hv => ⟨v, (hmem v).2 hv, rfl⟩, fun u hu => ⟨u, (hmem u).1 hu, rfl⟩⟩, hnd⟩

/-- The list of vertices described by a certificate `w`, for a vertex list `V` of length `m`: `w`
is read as blocks of `m` bits, one for each distinct vertex of `V`, and the block numbered `a`
names the entry of `V` whose position is its number of set bits, or `0` if there is none. -/
def decodeVertexList (V : List ℕ) (w : List Bool) : List ℕ :=
  (List.range V.dedup.length).map fun a =>
    V.getD ((List.range V.length).countP fun c => w.getD (V.length * a + c) false) 0

/-- Every list of the distinct vertices of `V`, each listed once, is described by a certificate
of length `n ^ 2`, for every `n` at least the length of `V`. -/
theorem exists_decodeVertexList_eq {V p : List ℕ} (hp : p.Nodup) (hpV : ∀ v, v ∈ p ↔ v ∈ V)
    {n : ℕ} (hn : V.length ≤ n) : ∃ w : List Bool, w.length = n ^ 2 ∧ decodeVertexList V w = p := by
  have hlen : p.length = V.dedup.length :=
    ((List.perm_ext_iff_of_nodup hp (List.nodup_dedup V)).2 fun v => by
      rw [List.mem_dedup]
      exact hpV v).length_eq
  have hle : V.dedup.length ≤ V.length := (List.dedup_sublist V).length_le
  refine ⟨unaryBlocks V.length (n ^ 2) fun a => V.idxOf (p.getD a 0), length_unaryBlocks ..,
    List.ext_getElem (by simp [decodeVertexList, hlen]) fun a ha ha' => ?_⟩
  have hidx : V.idxOf p[a] < V.length := List.idxOf_lt_length_iff.2 ((hpV _).1 (List.getElem_mem _))
  have hcount := countP_unaryBlocks (N := n ^ 2) (f := fun a => V.idxOf (p.getD a 0)) (a := a)
    (by rw [List.getD_eq_getElem _ _ ha']; exact hidx.le)
    (calc V.length * (a + 1) ≤ n * n := Nat.mul_le_mul hn (by omega)
      _ = n ^ 2 := (sq n).symm)
  simp only [decodeVertexList, List.getElem_map, List.getElem_range]
  rw [hcount, List.getD_eq_getElem _ _ ha', List.getD_eq_getElem _ _ hidx,
    List.getElem_idxOf hidx]

/-- Verify a vertex ordering problem: decode a list of vertices from the certificate
(`decodeVertexList`), check that it lists every vertex of `V x` exactly once, and test it with
`check`. -/
def verifyOrdering {α : Type} (V : α → List ℕ) (check : α → List ℕ → Bool)
    (x : α × List Bool) : Bool :=
  let p := decodeVertexList (V x.1) x.2
  enumeratesBool (V x.1) p && check x.1 p

/-- `verifyOrdering` verifies the existence of an ordering of the vertices satisfying `P`, with
certificates of length `n ^ 2` for instances of encoded length `n`, as long as `check` decides
`P` and the vertex list is not longer than the encoded instance. -/
theorem isVerifier_verifyOrdering {α : Type} {enc : α ↪ List Bool} {V : α → List ℕ}
    {check : α → List ℕ → Bool} {P : α → List ℕ → Prop}
    (hV : ∀ a, (V a).length ≤ (enc a).length) (hcheck : ∀ a p, check a p = true ↔ P a p) :
    IsVerifier enc (Polynomial.X ^ 2) (verifyOrdering V check)
      {a | ∃ p, p.Nodup ∧ (∀ v, v ∈ p ↔ v ∈ V a) ∧ P a p} := by
  intro a
  simp only [Set.mem_ofPred_eq, Polynomial.eval_pow, Polynomial.eval_X, verifyOrdering,
    Bool.and_eq_true, enumeratesBool_eq_true_iff, hcheck]
  constructor
  · rintro ⟨p, hnd, hmem, hP⟩
    obtain ⟨w, hw, hdec⟩ := exists_decodeVertexList_eq hnd hmem (hV a)
    exact ⟨w, hw, by rw [hdec]; exact ⟨⟨hnd, hmem⟩, hP⟩⟩
  · rintro ⟨w, -, ⟨hnd, hmem⟩, hP⟩
    exact ⟨_, hnd, hmem, hP⟩

/-! ### Polynomial-time verification -/

/-- Testing whether `r` holds between consecutive entries of a computed list is polynomial-time,
for an input-dependent polynomial-time test `r`. -/
@[fun_prop]
theorem computableTidilyInPolyTime_chainBool {γ : Type} {encIn : γ ↪ List Bool}
    {r : γ → ℕ → ℕ → Bool} {p : γ → List ℕ}
    (hr : ComputableTidilyInPolyTime (fun q : (γ × ℕ) × ℕ => r q.1.1 q.1.2 q.2)
      (encPair (encPair encIn encNat) encNat) encBool)
    (hp : ComputableTidilyInPolyTime p encIn (encList encNat)) :
    ComputableTidilyInPolyTime (fun x => chainBool (r x) (p x)) encIn encBool := by
  have hget : ∀ {i : γ × ℕ → ℕ}, ComputableTidilyInPolyTime i (encPair encIn encUnary) encUnary →
      ComputableTidilyInPolyTime (fun q => (p q.1).getD (i q) 0) (encPair encIn encUnary) encNat :=
    fun hi => (listGetD 0).comp ((hp.comp (fst _ _)).prod hi)
  unfold chainBool
  exact allWithInput (by fun_prop) (hr.comp (((fst _ _).prod (hget (snd _ _))).prod
    (hget (unary_add.comp ((snd _ _).prod (const 1))))))

/-- Testing whether `r` holds between cyclically consecutive entries of a computed list is
polynomial-time, for an input-dependent polynomial-time test `r`. -/
@[fun_prop]
theorem computableTidilyInPolyTime_cycleChainBool {γ : Type} {encIn : γ ↪ List Bool}
    {r : γ → ℕ → ℕ → Bool} {p : γ → List ℕ}
    (hr : ComputableTidilyInPolyTime (fun q : (γ × ℕ) × ℕ => r q.1.1 q.1.2 q.2)
      (encPair (encPair encIn encNat) encNat) encBool)
    (hp : ComputableTidilyInPolyTime p encIn (encList encNat)) :
    ComputableTidilyInPolyTime (fun x => cycleChainBool (r x) (p x)) encIn encBool := by
  have hget : ∀ {i : γ × ℕ → ℕ}, ComputableTidilyInPolyTime i (encPair encIn encUnary) encUnary →
      ComputableTidilyInPolyTime (fun q => (p q.1).getD (i q) 0) (encPair encIn encUnary) encNat :=
    fun hi => (listGetD 0).comp ((hp.comp (fst _ _)).prod hi)
  have hsucc : ComputableTidilyInPolyTime (fun q : γ × ℕ => q.2 + 1) (encPair encIn encUnary)
      encUnary := unary_add.comp ((snd _ _).prod (const 1))
  have hnext : ComputableTidilyInPolyTime
      (fun q : γ × ℕ => if q.2 + 1 = (p q.1).length then 0 else q.2 + 1)
      (encPair encIn encUnary) encUnary :=
    ite_decide (hsucc.decide_eq' ((length_list encNat).comp (hp.comp (fst _ _)))) (const 0) hsucc
  unfold cycleChainBool
  exact allWithInput (by fun_prop) (hr.comp (((fst _ _).prod (hget (snd _ _))).prod (hget hnext)))

/-- Testing whether a list lists every vertex of another exactly once is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_enumeratesBool :
    ComputableTidilyInPolyTime (fun x : List ℕ × List ℕ => enumeratesBool x.1 x.2)
      (encPair (encList encNat) (encList encNat)) encBool := by
  unfold enumeratesBool
  fun_prop

/-- Decoding a list of vertices from a certificate is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_decodeVertexList :
    ComputableTidilyInPolyTime (fun x : List ℕ × List Bool => decodeVertexList x.1 x.2)
      (encPair (encList encNat) encBits) (encList encNat) := by
  have hn : ComputableTidilyInPolyTime (fun x : List ℕ × List Bool => x.1.dedup.length)
      (encPair (encList encNat) encBits) encUnary := by
    simp only [← List.card_toFinset, ← length_selectDistinct_replicate]
    have := bitsReplicate true
    fun_prop
  have hblock : ComputableTidilyInPolyTime
      (fun q : (List ℕ × List Bool) × ℕ =>
        (List.range q.1.1.length).countP fun c => q.1.2.getD (q.1.1.length * q.2 + c) false)
      (encPair (encPair (encList encNat) encBits) encUnary) encUnary := by
    fun_prop
  unfold decodeVertexList
  fun_prop

/-- `verifyOrdering` is polynomial-time whenever the vertex list and the test `check` are. -/
@[fun_prop]
theorem computableTidilyInPolyTime_verifyOrdering {α : Type} {enc : α ↪ List Bool}
    {V : α → List ℕ} {check : α → List ℕ → Bool}
    (hV : ComputableTidilyInPolyTime V enc (encList encNat))
    (hcheck : ComputableTidilyInPolyTime (fun q : α × List ℕ => check q.1 q.2)
      (encPair enc (encList encNat)) encBool) :
    ComputableTidilyInPolyTime (verifyOrdering V check) (encPair enc encBits) encBool := by
  have hV' : ComputableTidilyInPolyTime (fun x : α × List Bool => V x.1) (encPair enc encBits)
      (encList encNat) := hV.comp (fst _ _)
  have hp : ComputableTidilyInPolyTime (fun x : α × List Bool => decodeVertexList (V x.1) x.2)
      (encPair enc encBits) (encList encNat) :=
    computableTidilyInPolyTime_decodeVertexList.comp (hV'.prod (snd _ _))
  exact (computableTidilyInPolyTime_enumeratesBool.comp (hV'.prod hp)).bool_and'
    (hcheck.comp ((fst _ _).prod hp))

end Graph

/-! ### Membership in `NP` -/

private theorem length_vertices_le_encPath (x : Graph × ℕ × ℕ) :
    x.1.1.length ≤ (encPair encGraph (encPair encNat encNat) x).length := by
  refine x.1.length_vertices_le_encGraph.trans ?_
  simp only [length_encPair]
  omega

/-- The endpoint and edge checks of the path verifiers are polynomial-time for a polynomial-time
edge test `r`. -/
private theorem computableTidilyInPolyTime_pathCheck {r : Graph → ℕ → ℕ → Bool}
    (hr : ComputableTidilyInPolyTime (fun q : (Graph × ℕ) × ℕ => r q.1.1 q.1.2 q.2)
      (encPair (encPair encGraph encNat) encNat) encBool) :
    ComputableTidilyInPolyTime (fun q : (Graph × ℕ × ℕ) × List ℕ =>
        decide (q.2.head? = some q.1.2.1) && decide (q.2.getLast? = some q.1.2.2) &&
          Graph.chainBool (r q.1.1) q.2)
      (encPair (encPair encGraph (encPair encNat encNat)) (encList encNat)) encBool := by
  have hp : ComputableTidilyInPolyTime (fun q : (Graph × ℕ × ℕ) × List ℕ => q.2)
      (encPair (encPair encGraph (encPair encNat encNat)) (encList encNat)) (encList encNat) :=
    snd _ _
  have hs : ComputableTidilyInPolyTime (fun q : (Graph × ℕ × ℕ) × List ℕ => some q.1.2.1)
      (encPair (encPair encGraph (encPair encNat encNat)) (encList encNat)) (encOption encNat) :=
    (optionSome encNat).comp (by fun_prop)
  have ht : ComputableTidilyInPolyTime (fun q : (Graph × ℕ × ℕ) × List ℕ => some q.1.2.2)
      (encPair (encPair encGraph (encPair encNat encNat)) (encList encNat)) (encOption encNat) :=
    (optionSome encNat).comp (by fun_prop)
  have hproj : ComputableTidilyInPolyTime
      (fun q : (((Graph × ℕ × ℕ) × List ℕ) × ℕ) × ℕ => ((q.1.1.1.1, q.1.2), q.2))
      (encPair (encPair (encPair (encPair encGraph (encPair encNat encNat)) (encList encNat))
        encNat) encNat)
      (encPair (encPair encGraph encNat) encNat) := by
    fun_prop
  simp only [← List.head?_reverse]
  exact bool_and' (bool_and' (((head? encNat).comp hp).decide_eq' hs)
      (((head? encNat).comp ((listReverse encNat).comp hp)).decide_eq' ht))
    (Graph.computableTidilyInPolyTime_chainBool (hr.comp hproj) hp)

/-- The cyclic edge check of the cycle verifiers is polynomial-time for a polynomial-time edge
test `r`. -/
private theorem computableTidilyInPolyTime_cycleCheck {r : Graph → ℕ → ℕ → Bool}
    (hr : ComputableTidilyInPolyTime (fun q : (Graph × ℕ) × ℕ => r q.1.1 q.1.2 q.2)
      (encPair (encPair encGraph encNat) encNat) encBool) :
    ComputableTidilyInPolyTime (fun q : Graph × List ℕ => Graph.cycleChainBool (r q.1) q.2)
      (encPair encGraph (encList encNat)) encBool := by
  have hproj : ComputableTidilyInPolyTime
      (fun q : ((Graph × List ℕ) × ℕ) × ℕ => ((q.1.1.1, q.1.2), q.2))
      (encPair (encPair (encPair encGraph (encList encNat)) encNat) encNat)
      (encPair (encPair encGraph encNat) encNat) := by
    fun_prop
  exact Graph.computableTidilyInPolyTime_cycleChainBool (hr.comp hproj) (snd _ _)

namespace DirHamPath

/-- The verifier for `DirHamPath`: decode a list of vertices from the certificate
(`Graph.decodeVertexList`) and check that it lists every declared vertex exactly once, starts at
`s`, ends at `t`, and that consecutive vertices are joined by arcs. -/
def verifier : (Graph × ℕ × ℕ) × List Bool → Bool :=
  Graph.verifyOrdering (fun x => x.1.1) fun x p =>
    decide (p.head? = some x.2.1) && decide (p.getLast? = some x.2.2) &&
      Graph.chainBool x.1.arcBool p

/-- `DirHamPath.verifier` verifies `DirHamPath` with certificates of length `n ^ 2` for instances
of encoded length `n`. -/
theorem isVerifier :
    IsVerifier (encPair encGraph (encPair encNat encNat)) (Polynomial.X ^ 2) verifier DirHamPath :=
  Graph.isVerifier_verifyOrdering
    (P := fun (x : Graph × ℕ × ℕ) p => p.head? = some x.2.1 ∧ p.getLast? = some x.2.2 ∧
      p.IsChain fun u v => (u, v) ∈ x.1.2)
    length_vertices_le_encPath fun x p => by
      simp only [Bool.and_eq_true, decide_eq_true_eq,
        Graph.chainBool_eq_true_iff (Graph.arcBool_eq_true_iff x.1), and_assoc]

/-- The `DirHamPath` verifier is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_verifier :
    ComputableTidilyInPolyTime verifier
      (encPair (encPair encGraph (encPair encNat encNat)) encBits) encBool :=
  Graph.computableTidilyInPolyTime_verifyOrdering (by unfold encGraph; fun_prop)
    (computableTidilyInPolyTime_pathCheck Graph.computableTidilyInPolyTime_arcBool)

/-- `DirHamPath` belongs to `NP`. -/
theorem mem_NP : DirHamPath ∈ NP (encPair encGraph (encPair encNat encNat)) :=
  ⟨_, verifier, computableTidilyInPolyTime_verifier, isVerifier⟩

end DirHamPath

namespace DirHamCycle

/-- The verifier for `DirHamCycle`: decode a list of vertices from the certificate
(`Graph.decodeVertexList`) and check that it is nonempty, lists every declared vertex exactly
once, and that cyclically consecutive vertices are joined by arcs. -/
def verifier : Graph × List Bool → Bool :=
  Graph.verifyOrdering (fun G => G.1) fun G p =>
    decide (p ≠ []) && Graph.cycleChainBool G.arcBool p

/-- `DirHamCycle.verifier` verifies `DirHamCycle` with certificates of length `n ^ 2` for graphs
of encoded length `n`. -/
theorem isVerifier : IsVerifier encGraph (Polynomial.X ^ 2) verifier DirHamCycle :=
  Graph.isVerifier_verifyOrdering
    (P := fun (G : Graph) p => p ≠ [] ∧ (p : Cycle ℕ).Chain fun u v => (u, v) ∈ G.2)
    Graph.length_vertices_le_encGraph fun G p => by
      simp only [Bool.and_eq_true, decide_eq_true_eq,
        Graph.cycleChainBool_eq_true_iff (Graph.arcBool_eq_true_iff G)]

/-- The `DirHamCycle` verifier is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_verifier :
    ComputableTidilyInPolyTime verifier (encPair encGraph encBits) encBool :=
  Graph.computableTidilyInPolyTime_verifyOrdering (by unfold encGraph; fun_prop)
    (bool_and' (by fun_prop) (computableTidilyInPolyTime_cycleCheck
      Graph.computableTidilyInPolyTime_arcBool))

/-- `DirHamCycle` belongs to `NP`. -/
theorem mem_NP : DirHamCycle ∈ NP encGraph :=
  ⟨_, verifier, computableTidilyInPolyTime_verifier, isVerifier⟩

end DirHamCycle

namespace HamPath

/-- The verifier for `HamPath`: decode a list of vertices from the certificate
(`Graph.decodeVertexList`) and check that it lists every declared vertex exactly once, starts at
`s`, ends at `t`, and that consecutive vertices are adjacent. -/
def verifier : (Graph × ℕ × ℕ) × List Bool → Bool :=
  Graph.verifyOrdering (fun x => x.1.1) fun x p =>
    decide (p.head? = some x.2.1) && decide (p.getLast? = some x.2.2) &&
      Graph.chainBool x.1.adjBool p

/-- `HamPath.verifier` verifies `HamPath` with certificates of length `n ^ 2` for instances of
encoded length `n`. -/
theorem isVerifier :
    IsVerifier (encPair encGraph (encPair encNat encNat)) (Polynomial.X ^ 2) verifier HamPath := by
  rintro ⟨G, s, t⟩
  rw [mem_HamPath_iff]
  refine Graph.isVerifier_verifyOrdering
    (P := fun (x : Graph × ℕ × ℕ) p => p.head? = some x.2.1 ∧ p.getLast? = some x.2.2 ∧
      p.IsChain x.1.toSimpleGraph.Adj)
    length_vertices_le_encPath (fun x p => ?_) (G, s, t)
  simp only [Bool.and_eq_true, decide_eq_true_eq,
    Graph.chainBool_eq_true_iff (Graph.adjBool_eq_true_iff x.1), and_assoc]

/-- The `HamPath` verifier is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_verifier :
    ComputableTidilyInPolyTime verifier
      (encPair (encPair encGraph (encPair encNat encNat)) encBits) encBool :=
  Graph.computableTidilyInPolyTime_verifyOrdering (by unfold encGraph; fun_prop)
    (computableTidilyInPolyTime_pathCheck Graph.computableTidilyInPolyTime_adjBool)

/-- `HamPath` belongs to `NP`. -/
theorem mem_NP : HamPath ∈ NP (encPair encGraph (encPair encNat encNat)) :=
  ⟨_, verifier, computableTidilyInPolyTime_verifier, isVerifier⟩

end HamPath

namespace HamCycle

/-- The verifier for `HamCycle`: decode a list of vertices from the certificate
(`Graph.decodeVertexList`) and check that it has at least three vertices, lists every declared
vertex exactly once, and that cyclically consecutive vertices are adjacent. -/
def verifier : Graph × List Bool → Bool :=
  Graph.verifyOrdering (fun G => G.1) fun G p =>
    decide (3 ≤ p.length) && Graph.cycleChainBool G.adjBool p

/-- `HamCycle.verifier` verifies `HamCycle` with certificates of length `n ^ 2` for graphs of
encoded length `n`. -/
theorem isVerifier : IsVerifier encGraph (Polynomial.X ^ 2) verifier HamCycle := by
  intro G
  rw [mem_HamCycle_iff]
  refine Graph.isVerifier_verifyOrdering
    (P := fun (G : Graph) p => 3 ≤ p.length ∧ (p : Cycle ℕ).Chain G.toSimpleGraph.Adj)
    Graph.length_vertices_le_encGraph (fun G p => ?_) G
  simp only [Bool.and_eq_true, decide_eq_true_eq,
    Graph.cycleChainBool_eq_true_iff (Graph.adjBool_eq_true_iff G)]

/-- The `HamCycle` verifier is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_verifier :
    ComputableTidilyInPolyTime verifier (encPair encGraph encBits) encBool :=
  Graph.computableTidilyInPolyTime_verifyOrdering (by unfold encGraph; fun_prop)
    (bool_and' (by fun_prop) (computableTidilyInPolyTime_cycleCheck
      Graph.computableTidilyInPolyTime_adjBool))

/-- `HamCycle` belongs to `NP`. -/
theorem mem_NP : HamCycle ∈ NP encGraph :=
  ⟨_, verifier, computableTidilyInPolyTime_verifier, isVerifier⟩

end HamCycle

end Cslib.Complexity
