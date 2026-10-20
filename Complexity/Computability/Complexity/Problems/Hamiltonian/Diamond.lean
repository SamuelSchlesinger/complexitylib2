/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Hamiltonian
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Diamond graphs

The diamond construction of [Sipser, Theorem 7.46][Sipser2013] reduces satisfiability to directed
Hamiltonian paths. This file treats it for an arbitrary layout of the rows, so that reductions can
choose how many nodes each row has. A diamond graph (`Cslib.Complexity.Diamond.graph`) has

* `N` diamonds, diamond `i` with a top node, a bottom node (the top of diamond `i + 1`), and a row
  of `3 * slots i + 3` nodes joined both ways in a line; the top has arcs to both ends of the row,
  and both ends have arcs to the bottom. Slot `s < slots i` of row `i` is the pair of row nodes
  `3 * s + 2` and `3 * s + 3`, and the nodes `3 * s + 1` separate the pairs;
* `M` clause nodes;
* a list of detours `(j, i, s, b)`, each through the node of clause `j` across slot `s` of row `i`:
  left to right when `b` is true, right to left when it is false.

When the detours across each slot all belong to one clause (`Cslib.Complexity.Diamond.WellFormed`),
the graph has a Hamiltonian path from the first top to the last bottom exactly when the rows can be
given directions so that every clause has a detour in the direction of its row
(`Cslib.Complexity.Diamond.mem_DirHamPath_iff`). In a Hamiltonian path every separator has its two
row neighbours as predecessor and successor, a detour must return to the slot it left, so all
separators of a row point the same way, and the node of a clause is entered from a slot whose row
points the way of the detour. Conversely, rows traversed in the given directions, each clause
visited by one detour in the direction of its row, form a Hamiltonian path.

Sipser's construction is the layout with one slot for each clause in every row; giving each row
only the slots of the detours through it makes the graph linear in the size of the formula.

## Main definitions

* `Cslib.Complexity.Diamond.graph`, `Cslib.Complexity.Diamond.cycleGraph`: diamond graphs and
  closed diamond graphs, with the node labels `Cslib.Complexity.Diamond.topNode`,
  `Cslib.Complexity.Diamond.rowNode` and `Cslib.Complexity.Diamond.clauseNode`, and the detours
  `Cslib.Complexity.Diamond.Detour`.
* `Cslib.Complexity.Diamond.WellFormed`, `Cslib.Complexity.Diamond.Satisfiable`.

## Main results

* `Cslib.Complexity.Diamond.mem_DirHamPath_iff`: Hamiltonian paths of a diamond graph are
  directions of its rows satisfying every clause.
* `Cslib.Complexity.Diamond.mem_DirHamCycle_iff`: Hamiltonian cycles of a closed diamond graph
  likewise.
* `Cslib.Complexity.Diamond.length_vertices`, `Cslib.Complexity.Diamond.length_arcs`: the size of a
  diamond graph.
* `Cslib.Complexity.Diamond.computableTidilyInPolyTime_graph`,
  `Cslib.Complexity.Diamond.computableTidilyInPolyTime_cycleGraph`: diamond graphs are computable
  in polynomial time from layouts computable in polynomial time.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

namespace Diamond

/-! ### Diamond graphs -/

/-- A detour `(j, i, s, b)`: through the node of clause `j`, across slot `s` of row `i`, left to
right when `b` is true and right to left otherwise. -/
abbrev Detour : Type := ℕ × ℕ × ℕ × Bool

/-- The top of diamond `i`, which is also the bottom of diamond `i - 1`. -/
def topNode (i : ℕ) : ℕ := Nat.pair 0 i

/-- Node `a` of the row of diamond `i`. -/
def rowNode (i a : ℕ) : ℕ := Nat.pair 1 (Nat.pair i a)

/-- The node of clause `j`. -/
def clauseNode (j : ℕ) : ℕ := Nat.pair 2 j

/-- The number of nodes in row `i`: a pair of nodes for each slot, separators between and around
the pairs, and the two ends. -/
def rowLength (slots : ℕ → ℕ) (i : ℕ) : ℕ := 3 * slots i + 3

/-- The arcs of diamond `i`: from its top to both ends of its row, from both ends to its bottom,
and both ways between consecutive row nodes. -/
def diamondArcs (slots : ℕ → ℕ) (i : ℕ) : List (ℕ × ℕ) :=
  [(topNode i, rowNode i 0), (topNode i, rowNode i (rowLength slots i - 1)),
    (rowNode i 0, topNode (i + 1)), (rowNode i (rowLength slots i - 1), topNode (i + 1))] ++
    (List.range (rowLength slots i - 1)).flatMap fun a =>
      [(rowNode i a, rowNode i (a + 1)), (rowNode i (a + 1), rowNode i a)]

/-- The arcs of the detour `d`. -/
def detourArcs (d : Detour) : List (ℕ × ℕ) :=
  if d.2.2.2 then
    [(rowNode d.2.1 (3 * d.2.2.1 + 2), clauseNode d.1),
      (clauseNode d.1, rowNode d.2.1 (3 * d.2.2.1 + 3))]
  else
    [(rowNode d.2.1 (3 * d.2.2.1 + 3), clauseNode d.1),
      (clauseNode d.1, rowNode d.2.1 (3 * d.2.2.1 + 2))]

/-- The arcs of the diamond graph: the diamonds and the detours. -/
def arcs (N : ℕ) (slots : ℕ → ℕ) (D : List Detour) : List (ℕ × ℕ) :=
  (List.range N).flatMap (diamondArcs slots) ++ D.flatMap detourArcs

/-- The vertices of the diamond graph: the tops, the rows and the clause nodes. -/
def vertices (N : ℕ) (slots : ℕ → ℕ) (M : ℕ) : List ℕ :=
  (List.range (N + 1)).map topNode ++
    (List.range N).flatMap (fun i => (List.range (rowLength slots i)).map (rowNode i)) ++
    (List.range M).map clauseNode

/-- The diamond graph with `N` diamonds whose rows have `slots i` slots, `M` clause nodes and the
detours `D`. -/
def graph (N : ℕ) (slots : ℕ → ℕ) (M : ℕ) (D : List Detour) : Graph :=
  (vertices N slots M, arcs N slots D)

/-- The diamond graph closed by an arc from the bottom of the last diamond to the top of the
first. -/
def cycleGraph (N : ℕ) (slots : ℕ → ℕ) (M : ℕ) (D : List Detour) : Graph :=
  (vertices N slots M, (topNode N, topNode 0) :: arcs N slots D)

/-- The detours go through declared nodes, and the detours across each slot all belong to one
clause. -/
structure WellFormed (N : ℕ) (slots : ℕ → ℕ) (M : ℕ) (D : List Detour) : Prop where
  clause_lt : ∀ d ∈ D, d.1 < M
  row_lt : ∀ d ∈ D, d.2.1 < N
  slot_lt : ∀ d ∈ D, d.2.2.1 < slots d.2.1
  clause_eq : ∀ d ∈ D, ∀ d' ∈ D, d.2.1 = d'.2.1 → d.2.2.1 = d'.2.2.1 → d.1 = d'.1

/-- Some directions of the rows give every clause `j < M` a detour in the direction of its row. -/
def Satisfiable (M : ℕ) (D : List Detour) : Prop :=
  ∃ dir : ℕ → Bool, ∀ j < M, ∃ d ∈ D, d.1 = j ∧ dir d.2.1 = d.2.2.2

/-! ### Vertices and arcs -/

@[simp] theorem topNode_inj {i i' : ℕ} : topNode i = topNode i' ↔ i = i' := by
  simp [topNode, Nat.pair_eq_pair]

@[simp] theorem rowNode_inj {i i' a a' : ℕ} : rowNode i a = rowNode i' a' ↔ i = i' ∧ a = a' := by
  simp [rowNode, Nat.pair_eq_pair]

@[simp] theorem clauseNode_inj {j j' : ℕ} : clauseNode j = clauseNode j' ↔ j = j' := by
  simp [clauseNode, Nat.pair_eq_pair]

@[simp] theorem topNode_ne_rowNode (i i' a : ℕ) : topNode i ≠ rowNode i' a := by
  simp [topNode, rowNode, Nat.pair_eq_pair]

@[simp] theorem rowNode_ne_topNode (i i' a : ℕ) : rowNode i' a ≠ topNode i :=
  (topNode_ne_rowNode i i' a).symm

@[simp] theorem topNode_ne_clauseNode (i j : ℕ) : topNode i ≠ clauseNode j := by
  simp [topNode, clauseNode, Nat.pair_eq_pair]

@[simp] theorem clauseNode_ne_topNode (i j : ℕ) : clauseNode j ≠ topNode i :=
  (topNode_ne_clauseNode i j).symm

@[simp] theorem rowNode_ne_clauseNode (i a j : ℕ) : rowNode i a ≠ clauseNode j := by
  simp [rowNode, clauseNode, Nat.pair_eq_pair]

@[simp] theorem clauseNode_ne_rowNode (i a j : ℕ) : clauseNode j ≠ rowNode i a :=
  (rowNode_ne_clauseNode i a j).symm

theorem rowLength_sub_one (slots : ℕ → ℕ) (i : ℕ) : rowLength slots i - 1 = 3 * slots i + 2 := by
  simp only [rowLength]
  omega

variable {N : ℕ} {slots : ℕ → ℕ} {M : ℕ} {D : List Detour}

theorem mem_vertices {v : ℕ} :
    v ∈ vertices N slots M ↔ (∃ i ≤ N, v = topNode i) ∨
      (∃ i < N, ∃ a < rowLength slots i, v = rowNode i a) ∨ (∃ j < M, v = clauseNode j) := by
  simp only [vertices, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
    Nat.lt_succ_iff]
  constructor
  · rintro ((⟨i, hi, rfl⟩ | ⟨i, hi, a, ha, rfl⟩) | ⟨j, hj, rfl⟩)
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr (Or.inl ⟨i, hi, a, ha, rfl⟩)
    · exact Or.inr (Or.inr ⟨j, hj, rfl⟩)
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, a, ha, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inl (Or.inl ⟨i, hi, rfl⟩)
    · exact Or.inl (Or.inr ⟨i, hi, a, ha, rfl⟩)
    · exact Or.inr ⟨j, hj, rfl⟩

theorem mem_arcs {u v : ℕ} :
    (u, v) ∈ arcs N slots D ↔
      (∃ i < N,
        (u = topNode i ∧ (v = rowNode i 0 ∨ v = rowNode i (rowLength slots i - 1))) ∨
        ((u = rowNode i 0 ∨ u = rowNode i (rowLength slots i - 1)) ∧ v = topNode (i + 1)) ∨
        (∃ a < rowLength slots i - 1, (u = rowNode i a ∧ v = rowNode i (a + 1)) ∨
          (u = rowNode i (a + 1) ∧ v = rowNode i a))) ∨
      (∃ d ∈ D,
        (d.2.2.2 = true ∧ ((u = rowNode d.2.1 (3 * d.2.2.1 + 2) ∧ v = clauseNode d.1) ∨
          (u = clauseNode d.1 ∧ v = rowNode d.2.1 (3 * d.2.2.1 + 3)))) ∨
        (d.2.2.2 = false ∧ ((u = rowNode d.2.1 (3 * d.2.2.1 + 3) ∧ v = clauseNode d.1) ∨
          (u = clauseNode d.1 ∧ v = rowNode d.2.1 (3 * d.2.2.1 + 2))))) := by
  simp only [arcs, List.mem_append, List.mem_flatMap, List.mem_range]
  refine or_congr ?_ (exists_congr fun d => and_congr_right fun _ => ?_)
  · refine exists_congr fun i => and_congr_right fun _ => ?_
    simp only [diamondArcs, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
      Prod.mk.injEq, List.not_mem_nil, or_false]
    constructor
    · rintro ((h | h | h | h) | ⟨a, ha, h | h⟩)
      · exact Or.inl ⟨h.1, Or.inl h.2⟩
      · exact Or.inl ⟨h.1, Or.inr h.2⟩
      · exact Or.inr (Or.inl ⟨Or.inl h.1, h.2⟩)
      · exact Or.inr (Or.inl ⟨Or.inr h.1, h.2⟩)
      · exact Or.inr (Or.inr ⟨a, ha, Or.inl h⟩)
      · exact Or.inr (Or.inr ⟨a, ha, Or.inr h⟩)
    · rintro (⟨h₁, h₂ | h₂⟩ | ⟨h₁ | h₁, h₂⟩ | ⟨a, ha, h | h⟩)
      · exact Or.inl (Or.inl ⟨h₁, h₂⟩)
      · exact Or.inl (Or.inr (Or.inl ⟨h₁, h₂⟩))
      · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨h₁, h₂⟩)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨h₁, h₂⟩)))
      · exact Or.inr ⟨a, ha, Or.inl h⟩
      · exact Or.inr ⟨a, ha, Or.inr h⟩
  · unfold detourArcs
    cases hb : d.2.2.2 <;> simp

/-- The number of vertices of a diamond graph, counted as listed. -/
theorem length_vertices (N : ℕ) (slots : ℕ → ℕ) (M : ℕ) :
    (vertices N slots M).length = 4 * N + 3 * ((List.range N).map slots).sum + M + 1 := by
  simp only [vertices, List.length_append, List.length_map, List.length_range,
    List.length_flatMap, rowLength]
  rw [List.sum_map_add, List.sum_map_mul_left]
  simp only [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  ring

/-- The number of arcs of a diamond graph, counted as listed. -/
theorem length_arcs (N : ℕ) (slots : ℕ → ℕ) (D : List Detour) :
    (arcs N slots D).length = 8 * N + 6 * ((List.range N).map slots).sum + 2 * D.length := by
  have h₁ : ∀ i, (diamondArcs slots i).length = 6 * slots i + 8 := fun i => by
    simp only [diamondArcs, List.length_append, List.length_cons, List.length_nil,
      List.length_flatMap, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul,
      rowLength_sub_one]
    ring
  have h₂ : ∀ d, (detourArcs d).length = 2 := fun d => by
    unfold detourArcs
    split_ifs <;> rfl
  simp only [arcs, List.length_append, List.length_flatMap, h₁, h₂]
  rw [List.sum_map_add, List.sum_map_mul_left]
  simp only [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  ring

/-- No arc enters the top of the first diamond. -/
theorem notMem_arcs_topNode_zero (u : ℕ) : (u, topNode 0) ∉ arcs N slots D := fun h => by
  rcases mem_arcs.1 h with
      ⟨i, -, ⟨-, h₂ | h₂⟩ | ⟨-, h₂⟩ | ⟨a, -, ⟨-, h₂⟩ | ⟨-, h₂⟩⟩⟩ |
      ⟨d, -, ⟨-, ⟨-, h₂⟩ | ⟨-, h₂⟩⟩ | ⟨-, ⟨-, h₂⟩ | ⟨-, h₂⟩⟩⟩ <;> simp at h₂

@[deprecated (since := "2026-10-19")] alias not_mem_arcs_topNode_zero := notMem_arcs_topNode_zero

/-- Split an arc of the diamond graph into its kinds, simplify the label equations, and close
position constraints by `omega`. -/
local macro "diamond_arc_omega " h:ident : tactic => `(tactic|
  (rcases mem_arcs.1 $h with
      ⟨i', hi', ⟨h₁, h₂ | h₂⟩ | ⟨h₁ | h₁, h₂⟩ | ⟨a', ha', ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩⟩ |
      ⟨⟨j', i', s', b'⟩, hd, ⟨hb, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ | ⟨hb, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩⟩ <;>
    (try simp only [rowLength_sub_one] at *) <;>
    simp only [rowNode_inj, topNode_inj, clauseNode_inj, rowNode_ne_topNode,
      topNode_ne_rowNode, rowNode_ne_clauseNode, clauseNode_ne_rowNode] at h₁ h₂ <;>
    (try casesm* _ ∧ _) <;>
    subst_vars <;>
    simp only [rowNode_inj, topNode_inj, clauseNode_inj, rowNode_ne_topNode,
      topNode_ne_rowNode, rowNode_ne_clauseNode, clauseNode_ne_rowNode, true_and, and_true,
      false_or, or_false, or_true, true_or] <;>
    omega))

/-- Split an arc at a node of a slot into its kinds: the conclusion is an adjacent row node, a
clause node of a detour across the slot, or a contradiction in the positions. -/
local macro "diamond_slot_arc " h:ident : tactic => `(tactic|
  (rcases $h:ident with h | h <;>
  rcases mem_arcs.1 h with
      ⟨i', hi', ⟨h₁, h₂ | h₂⟩ | ⟨h₁ | h₁, h₂⟩ | ⟨a', ha', ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩⟩ |
      ⟨⟨j', i', s', b'⟩, hd, ⟨hb, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ | ⟨hb, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩⟩ <;>
    (try simp only [rowLength_sub_one] at *) <;>
    simp only [rowNode_inj, topNode_inj, clauseNode_inj, rowNode_ne_topNode,
      topNode_ne_rowNode, rowNode_ne_clauseNode, clauseNode_ne_rowNode] at h₁ h₂ <;>
    (try casesm* _ ∧ _) <;>
    subst_vars <;>
    first
    | (left; simp only [rowNode_inj, true_and] <;> omega)
    | (right; left; simp only [rowNode_inj, true_and] <;> omega)
    | (right; right; refine ⟨_, hd, rfl, ?_, rfl⟩; dsimp only; omega)
    | omega))

/-- The neighbours of a separator are the adjacent row nodes. -/
private theorem separator_nbrs {i s u : ℕ}
    (h : (u, rowNode i (3 * s + 1)) ∈ arcs N slots D ∨
      (rowNode i (3 * s + 1), u) ∈ arcs N slots D) :
    u = rowNode i (3 * s) ∨ u = rowNode i (3 * s + 2) := by
  rcases h with h | h
  · diamond_arc_omega h
  · diamond_arc_omega h

/-- The neighbours of the left node of slot `s` are the adjacent row nodes and the nodes of the
clauses of the detours across the slot. -/
private theorem pairLeft_nbrs {i s u : ℕ} (hs : s < slots i)
    (h : (u, rowNode i (3 * s + 2)) ∈ arcs N slots D ∨
      (rowNode i (3 * s + 2), u) ∈ arcs N slots D) :
    u = rowNode i (3 * s + 1) ∨ u = rowNode i (3 * s + 3) ∨
      ∃ d ∈ D, d.2.1 = i ∧ d.2.2.1 = s ∧ u = clauseNode d.1 := by
  diamond_slot_arc h

/-- The neighbours of the right node of slot `s` are the adjacent row nodes and the nodes of the
clauses of the detours across the slot. -/
private theorem pairRight_nbrs {i s u : ℕ}
    (h : (u, rowNode i (3 * s + 3)) ∈ arcs N slots D ∨
      (rowNode i (3 * s + 3), u) ∈ arcs N slots D) :
    u = rowNode i (3 * s + 2) ∨ u = rowNode i (3 * s + 4) ∨
      ∃ d ∈ D, d.2.1 = i ∧ d.2.2.1 = s ∧ u = clauseNode d.1 := by
  diamond_slot_arc h

/-- Arcs into the left end of a row come from the top of its diamond or the next row node. -/
private theorem leftEnd_nbrs {i u : ℕ} (h : (u, rowNode i 0) ∈ arcs N slots D) :
    u = topNode i ∨ u = rowNode i 1 := by
  diamond_arc_omega h

/-- Arcs into the node of clause `j` come from the slots of its detours: from the left node for a
detour from left to right, from the right node otherwise. -/
private theorem clauseNode_nbrs {j u : ℕ} (h : (u, clauseNode j) ∈ arcs N slots D) :
    ∃ d ∈ D, d.1 = j ∧
      u = rowNode d.2.1 (if d.2.2.2 then 3 * d.2.2.1 + 2 else 3 * d.2.2.1 + 3) := by
  rcases mem_arcs.1 h with
      ⟨i', hi', ⟨h₁, h₂ | h₂⟩ | ⟨h₁ | h₁, h₂⟩ | ⟨a', ha', ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩⟩ |
      ⟨d, hd, ⟨hb, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ | ⟨hb, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩⟩ <;>
    simp only [clauseNode_inj, clauseNode_ne_topNode, clauseNode_ne_rowNode] at h₂
  · exact ⟨d, hd, h₂.symm, by simp [h₁, hb]⟩
  · exact ⟨d, hd, h₂.symm, by simp [h₁, hb]⟩

/-! ### Successors in a list -/

/-- `v` immediately follows `u` in the list `p`. -/
private def Follows (p : List ℕ) (u v : ℕ) : Prop := ∃ i, p[i]? = some u ∧ p[i + 1]? = some v

private theorem Follows.rel {R : ℕ → ℕ → Prop} {p : List ℕ} (hp : p.IsChain R) {u v : ℕ}
    (h : Follows p u v) : R u v := by
  obtain ⟨i, hu, hv⟩ := h
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hu
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.1 hv
  exact List.isChain_iff_getElem.1 hp i hi'

private theorem Follows.right_unique {p : List ℕ} (hnd : p.Nodup) {u v v' : ℕ}
    (h : Follows p u v) (h' : Follows p u v') : v = v' := by
  obtain ⟨i, hu, hv⟩ := h
  obtain ⟨j, hu', hv'⟩ := h'
  obtain rfl : i = j :=
    (hnd.getElem?_inj (List.getElem?_eq_some_iff.1 hu).1).1 (hu.trans hu'.symm)
  exact Option.some_injective _ (hv.symm.trans hv')

private theorem Follows.left_unique {p : List ℕ} (hnd : p.Nodup) {u u' v : ℕ}
    (h : Follows p u v) (h' : Follows p u' v) : u = u' := by
  obtain ⟨i, hu, hv⟩ := h
  obtain ⟨j, hu', hv'⟩ := h'
  obtain rfl : i = j := by
    have := (hnd.getElem?_inj (List.getElem?_eq_some_iff.1 hv).1).1 (hv.trans hv'.symm)
    omega
  exact Option.some_injective _ (hu.symm.trans hu')

private theorem Follows.asymm {p : List ℕ} (hnd : p.Nodup) {u v : ℕ} (h : Follows p u v) :
    ¬Follows p v u := by
  rintro ⟨j, hv', hu'⟩
  obtain ⟨i, hu, hv⟩ := h
  have h₁ := (hnd.getElem?_inj (List.getElem?_eq_some_iff.1 hu).1).1 (hu.trans hu'.symm)
  have h₂ := (hnd.getElem?_inj (List.getElem?_eq_some_iff.1 hv).1).1 (hv.trans hv'.symm)
  omega

private theorem exists_follows_of_ne_getLast {p : List ℕ} {v : ℕ} (hv : v ∈ p)
    (hlast : p.getLast? ≠ some v) : ∃ w, Follows p v w := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hv
  have hilt := (List.getElem?_eq_some_iff.1 hi).1
  have : i + 1 < p.length := by
    by_contra h
    apply hlast
    rw [List.getLast?_eq_getElem?, show p.length - 1 = i by omega, hi]
  exact ⟨p[i + 1], i, hi, List.getElem?_eq_getElem this⟩

private theorem exists_follows_of_ne_head {p : List ℕ} {v : ℕ} (hv : v ∈ p)
    (hhead : p.head? ≠ some v) : ∃ u, Follows p u v := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hv
  cases i with
  | zero => exact (hhead (by rw [List.head?_eq_getElem?, hi])).elim
  | succ i =>
    have := (List.getElem?_eq_some_iff.1 hi).1
    exact ⟨p[i], i, List.getElem?_eq_getElem (by omega), hi⟩

/-! ### Hamiltonian paths give directions satisfying every clause -/

section PathToDirections

variable {p : List ℕ}

private theorem rowNode_mem_vertices {i a : ℕ} (hi : i < N) (ha : a < rowLength slots i) :
    rowNode i a ∈ vertices N slots M :=
  mem_vertices.2 (Or.inr (Or.inl ⟨i, hi, a, ha, rfl⟩))

private theorem clauseNode_mem_vertices {j : ℕ} (hj : j < M) :
    clauseNode j ∈ vertices N slots M :=
  mem_vertices.2 (Or.inr (Or.inr ⟨j, hj, rfl⟩))

/-- In a Hamiltonian path, every node other than the start has a predecessor. -/
private theorem exists_pred
    (hp : (graph N slots M D).IsDirHamPath (topNode 0) (topNode N) p) {v : ℕ}
    (hv : v ∈ vertices N slots M) (hne : v ≠ topNode 0) : ∃ u, Follows p u v :=
  exists_follows_of_ne_head ((hp.2.1 v).2 hv) (by
    rw [hp.2.2.1]
    exact fun h => hne (Option.some_injective _ h).symm)

/-- In a Hamiltonian path, every node other than the end has a successor. -/
private theorem exists_succ
    (hp : (graph N slots M D).IsDirHamPath (topNode 0) (topNode N) p) {v : ℕ}
    (hv : v ∈ vertices N slots M) (hne : v ≠ topNode N) : ∃ w, Follows p v w :=
  exists_follows_of_ne_getLast ((hp.2.1 v).2 hv) (by
    rw [hp.2.2.2.1]
    exact fun h => hne (Option.some_injective _ h).symm)

/-- A separator is traversed either rightwards or leftwards. -/
private theorem separator_dir
    (hp : (graph N slots M D).IsDirHamPath (topNode 0) (topNode N) p) {i s : ℕ}
    (hi : i < N) (hs : s ≤ slots i) :
    (Follows p (rowNode i (3 * s)) (rowNode i (3 * s + 1)) ∧
        Follows p (rowNode i (3 * s + 1)) (rowNode i (3 * s + 2))) ∨
      (Follows p (rowNode i (3 * s + 2)) (rowNode i (3 * s + 1)) ∧
        Follows p (rowNode i (3 * s + 1)) (rowNode i (3 * s))) := by
  have hmem := rowNode_mem_vertices (slots := slots) (M := M) (a := 3 * s + 1) hi
    (by simp only [rowLength]; omega)
  obtain ⟨u, hu⟩ := exists_pred hp hmem (rowNode_ne_topNode _ _ _)
  obtain ⟨w, hw⟩ := exists_succ hp hmem (rowNode_ne_topNode _ _ _)
  rcases separator_nbrs (Or.inl (hu.rel hp.2.2.2.2)) with rfl | rfl <;>
    rcases separator_nbrs (Or.inr (hw.rel hp.2.2.2.2)) with rfl | rfl
  · exact absurd hw (hu.asymm hp.1)
  · exact Or.inl ⟨hu, hw⟩
  · exact Or.inr ⟨hu, hw⟩
  · exact absurd hw (hu.asymm hp.1)

/-- Separator `s + 1` written with the positions of slot `s`. -/
private theorem separator_dir_succ
    (hp : (graph N slots M D).IsDirHamPath (topNode 0) (topNode N) p) {i s : ℕ}
    (hi : i < N) (hs : s < slots i) :
    (Follows p (rowNode i (3 * s + 3)) (rowNode i (3 * s + 4)) ∧
        Follows p (rowNode i (3 * s + 4)) (rowNode i (3 * s + 5))) ∨
      (Follows p (rowNode i (3 * s + 5)) (rowNode i (3 * s + 4)) ∧
        Follows p (rowNode i (3 * s + 4)) (rowNode i (3 * s + 3))) := by
  have h := separator_dir hp hi (s := s + 1) (by omega)
  rwa [show 3 * (s + 1) = 3 * s + 3 by ring, show 3 * s + 3 + 1 = 3 * s + 4 by ring,
    show 3 * s + 3 + 2 = 3 * s + 5 by ring] at h

/-- The clause nodes adjacent to the two nodes of a slot are the same. -/
private theorem clauseNode_eq_of_slot (hD : WellFormed N slots M D) {i s : ℕ} {d d' : Detour}
    (hd : d ∈ D) (hd' : d' ∈ D) (hi : d.2.1 = i) (hs : d.2.2.1 = s) (hi' : d'.2.1 = i)
    (hs' : d'.2.2.1 = s) : clauseNode d.1 = clauseNode d'.1 := by
  rw [hD.clause_eq d hd d' hd' (hi.trans hi'.symm) (hs.trans hs'.symm)]

/-- If the separator before slot `s` is traversed rightwards, so is the separator after it. -/
private theorem pair_rightwards (hD : WellFormed N slots M D)
    (hp : (graph N slots M D).IsDirHamPath (topNode 0) (topNode N) p) {i s : ℕ}
    (hi : i < N) (hs : s < slots i)
    (h : Follows p (rowNode i (3 * s + 1)) (rowNode i (3 * s + 2))) :
    Follows p (rowNode i (3 * s + 4)) (rowNode i (3 * s + 5)) := by
  have hnd := hp.1
  have hch := hp.2.2.2.2
  have hq := rowNode_mem_vertices (slots := slots) (M := M) (a := 3 * s + 3) hi
    (by simp only [rowLength]; omega)
  have hpp := rowNode_mem_vertices (slots := slots) (M := M) (a := 3 * s + 2) hi
    (by simp only [rowLength]; omega)
  -- Leaving the right pair node towards the right separator makes it rightward.
  have hright : Follows p (rowNode i (3 * s + 3)) (rowNode i (3 * s + 4)) →
      Follows p (rowNode i (3 * s + 4)) (rowNode i (3 * s + 5)) := fun hq' => by
    rcases separator_dir_succ hp hi hs with ⟨-, h'⟩ | ⟨-, h'⟩
    · exact h'
    · exact absurd h' (hq'.asymm hnd)
  -- The successor of the right pair node lies to its right.
  have hsucc_q : ∀ w, Follows p (rowNode i (3 * s + 3)) w →
      w ≠ rowNode i (3 * s + 2) → (∀ d ∈ D, d.2.1 = i → d.2.2.1 = s → w ≠ clauseNode d.1) →
      Follows p (rowNode i (3 * s + 4)) (rowNode i (3 * s + 5)) := fun w hw h₁ h₂ => by
    rcases pairRight_nbrs (Or.inr (hw.rel hch)) with rfl | rfl | ⟨d, hd, hdi, hds, rfl⟩
    · exact (h₁ rfl).elim
    · exact hright hw
    · exact (h₂ d hd hdi hds rfl).elim
  obtain ⟨w, hw⟩ := exists_succ hp hpp (rowNode_ne_topNode _ _ _)
  rcases pairLeft_nbrs hs (Or.inr (hw.rel hch)) with rfl | rfl | ⟨d, hd, hdi, hds, rfl⟩
  · exact absurd hw (h.asymm hnd)
  · -- `p → q`: the successor of `q` is neither `p` nor a clause node of the slot.
    obtain ⟨w', hw'⟩ := exists_succ hp hq (rowNode_ne_topNode _ _ _)
    refine hsucc_q w' hw' (fun he => ?_) (fun d hd hdi hds he => ?_)
    · subst he
      exact hw'.asymm hnd hw
    · subst he
      rcases separator_dir_succ hp hi hs with ⟨h₁, -⟩ | ⟨-, h₁⟩
      · exact clauseNode_ne_rowNode _ _ _ (hw'.right_unique hnd h₁)
      · simpa using hw.left_unique hnd h₁
  · -- `p → c`: the successor of `q` is neither `p` nor a clause node of the slot.
    obtain ⟨w', hw'⟩ := exists_succ hp hq (rowNode_ne_topNode _ _ _)
    have hw'p : w' ≠ rowNode i (3 * s + 2) := fun he => by
      subst he
      simpa using hw'.left_unique hnd h
    have hw'c : ∀ d' ∈ D, d'.2.1 = i → d'.2.2.1 = s → w' ≠ clauseNode d'.1 := fun d' hd' hdi'
        hds' he => by
      rw [he, ← clauseNode_eq_of_slot hD hd hd' hdi hds hdi' hds'] at hw'
      simpa using hw'.left_unique hnd hw
    exact hsucc_q w' hw' hw'p hw'c

/-- The separator before slot `s` cannot be traversed leftwards while the separator after it is
traversed rightwards. -/
private theorem not_pair_left_right (hD : WellFormed N slots M D)
    (hp : (graph N slots M D).IsDirHamPath (topNode 0) (topNode N) p) {i s : ℕ}
    (hi : i < N) (hs : s < slots i) :
    ¬(Follows p (rowNode i (3 * s + 2)) (rowNode i (3 * s + 1)) ∧
      Follows p (rowNode i (3 * s + 3)) (rowNode i (3 * s + 4))) := by
  rintro ⟨hl, hr⟩
  have hnd := hp.1
  have hch := hp.2.2.2.2
  obtain ⟨u, hu⟩ := exists_pred hp
    (rowNode_mem_vertices (slots := slots) (M := M) (a := 3 * s + 2) hi
      (by simp only [rowLength]; omega)) (rowNode_ne_topNode _ _ _)
  rcases pairLeft_nbrs hs (Or.inl (hu.rel hch)) with rfl | rfl | ⟨d, hd, hdi, hds, rfl⟩
  · exact hu.asymm hnd hl
  · simpa using hu.right_unique hnd hr
  · obtain ⟨u', hu'⟩ := exists_pred hp
      (rowNode_mem_vertices (slots := slots) (M := M) (a := 3 * s + 3) hi
        (by simp only [rowLength]; omega)) (rowNode_ne_topNode _ _ _)
    rcases pairRight_nbrs (Or.inl (hu'.rel hch)) with rfl | rfl | ⟨d', hd', hdi', hds', rfl⟩
    · simpa using hu'.right_unique hnd hl
    · exact hu'.asymm hnd hr
    · rw [← clauseNode_eq_of_slot hD hd hd' hdi hds hdi' hds'] at hu'
      simpa using hu'.right_unique hnd hu

/-- All separators of a row are traversed in the same direction. -/
private theorem rightwards_iff (hD : WellFormed N slots M D)
    (hp : (graph N slots M D).IsDirHamPath (topNode 0) (topNode N) p) {i : ℕ} (hi : i < N) :
    ∀ s ≤ slots i, (Follows p (rowNode i (3 * s + 1)) (rowNode i (3 * s + 2)) ↔
      Follows p (rowNode i 1) (rowNode i 2))
  | 0, _ => Iff.rfl
  | s + 1, hs => by
    have ih := rightwards_iff hD hp hi s (by omega)
    rw [show 3 * (s + 1) + 1 = 3 * s + 4 by ring, show 3 * (s + 1) + 2 = 3 * s + 5 by ring,
      ← ih]
    refine ⟨fun h => ?_, pair_rightwards hD hp hi (by omega)⟩
    by_contra hs'
    rcases separator_dir hp hi (s := s) (by omega) with ⟨-, h'⟩ | ⟨h', -⟩
    · exact hs' h'
    · rcases separator_dir_succ hp hi (s := s) (by omega) with ⟨h'', -⟩ | ⟨-, h''⟩
      · exact not_pair_left_right hD hp hi (by omega) ⟨h', h''⟩
      · simpa using h''.right_unique hp.1 h

/-- A row is traversed rightwards exactly when its diamond is entered at the left end. -/
private theorem rightwards_iff_top
    (hp : (graph N slots M D).IsDirHamPath (topNode 0) (topNode N) p) {i : ℕ} (hi : i < N) :
    Follows p (rowNode i 1) (rowNode i 2) ↔ Follows p (topNode i) (rowNode i 0) := by
  have hnd := hp.1
  have h0 := separator_dir hp hi (s := 0) (Nat.zero_le _)
  simp only [mul_zero, zero_add] at h0
  constructor
  · intro h
    rcases h0 with ⟨h₁, -⟩ | ⟨-, h₁⟩
    · obtain ⟨u, hu⟩ := exists_pred hp
        (rowNode_mem_vertices (slots := slots) (M := M) (a := 0) hi
          (by simp only [rowLength]; omega)) (rowNode_ne_topNode _ _ _)
      rcases leftEnd_nbrs (hu.rel hp.2.2.2.2) with rfl | rfl
      · exact hu
      · exact (hu.asymm hnd h₁).elim
    · simpa using h.right_unique hnd h₁
  · intro h
    rcases h0 with ⟨-, h₁⟩ | ⟨-, h₁⟩
    · exact h₁
    · simpa using h.left_unique hnd h₁

/-- The node of clause `j` is entered by a detour in the direction of its row. -/
private theorem exists_detour (hD : WellFormed N slots M D)
    (hp : (graph N slots M D).IsDirHamPath (topNode 0) (topNode N) p) {j : ℕ} (hj : j < M) :
    ∃ d ∈ D, d.1 = j ∧
      (Follows p (topNode d.2.1) (rowNode d.2.1 0) ↔ d.2.2.2 = true) := by
  have hnd := hp.1
  obtain ⟨u, hu⟩ := exists_pred hp (clauseNode_mem_vertices (N := N) (slots := slots) hj)
    (clauseNode_ne_topNode _ _)
  obtain ⟨d, hd, hdj, rfl⟩ := clauseNode_nbrs (hu.rel hp.2.2.2.2)
  have hi := hD.row_lt d hd
  have hs := hD.slot_lt d hd
  refine ⟨d, hd, hdj, ?_⟩
  rw [← rightwards_iff_top hp hi]
  cases hb : d.2.2.2
  · simp only [hb, Bool.false_eq_true, ite_false] at hu
    rw [← rightwards_iff hD hp hi (d.2.2.1 + 1) (by omega),
      show 3 * (d.2.2.1 + 1) + 1 = 3 * d.2.2.1 + 4 by ring,
      show 3 * (d.2.2.1 + 1) + 2 = 3 * d.2.2.1 + 5 by ring]
    simp only [Bool.false_eq_true, iff_false]
    intro h
    rcases separator_dir_succ hp hi hs with ⟨h₁, -⟩ | ⟨-, h₁⟩
    · simpa using hu.right_unique hnd h₁
    · simpa using h₁.right_unique hnd h
  · simp only [hb, ite_true] at hu
    simp only [iff_true]
    rw [← rightwards_iff hD hp hi d.2.2.1 hs.le]
    rcases separator_dir hp hi (s := d.2.2.1) hs.le with ⟨-, h₁⟩ | ⟨h₁, -⟩
    · exact h₁
    · simpa using hu.right_unique hnd h₁

/-- A Hamiltonian path of the diamond graph gives directions of the rows satisfying every
clause. -/
theorem satisfiable_of_mem_DirHamPath (hD : WellFormed N slots M D)
    (h : (graph N slots M D, topNode 0, topNode N) ∈ DirHamPath) : Satisfiable M D := by
  classical
  obtain ⟨p, hp⟩ := h
  refine ⟨fun i => decide (Follows p (topNode i) (rowNode i 0)), fun j hj => ?_⟩
  obtain ⟨d, hd, hdj, hiff⟩ := exists_detour hD hp hj
  refine ⟨d, hd, hdj, ?_⟩
  cases hb : d.2.2.2 <;> simp_all

@[deprecated (since := "2026-10-19")] alias satisfiable_of_mem := satisfiable_of_mem_DirHamPath

end PathToDirections

/-! ### Directions satisfying every clause give Hamiltonian paths -/

section Blocks

variable {α : Type*} {R : α → α → Prop} {f : ℕ → List α} {n : ℕ}

/-- Nonempty chains indexed by `0, …, n - 1`, each linked to the next, form a chain. -/
private theorem isChain_flatMap_range (hne : ∀ a < n, f a ≠ [])
    (hblock : ∀ a < n, (f a).IsChain R)
    (hlink : ∀ a, a + 1 < n → ∀ x ∈ (f a).getLast?, ∀ y ∈ (f (a + 1)).head?, R x y) :
    ((List.range n).flatMap f).IsChain R := by
  rw [List.flatMap_def, List.isChain_flatten (by simpa using hne)]
  refine ⟨fun l hl => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hl
    exact hblock a (List.mem_range.1 ha)
  · rw [List.isChain_map, List.isChain_range]
    exact fun a ha => hlink a (by omega)

/-- Nonempty chains indexed by `n - 1, …, 0`, each linked to the previous, form a chain. -/
private theorem isChain_flatMap_range_reverse (hne : ∀ a < n, f a ≠ [])
    (hblock : ∀ a < n, (f a).IsChain R)
    (hlink : ∀ a, a + 1 < n → ∀ x ∈ (f (a + 1)).getLast?, ∀ y ∈ (f a).head?, R x y) :
    ((List.range n).reverse.flatMap f).IsChain R := by
  rw [List.flatMap_def, List.isChain_flatten (by simpa using hne)]
  refine ⟨fun l hl => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hl
    exact hblock a (List.mem_range.1 (List.mem_reverse.1 ha))
  · rw [List.isChain_map, List.isChain_reverse, List.isChain_range]
    exact fun a ha => hlink a (by omega)

private theorem head?_flatMap_range (hn : 0 < n) (h : f 0 ≠ []) :
    ((List.range n).flatMap f).head? = (f 0).head? := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [Nat.zero_add, List.range_succ_eq_map, List.flatMap_cons, List.head?_append_of_ne_nil _ h]

private theorem getLast?_flatMap_range (hn : 0 < n) (h : f (n - 1) ≠ []) :
    ((List.range n).flatMap f).getLast? = (f (n - 1)).getLast? := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [Nat.zero_add, Nat.add_sub_cancel] at h ⊢
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
    List.getLast?_append_of_ne_nil _ h]

private theorem head?_flatMap_range_reverse (hn : 0 < n) (h : f (n - 1) ≠ []) :
    ((List.range n).reverse.flatMap f).head? = (f (n - 1)).head? := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [Nat.zero_add, Nat.add_sub_cancel] at h ⊢
  rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.flatMap_cons, List.head?_append_of_ne_nil _ h]

private theorem getLast?_flatMap_range_reverse (hn : 0 < n) (h : f 0 ≠ []) :
    ((List.range n).reverse.flatMap f).getLast? = (f 0).getLast? := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [Nat.zero_add, List.range_succ_eq_map, List.reverse_cons, List.flatMap_append,
    List.flatMap_singleton, List.getLast?_append_of_ne_nil _ h]

end Blocks

section DirectionsToPath

variable (N slots M) (dir : ℕ → Bool) (pick : ℕ → Detour)

/-- The clause visited across slot `s` of row `i`: one whose picked detour crosses the slot. -/
private def visit (i s : ℕ) : Option ℕ :=
  (List.range M).find? fun j => decide ((pick j).2.1 = i ∧ (pick j).2.2.1 = s)

/-- Row node `a` of row `i` in a rightward traversal, followed by the node of the clause visited
across the slot starting at `a`. -/
private def rightStep (i a : ℕ) : List ℕ :=
  rowNode i a :: if a % 3 = 2 then ((visit M pick i (a / 3)).map clauseNode).toList else []

/-- Row node `a` of row `i` in a leftward traversal, followed by the node of the clause visited
across the slot ending at `a`. -/
private def leftStep (i a : ℕ) : List ℕ :=
  rowNode i a ::
    if a % 3 = 0 ∧ 0 < a then ((visit M pick i (a / 3 - 1)).map clauseNode).toList else []

/-- The traversal of row `i` in its direction, with the visited clauses. -/
private def rowPath (i : ℕ) : List ℕ :=
  if dir i then (List.range (rowLength slots i)).flatMap (rightStep M pick i)
  else (List.range (rowLength slots i)).reverse.flatMap (leftStep M pick i)

/-- The Hamiltonian path of the diamond graph read off directions of the rows. -/
private def hamPath : List ℕ :=
  (List.range N).flatMap (fun i => topNode i :: rowPath slots M dir pick i) ++ [topNode N]

variable {N slots M dir pick}

private theorem mem_rightStep {i a x : ℕ} : x ∈ rightStep M pick i a ↔ x = rowNode i a ∨
    (a % 3 = 2 ∧ ∃ j, visit M pick i (a / 3) = some j ∧ x = clauseNode j) := by
  unfold rightStep
  split_ifs with h
  · cases hv : visit M pick i (a / 3) <;> simp [h]
  · simp [h]

private theorem mem_leftStep {i a x : ℕ} : x ∈ leftStep M pick i a ↔ x = rowNode i a ∨
    ((a % 3 = 0 ∧ 0 < a) ∧ ∃ j, visit M pick i (a / 3 - 1) = some j ∧ x = clauseNode j) := by
  unfold leftStep
  split_ifs with h
  · cases hv : visit M pick i (a / 3 - 1) <;> simp [h]
  · simp [h]

private theorem rightStep_ne_nil (i a : ℕ) : rightStep M pick i a ≠ [] := List.cons_ne_nil _ _

private theorem leftStep_ne_nil (i a : ℕ) : leftStep M pick i a ≠ [] := List.cons_ne_nil _ _

private theorem rowLength_pos (i : ℕ) : 0 < rowLength slots i := by
  simp only [rowLength]
  omega

private theorem arc_of_mem_diamondArcs {i : ℕ} (hi : i < N) {e : ℕ × ℕ}
    (he : e ∈ diamondArcs slots i) : e ∈ arcs N slots D :=
  List.mem_append_left _ (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, he⟩)

private theorem arc_row_succ {i a : ℕ} (hi : i < N) (ha : a + 1 < rowLength slots i) :
    (rowNode i a, rowNode i (a + 1)) ∈ arcs N slots D :=
  arc_of_mem_diamondArcs hi (List.mem_append_right _
    (List.mem_flatMap.2 ⟨a, List.mem_range.2 (by omega), by simp⟩))

private theorem arc_row_pred {i a : ℕ} (hi : i < N) (ha : a + 1 < rowLength slots i) :
    (rowNode i (a + 1), rowNode i a) ∈ arcs N slots D :=
  arc_of_mem_diamondArcs hi (List.mem_append_right _
    (List.mem_flatMap.2 ⟨a, List.mem_range.2 (by omega), by simp⟩))

variable (hD : WellFormed N slots M D)
  (hpick : ∀ j < M, pick j ∈ D ∧ (pick j).1 = j ∧ dir (pick j).2.1 = (pick j).2.2.2)
include hD hpick

private theorem visit_eq_some_iff {i s j : ℕ} :
    visit M pick i s = some j ↔ j < M ∧ (pick j).2.1 = i ∧ (pick j).2.2.1 = s := by
  constructor
  · intro h
    have hmem := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    simp only [decide_eq_true_eq] at hp
    exact ⟨List.mem_range.1 hmem, hp⟩
  · rintro ⟨hj, hi, hs⟩
    cases hv : visit M pick i s with
    | none =>
      rw [visit, List.find?_eq_none] at hv
      exact absurd (by simp [hi, hs]) (hv j (List.mem_range.2 hj))
    | some j' =>
      have hmem := List.mem_range.1 (List.mem_of_find?_eq_some hv)
      have hp := List.find?_some hv
      simp only [decide_eq_true_eq] at hp
      have h₁ := (hpick j hj).2.1
      have h₂ := (hpick j' hmem).2.1
      have := hD.clause_eq _ (hpick j hj).1 _ (hpick j' hmem).1 (hi.trans hp.1.symm)
        (hs.trans hp.2.symm)
      rw [h₁, h₂] at this
      rw [this]

omit hD in
/-- The arcs of the picked detour of a clause, in the direction of its row. -/
private theorem arc_detour {j : ℕ} (hj : j < M) :
    (dir (pick j).2.1 = true →
      (rowNode (pick j).2.1 (3 * (pick j).2.2.1 + 2), clauseNode j) ∈ arcs N slots D ∧
      (clauseNode j, rowNode (pick j).2.1 (3 * (pick j).2.2.1 + 3)) ∈ arcs N slots D) ∧
    (dir (pick j).2.1 = false →
      (rowNode (pick j).2.1 (3 * (pick j).2.2.1 + 3), clauseNode j) ∈ arcs N slots D ∧
      (clauseNode j, rowNode (pick j).2.1 (3 * (pick j).2.2.1 + 2)) ∈ arcs N slots D) := by
  obtain ⟨hmem, hcl, hdir⟩ := hpick j hj
  have harc : ∀ e ∈ detourArcs (pick j), e ∈ arcs N slots D := fun e he =>
    List.mem_append_right _ (List.mem_flatMap.2 ⟨pick j, hmem, he⟩)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hb : (pick j).2.2.2 = true := hdir ▸ h
    exact ⟨harc _ (by simp [detourArcs, hb, hcl]), harc _ (by simp [detourArcs, hb, hcl])⟩
  · have hb : (pick j).2.2.2 = false := hdir ▸ h
    exact ⟨harc _ (by simp [detourArcs, hb, hcl]), harc _ (by simp [detourArcs, hb, hcl])⟩

/-- No clause is visited across the right end of a row. -/
private theorem visit_last (i : ℕ) : visit M pick i (slots i) = none := by
  cases hv : visit M pick i (slots i) with
  | none => rfl
  | some j =>
    obtain ⟨hj, hi, hs⟩ := (visit_eq_some_iff hD hpick).1 hv
    have := hD.slot_lt _ (hpick j hj).1
    rw [hi, hs] at this
    exact absurd this (lt_irrefl _)

/-- The traversal of a row, its first and last node, and its arcs. -/
private theorem rowPath_spec {i : ℕ} (hi : i < N) :
    (rowPath slots M dir pick i).IsChain (fun u v => (u, v) ∈ arcs N slots D) ∧
    (∀ x ∈ (rowPath slots M dir pick i).head?, (topNode i, x) ∈ arcs N slots D) ∧
    (∀ x ∈ (rowPath slots M dir pick i).getLast?, (x, topNode (i + 1)) ∈ arcs N slots D) ∧
    rowPath slots M dir pick i ≠ [] := by
  have hm := rowLength_sub_one slots i
  have hpos := rowLength_pos (slots := slots) i
  have hdiam : ∀ e ∈ diamondArcs slots i, e ∈ arcs N slots D := fun e he =>
    arc_of_mem_diamondArcs hi he
  unfold rowPath
  split_ifs with hd
  · refine ⟨isChain_flatMap_range (fun a _ => rightStep_ne_nil i a) (fun a ha => ?_)
      (fun a ha => ?_), ?_, ?_, ?_⟩
    · unfold rightStep
      split_ifs with h
      · cases hv : visit M pick i (a / 3) with
        | none => exact List.IsChain.singleton _
        | some j =>
          obtain ⟨hj, hji, hjs⟩ := (visit_eq_some_iff hD hpick).1 hv
          have := ((arc_detour (N := N) (slots := slots) hpick hj).1 (hji ▸ hd)).1
          rw [hji, hjs, show 3 * (a / 3) + 2 = a by omega] at this
          exact List.IsChain.cons_cons this (List.IsChain.singleton _)
      · exact List.IsChain.singleton _
    · intro x hx y hy
      simp only [rightStep, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      unfold rightStep at hx
      split_ifs at hx with h
      · cases hv : visit M pick i (a / 3) with
        | none =>
          simp only [hv, Option.map_none, Option.toList_none, List.getLast?_singleton,
            Option.mem_def, Option.some.injEq] at hx
          subst hx
          exact arc_row_succ hi ha
        | some j =>
          simp only [hv, Option.map_some, Option.toList_some, List.getLast?_cons_cons,
            List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
          subst hx
          obtain ⟨hj, hji, hjs⟩ := (visit_eq_some_iff hD hpick).1 hv
          have := ((arc_detour (N := N) (slots := slots) hpick hj).1 (hji ▸ hd)).2
          rwa [hji, hjs, show 3 * (a / 3) + 3 = a + 1 by omega] at this
      · simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
        subst hx
        exact arc_row_succ hi ha
    · intro x hx
      rw [head?_flatMap_range hpos (rightStep_ne_nil i 0)] at hx
      simp only [rightStep, List.head?_cons, Option.mem_def, Option.some.injEq] at hx
      subst hx
      exact hdiam _ (by simp [diamondArcs])
    · intro x hx
      rw [getLast?_flatMap_range hpos (rightStep_ne_nil i _)] at hx
      unfold rightStep at hx
      rw [show (rowLength slots i - 1) / 3 = slots i by omega, visit_last hD hpick] at hx
      simp only [Option.map_none, Option.toList_none, ite_self, List.getLast?_singleton,
        Option.mem_def, Option.some.injEq] at hx
      subst hx
      exact hdiam _ (by simp [diamondArcs])
    · simpa using ⟨0, hpos, rightStep_ne_nil i 0⟩
  · have hd' : dir i = false := by simpa using hd
    refine ⟨isChain_flatMap_range_reverse (fun a _ => leftStep_ne_nil i a)
      (fun a ha => ?_) (fun a ha => ?_), ?_, ?_, ?_⟩
    · unfold leftStep
      split_ifs with h
      · cases hv : visit M pick i (a / 3 - 1) with
        | none => exact List.IsChain.singleton _
        | some j =>
          obtain ⟨hj, hji, hjs⟩ := (visit_eq_some_iff hD hpick).1 hv
          have := ((arc_detour (N := N) (slots := slots) hpick hj).2 (hji ▸ hd')).1
          rw [hji, hjs, show 3 * (a / 3 - 1) + 3 = a by omega] at this
          exact List.IsChain.cons_cons this (List.IsChain.singleton _)
      · exact List.IsChain.singleton _
    · intro x hx y hy
      simp only [leftStep, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      unfold leftStep at hx
      split_ifs at hx with h
      · cases hv : visit M pick i ((a + 1) / 3 - 1) with
        | none =>
          simp only [hv, Option.map_none, Option.toList_none, List.getLast?_singleton,
            Option.mem_def, Option.some.injEq] at hx
          subst hx
          exact arc_row_pred hi ha
        | some j =>
          simp only [hv, Option.map_some, Option.toList_some, List.getLast?_cons_cons,
            List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
          subst hx
          obtain ⟨hj, hji, hjs⟩ := (visit_eq_some_iff hD hpick).1 hv
          have := ((arc_detour (N := N) (slots := slots) hpick hj).2 (hji ▸ hd')).2
          rwa [hji, hjs, show 3 * ((a + 1) / 3 - 1) + 2 = a by omega] at this
      · simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
        subst hx
        exact arc_row_pred hi ha
    · intro x hx
      rw [head?_flatMap_range_reverse hpos (leftStep_ne_nil i _)] at hx
      simp only [leftStep, List.head?_cons, Option.mem_def, Option.some.injEq] at hx
      subst hx
      exact hdiam _ (by simp [diamondArcs])
    · intro x hx
      rw [getLast?_flatMap_range_reverse hpos (leftStep_ne_nil i 0)] at hx
      simp only [leftStep, lt_irrefl, and_false, ite_false, List.getLast?_singleton,
        Option.mem_def, Option.some.injEq] at hx
      subst hx
      exact hdiam _ (by simp [diamondArcs])
    · simpa using ⟨0, hpos, leftStep_ne_nil i 0⟩

/-- The traversal of row `i` visits its row nodes and the nodes of the clauses picked across it.
-/
private theorem mem_rowPath {i v : ℕ} :
    v ∈ rowPath slots M dir pick i ↔ (∃ a < rowLength slots i, v = rowNode i a) ∨
      (∃ j < M, (pick j).2.1 = i ∧ v = clauseNode j) := by
  have hm := rowLength_sub_one slots i
  unfold rowPath
  split_ifs
  · simp only [List.mem_flatMap, List.mem_range, mem_rightStep]
    constructor
    · rintro ⟨a, ha, rfl | ⟨-, j, hv, rfl⟩⟩
      · exact Or.inl ⟨a, ha, rfl⟩
      · obtain ⟨hj, hji, -⟩ := (visit_eq_some_iff hD hpick).1 hv
        exact Or.inr ⟨j, hj, hji, rfl⟩
    · rintro (⟨a, ha, rfl⟩ | ⟨j, hj, hji, rfl⟩)
      · exact ⟨a, ha, Or.inl rfl⟩
      · have hs := hD.slot_lt _ (hpick j hj).1
        rw [hji] at hs
        have hs' : (3 * (pick j).2.2.1 + 2) / 3 = (pick j).2.2.1 := by omega
        refine ⟨3 * (pick j).2.2.1 + 2, by simp only [rowLength]; omega,
          Or.inr ⟨by omega, j, ?_, rfl⟩⟩
        rw [hs']
        exact (visit_eq_some_iff hD hpick).2 ⟨hj, hji, rfl⟩
  · simp only [List.mem_flatMap, List.mem_reverse, List.mem_range, mem_leftStep]
    constructor
    · rintro ⟨a, ha, rfl | ⟨-, j, hv, rfl⟩⟩
      · exact Or.inl ⟨a, ha, rfl⟩
      · obtain ⟨hj, hji, -⟩ := (visit_eq_some_iff hD hpick).1 hv
        exact Or.inr ⟨j, hj, hji, rfl⟩
    · rintro (⟨a, ha, rfl⟩ | ⟨j, hj, hji, rfl⟩)
      · exact ⟨a, ha, Or.inl rfl⟩
      · have hs := hD.slot_lt _ (hpick j hj).1
        rw [hji] at hs
        have hs' : (3 * (pick j).2.2.1 + 3) / 3 - 1 = (pick j).2.2.1 := by omega
        refine ⟨3 * (pick j).2.2.1 + 3, by simp only [rowLength]; omega,
          Or.inr ⟨⟨by omega, by omega⟩, j, ?_, rfl⟩⟩
        rw [hs']
        exact (visit_eq_some_iff hD hpick).2 ⟨hj, hji, rfl⟩

private theorem nodup_rowPath (i : ℕ) : (rowPath slots M dir pick i).Nodup := by
  unfold rowPath
  split_ifs
  · rw [List.nodup_flatMap]
    refine ⟨fun a _ => ?_, List.nodup_range.pairwise_of_forall_ne fun a _ b _ hab => ?_⟩
    · unfold rightStep
      split_ifs
      · cases visit M pick i (a / 3) <;> simp
      · simp
    · intro x hx hx'
      rw [mem_rightStep] at hx hx'
      rcases hx with rfl | ⟨h, j, hv, rfl⟩ <;> rcases hx' with h' | ⟨h', j', hv', h''⟩
      · simp only [rowNode_inj] at h'
        omega
      · simp at h''
      · simp at h'
      · simp only [clauseNode_inj] at h''
        subst h''
        obtain ⟨-, -, hs⟩ := (visit_eq_some_iff hD hpick).1 hv
        obtain ⟨-, -, hs'⟩ := (visit_eq_some_iff hD hpick).1 hv'
        omega
  · rw [List.nodup_flatMap]
    refine ⟨fun a _ => ?_,
      (List.nodup_reverse.2 List.nodup_range).pairwise_of_forall_ne fun a _ b _ hab => ?_⟩
    · unfold leftStep
      split_ifs
      · cases visit M pick i (a / 3 - 1) <;> simp
      · simp
    · intro x hx hx'
      rw [mem_leftStep] at hx hx'
      rcases hx with rfl | ⟨h, j, hv, rfl⟩ <;> rcases hx' with h' | ⟨h', j', hv', h''⟩
      · simp only [rowNode_inj] at h'
        omega
      · simp at h''
      · simp at h'
      · simp only [clauseNode_inj] at h''
        subst h''
        obtain ⟨-, -, hs⟩ := (visit_eq_some_iff hD hpick).1 hv
        obtain ⟨-, -, hs'⟩ := (visit_eq_some_iff hD hpick).1 hv'
        omega

/-- The Hamiltonian path read off directions of the rows satisfying every clause. -/
private theorem isDirHamPath_hamPath :
    (graph N slots M D).IsDirHamPath (topNode 0) (topNode N) (hamPath N slots M dir pick) := by
  have hblock_ne : ∀ i, topNode i :: rowPath slots M dir pick i ≠ [] :=
    fun _ => List.cons_ne_nil _ _
  have hmem_block : ∀ {i v}, v ∈ topNode i :: rowPath slots M dir pick i ↔ v = topNode i ∨
      (∃ a < rowLength slots i, v = rowNode i a) ∨
      (∃ j < M, (pick j).2.1 = i ∧ v = clauseNode j) := by
    intro i v
    rw [List.mem_cons, mem_rowPath hD hpick]
  refine ⟨?_, fun v => ?_, ?_, ?_, ?_⟩
  · -- No repetitions.
    rw [hamPath, List.nodup_append, List.nodup_flatMap]
    refine ⟨⟨fun i _ => List.nodup_cons.2 ⟨fun h => ?_, nodup_rowPath hD hpick i⟩,
      List.nodup_range.pairwise_of_forall_ne fun i _ i' _ hii' => ?_⟩,
      List.nodup_singleton _, fun v hv w hw => ?_⟩
    · rcases (mem_rowPath hD hpick).1 h with ⟨a, -, h⟩ | ⟨j, -, -, h⟩ <;> simp at h
    · intro x hx hx'
      rw [hmem_block] at hx hx'
      rcases hx with rfl | ⟨a, -, rfl⟩ | ⟨j, -, hj, rfl⟩ <;>
        rcases hx' with h | ⟨a', -, h⟩ | ⟨j', -, hj', h⟩ <;>
        simp only [topNode_inj, rowNode_inj, clauseNode_inj, topNode_ne_rowNode,
          rowNode_ne_topNode, topNode_ne_clauseNode, clauseNode_ne_topNode,
          rowNode_ne_clauseNode, clauseNode_ne_rowNode] at h <;> grind
    · rw [List.mem_singleton] at hw
      subst hw
      obtain ⟨i, hi, hv⟩ := List.mem_flatMap.1 hv
      rw [List.mem_range] at hi
      rcases hmem_block.1 hv with rfl | ⟨a, -, rfl⟩ | ⟨j, -, -, rfl⟩
      · simp only [ne_eq, topNode_inj]
        omega
      · simp
      · simp
  · -- Every vertex is visited.
    change v ∈ hamPath N slots M dir pick ↔ v ∈ vertices N slots M
    rw [mem_vertices, hamPath, List.mem_append, List.mem_flatMap, List.mem_singleton]
    constructor
    · rintro (⟨i, hi, hv⟩ | rfl)
      · rw [List.mem_range] at hi
        rcases hmem_block.1 hv with rfl | ⟨a, ha, rfl⟩ | ⟨j, hj, -, rfl⟩
        · exact Or.inl ⟨i, hi.le, rfl⟩
        · exact Or.inr (Or.inl ⟨i, hi, a, ha, rfl⟩)
        · exact Or.inr (Or.inr ⟨j, hj, rfl⟩)
      · exact Or.inl ⟨_, le_rfl, rfl⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, a, ha, rfl⟩ | ⟨j, hj, rfl⟩)
      · rcases hi.lt_or_eq with hi | rfl
        · exact Or.inl ⟨i, List.mem_range.2 hi, hmem_block.2 (Or.inl rfl)⟩
        · exact Or.inr rfl
      · exact Or.inl ⟨i, List.mem_range.2 hi, hmem_block.2 (Or.inr (Or.inl ⟨a, ha, rfl⟩))⟩
      · exact Or.inl ⟨_, List.mem_range.2 (hD.row_lt _ (hpick j hj).1),
          hmem_block.2 (Or.inr (Or.inr ⟨j, hj, rfl, rfl⟩))⟩
  · -- It starts at the top of the first diamond.
    rw [hamPath]
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · rw [List.head?_append_of_ne_nil _ (by simpa using ⟨0, h⟩),
        head?_flatMap_range h (hblock_ne 0)]
      rfl
  · -- It ends at the bottom of the last diamond.
    rw [hamPath, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
    rfl
  · -- Consecutive vertices are joined by arcs.
    rw [hamPath, List.isChain_append]
    refine ⟨isChain_flatMap_range (fun i _ => hblock_ne i) (fun i hi => ?_) (fun i hi => ?_),
      List.IsChain.singleton _, ?_⟩
    · obtain ⟨hch, hhead, -, -⟩ := rowPath_spec hD hpick hi
      exact List.isChain_cons.2 ⟨hhead, hch⟩
    · intro x hx y hy
      obtain ⟨-, -, hlast, hne⟩ := rowPath_spec hD hpick (i := i) (by omega)
      rw [← List.singleton_append, List.getLast?_append_of_ne_nil _ hne] at hx
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact hlast x hx
    · intro x hx y hy
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      rcases Nat.eq_zero_or_pos N with h | h
      · simp [h] at hx
      · obtain ⟨-, -, hlast, hne⟩ := rowPath_spec hD hpick (i := N - 1) (by omega)
        rw [getLast?_flatMap_range h (hblock_ne _), ← List.singleton_append,
          List.getLast?_append_of_ne_nil _ hne] at hx
        have := hlast x hx
        rwa [Nat.sub_add_cancel h] at this

end DirectionsToPath

/-- **Hamiltonian paths of diamond graphs.** A well-formed diamond graph has a Hamiltonian path
from the top of the first diamond to the bottom of the last exactly when its rows can be given
directions so that every clause has a detour in the direction of its row. -/
theorem mem_DirHamPath_iff (hD : WellFormed N slots M D) :
    (graph N slots M D, topNode 0, topNode N) ∈ DirHamPath ↔ Satisfiable M D := by
  refine ⟨satisfiable_of_mem_DirHamPath hD, fun ⟨dir, hdir⟩ => ?_⟩
  choose! pick hpick using hdir
  exact ⟨_, isDirHamPath_hamPath (dir := dir) hD fun j hj =>
    ⟨(hpick j hj).1, (hpick j hj).2.1, (hpick j hj).2.2⟩⟩

/-- **Hamiltonian cycles of closed diamond graphs.** A well-formed closed diamond graph has a
Hamiltonian cycle exactly when its rows can be given directions so that every clause has a detour
in the direction of its row. -/
theorem mem_DirHamCycle_iff {N M : ℕ} {slots : ℕ → ℕ} {D : List Detour}
    (hD : WellFormed N slots M D) :
    cycleGraph N slots M D ∈ DirHamCycle ↔ Satisfiable M D :=
  (Graph.mem_DirHamCycle_cons_iff (G := graph N slots M D)
    (mem_vertices.2 (Or.inl ⟨0, Nat.zero_le _, rfl⟩)) notMem_arcs_topNode_zero).trans
    (mem_DirHamPath_iff hD)

/-! ### Polynomial time -/

section PolyTime

open Turing.MultiTapeTM ComputableTidilyInPolyTime

/-- Detours encoded with unary clause, row and slot indices. -/
abbrev encDetour : Detour ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encUnary encBool))

/-- The top nodes are computable in polynomial time from unary indices. -/
@[fun_prop]
theorem computableTidilyInPolyTime_topNode :
    ComputableTidilyInPolyTime (fun i => topNode i) encUnary encNat :=
  unary_to_binary.comp (show ComputableTidilyInPolyTime (fun i => Nat.pair 0 i) _ _ by fun_prop)

/-- The row nodes are computable in polynomial time from unary indices. -/
@[fun_prop]
theorem computableTidilyInPolyTime_rowNode :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ => rowNode p.1 p.2) (encPair encUnary encUnary)
      encNat :=
  unary_to_binary.comp (show ComputableTidilyInPolyTime
    (fun p : ℕ × ℕ => Nat.pair 1 (Nat.pair p.1 p.2)) _ _ by fun_prop)

/-- The clause nodes are computable in polynomial time from unary indices. -/
@[fun_prop]
theorem computableTidilyInPolyTime_clauseNode :
    ComputableTidilyInPolyTime (fun j => clauseNode j) encUnary encNat :=
  unary_to_binary.comp (show ComputableTidilyInPolyTime (fun j => Nat.pair 2 j) _ _ by fun_prop)

/-- A diamond graph is computable in polynomial time from a layout computable in polynomial time,
with the numbers of diamonds, slots and clauses in unary. -/
theorem computableTidilyInPolyTime_graph {α : Type} {encIn : α ↪ List Bool} {N M : α → ℕ}
    {slots : α → ℕ → ℕ} {D : α → List Detour} (hN : ComputableTidilyInPolyTime N encIn encUnary)
    (hslots : ComputableTidilyInPolyTime (fun p : α × ℕ => slots p.1 p.2)
      (encPair encIn encUnary) encUnary)
    (hM : ComputableTidilyInPolyTime M encIn encUnary)
    (hD : ComputableTidilyInPolyTime D encIn (encList encDetour)) :
    ComputableTidilyInPolyTime (fun a => graph (N a) (slots a) (M a) (D a)) encIn encGraph := by
  unfold graph vertices arcs diamondArcs detourArcs rowLength encGraph
  fun_prop

/-- A closed diamond graph is computable in polynomial time from a layout computable in polynomial
time, with the numbers of diamonds, slots and clauses in unary. -/
theorem computableTidilyInPolyTime_cycleGraph {α : Type} {encIn : α ↪ List Bool} {N M : α → ℕ}
    {slots : α → ℕ → ℕ} {D : α → List Detour} (hN : ComputableTidilyInPolyTime N encIn encUnary)
    (hslots : ComputableTidilyInPolyTime (fun p : α × ℕ => slots p.1 p.2)
      (encPair encIn encUnary) encUnary)
    (hM : ComputableTidilyInPolyTime M encIn encUnary)
    (hD : ComputableTidilyInPolyTime D encIn (encList encDetour)) :
    ComputableTidilyInPolyTime (fun a => cycleGraph (N a) (slots a) (M a) (D a)) encIn
      encGraph := by
  unfold cycleGraph vertices arcs diamondArcs detourArcs rowLength encGraph
  fun_prop

end PolyTime

end Diamond

end Cslib.Complexity
