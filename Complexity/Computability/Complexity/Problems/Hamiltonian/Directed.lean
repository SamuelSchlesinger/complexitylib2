/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Hamiltonian
public import Complexity.Computability.Complexity.Problems.ThreeSAT
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Directed Hamiltonian paths and cycles are NP-hard

`SAT.toDirHamPath` is the diamond construction of [Sipser, Theorem 7.46][Sipser2013]. Each
variable occurrence of `φ`, in order of occurrence, gets a diamond: a top node, a bottom node (the
top of the next diamond), and a row of `3 * φ.length + 3` nodes joined both ways in a line. The
top has arcs to both ends of the row, and both ends have arcs to the bottom. Clause `j` owns the
pair of row nodes `3 * j + 2` and `3 * j + 3`, and the nodes `3 * j + 1` separate the pairs. A
literal `(x, b)` of clause `j` adds a detour through the node of clause `j` across the pair of `j`
in the diamond of the first occurrence of `x`: left to right when `b` is true, right to left when
it is false. The instance asks for a Hamiltonian path from the first top to the last bottom.

A satisfying assignment gives a path that traverses each row rightwards or leftwards according to
the value of its variable and visits each clause node by the detour of the first true literal of
the clause. Conversely, in a Hamiltonian path every separator has its two row neighbours as
predecessor and successor, a detour must return to the pair it left, so all separators of a row
point the same way, and the node of a clause is entered from a pair whose row points the way of
a true literal (`SAT.mem_SAT_of_toDirHamPath_mem`). Diamonds of repeated occurrences of a variable
carry no detours and can be traversed either way. Clauses of every width, including the empty
clause, are handled, so the reduction is from `SAT`; it also reduces `ThreeSAT` after rejecting
clauses with more than three literals.

`Graph.mem_DirHamCycle_cons_iff` closes Hamiltonian paths into cycles with an arc back to a start
vertex that no arc enters. The top of the first diamond is such a vertex, which gives
`SAT.toDirHamCycle`.

## Main definitions

* `Cslib.Complexity.SAT.toDirHamPath`, `Cslib.Complexity.SAT.toDirHamCycle`, with the node labels
  `Cslib.Complexity.SAT.topNode`, `Cslib.Complexity.SAT.rowNode` and
  `Cslib.Complexity.SAT.clauseNode`.

## Main results

* `Cslib.Complexity.SAT.toDirHamPath_mem_iff`: `toDirHamPath φ ∈ DirHamPath ↔ φ ∈ SAT`.
* `Cslib.Complexity.Graph.mem_DirHamCycle_cons_iff`: closing paths into cycles.
* `Cslib.Complexity.SAT.toDirHamCycle_mem_iff`: `toDirHamCycle φ ∈ DirHamCycle ↔ φ ∈ SAT`.
* `Cslib.Complexity.SAT.computableTidilyInPolyTime_toDirHamPath`,
  `Cslib.Complexity.SAT.computableTidilyInPolyTime_toDirHamCycle`: the reductions are
  polynomial-time.
* `Cslib.Complexity.polyTimeReducible_SAT_DirHamPath`,
  `Cslib.Complexity.polyTimeReducible_ThreeSAT_DirHamPath`, `Cslib.Complexity.DirHamPath_npHard`,
  `Cslib.Complexity.polyTimeReducible_SAT_DirHamCycle`, `Cslib.Complexity.DirHamCycle_npHard`.
* `Cslib.Complexity.DirHamPath_npComplete`, `Cslib.Complexity.DirHamCycle_npComplete`: the
  directed problems are `NP`-complete.

## References

* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM ComputableTidilyInPolyTime

namespace SAT

/-! ### The diamond graph -/

/-- The number of nodes in the row of each diamond: a pair of nodes for each clause, separators
between and around the pairs, and the two ends. -/
def rowLength (φ : CNF ℕ) : ℕ := 3 * φ.length + 3

/-- The top of diamond `i`, which is also the bottom of diamond `i - 1`. -/
def topNode (i : ℕ) : ℕ := Nat.pair 0 i

/-- Node `a` of the row of diamond `i`. Node `0` is the left end and node `rowLength φ - 1` the
right end; clause `j` owns nodes `3 * j + 2` and `3 * j + 3`, and the nodes `3 * j + 1` separate
the pairs. -/
def rowNode (i a : ℕ) : ℕ := Nat.pair 1 (Nat.pair i a)

/-- The node of clause `j`. -/
def clauseNode (j : ℕ) : ℕ := Nat.pair 2 j

/-- The arcs of diamond `i`: from its top to both ends of its row, from both ends to its bottom,
and both ways between consecutive row nodes. -/
def diamondArcs (φ : CNF ℕ) (i : ℕ) : List (ℕ × ℕ) :=
  [(topNode i, rowNode i 0), (topNode i, rowNode i (rowLength φ - 1)),
    (rowNode i 0, topNode (i + 1)), (rowNode i (rowLength φ - 1), topNode (i + 1))] ++
    (List.range (rowLength φ - 1)).flatMap fun a =>
      [(rowNode i a, rowNode i (a + 1)), (rowNode i (a + 1), rowNode i a)]

/-- The detour of the literal `l` through the node of clause `j`, in the diamond of the first
occurrence of its variable: left to right across the pair of `j` for a positive literal, right to
left for a negative one. -/
def literalArcs (φ : CNF ℕ) (j : ℕ) (l : Literal ℕ) : List (ℕ × ℕ) :=
  if l.2 then
    [(rowNode (φ.vars.idxOf l.1) (3 * j + 2), clauseNode j),
      (clauseNode j, rowNode (φ.vars.idxOf l.1) (3 * j + 3))]
  else
    [(rowNode (φ.vars.idxOf l.1) (3 * j + 3), clauseNode j),
      (clauseNode j, rowNode (φ.vars.idxOf l.1) (3 * j + 2))]

/-- The arcs of the diamond graph of `φ`: one diamond for each variable occurrence and the clause
detours. -/
def diamondGraphArcs (φ : CNF ℕ) : List (ℕ × ℕ) :=
  (List.range φ.vars.length).flatMap (diamondArcs φ) ++
    φ.zipIdx.flatMap fun c => c.1.flatMap (literalArcs φ c.2)

/-- The vertices of the diamond graph of `φ`: the tops, the rows and the clause nodes. -/
def diamondGraphVertices (φ : CNF ℕ) : List ℕ :=
  (List.range (φ.vars.length + 1)).map topNode ++
    (List.range φ.vars.length).flatMap (fun i => (List.range (rowLength φ)).map (rowNode i)) ++
    (List.range φ.length).map clauseNode

/-- The reduction from `SAT` to `DirHamPath` [Sipser, Theorem 7.46][Sipser2013]: the diamond
graph of `φ`, from the top of the first diamond to the bottom of the last. -/
def toDirHamPath (φ : CNF ℕ) : Graph × ℕ × ℕ :=
  ((diamondGraphVertices φ, diamondGraphArcs φ), topNode 0, topNode φ.vars.length)

/-! ### Arcs of the diamond graph -/

theorem mem_diamondGraphVertices {φ : CNF ℕ} {v : ℕ} :
    v ∈ diamondGraphVertices φ ↔ (∃ i ≤ φ.vars.length, v = topNode i) ∨
      (∃ i < φ.vars.length, ∃ a < rowLength φ, v = rowNode i a) ∨
      (∃ j < φ.length, v = clauseNode j) := by
  simp only [diamondGraphVertices, List.mem_append, List.mem_map, List.mem_range,
    List.mem_flatMap, Nat.lt_succ_iff]
  constructor
  · rintro ((⟨i, hi, rfl⟩ | ⟨i, hi, a, ha, rfl⟩) | ⟨j, hj, rfl⟩)
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr (Or.inl ⟨i, hi, a, ha, rfl⟩)
    · exact Or.inr (Or.inr ⟨j, hj, rfl⟩)
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, a, ha, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inl (Or.inl ⟨i, hi, rfl⟩)
    · exact Or.inl (Or.inr ⟨i, hi, a, ha, rfl⟩)
    · exact Or.inr ⟨j, hj, rfl⟩

theorem mem_diamondGraphArcs {φ : CNF ℕ} {u v : ℕ} :
    (u, v) ∈ diamondGraphArcs φ ↔
      (∃ i < φ.vars.length,
        (u = topNode i ∧ (v = rowNode i 0 ∨ v = rowNode i (rowLength φ - 1))) ∨
        ((u = rowNode i 0 ∨ u = rowNode i (rowLength φ - 1)) ∧ v = topNode (i + 1)) ∨
        (∃ a < rowLength φ - 1, (u = rowNode i a ∧ v = rowNode i (a + 1)) ∨
          (u = rowNode i (a + 1) ∧ v = rowNode i a))) ∨
      (∃ j < φ.length, ∃ l ∈ φ[j]?.getD [],
        (l.2 = true ∧ ((u = rowNode (φ.vars.idxOf l.1) (3 * j + 2) ∧ v = clauseNode j) ∨
          (u = clauseNode j ∧ v = rowNode (φ.vars.idxOf l.1) (3 * j + 3)))) ∨
        (l.2 = false ∧ ((u = rowNode (φ.vars.idxOf l.1) (3 * j + 3) ∧ v = clauseNode j) ∨
          (u = clauseNode j ∧ v = rowNode (φ.vars.idxOf l.1) (3 * j + 2))))) := by
  simp only [diamondGraphArcs, List.mem_append, List.mem_flatMap, List.mem_range]
  refine or_congr ?_ ?_
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
  · constructor
    · rintro ⟨⟨c, j⟩, hc, l, hl, he⟩
      have hc' := List.mem_zipIdx_iff_getElem?.1 hc
      simp only at hc' hl he
      obtain ⟨hj, hcj⟩ := List.getElem?_eq_some_iff.1 hc'
      refine ⟨j, hj, l, by rw [List.getElem?_eq_getElem hj, Option.getD_some, hcj]; exact hl, ?_⟩
      unfold literalArcs at he
      cases hb : l.2 <;> simp_all
    · rintro ⟨j, hj, l, hl, he⟩
      refine ⟨⟨φ[j], j⟩, List.mem_zipIdx_iff_getElem?.2 (by simp [hj]), l, by simpa [hj] using hl,
        ?_⟩
      unfold literalArcs
      cases hb : l.2 <;> simp_all

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

theorem rowLength_sub_one (φ : CNF ℕ) : rowLength φ - 1 = 3 * φ.length + 2 := by
  simp only [rowLength]
  omega

/-- Split an arc of the diamond graph into its kinds, simplify the label equations, and close
position constraints by `omega`. -/
local macro "diamond_arc_omega " h:ident : tactic => `(tactic|
  (rcases mem_diamondGraphArcs.1 $h with
      ⟨i', hi', ⟨h₁, h₂ | h₂⟩ | ⟨h₁ | h₁, h₂⟩ | ⟨a', ha', ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩⟩ |
      ⟨j', hj', l, hl, ⟨hb, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ | ⟨hb, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩⟩ <;>
    simp only [rowNode_inj, topNode_inj, clauseNode_inj, rowNode_ne_topNode,
      topNode_ne_rowNode, rowNode_ne_clauseNode, clauseNode_ne_rowNode] at h₁ h₂ <;>
    subst_vars <;>
    simp only [rowNode_inj, topNode_inj, clauseNode_inj, rowNode_ne_topNode,
      topNode_ne_rowNode, rowNode_ne_clauseNode, clauseNode_ne_rowNode, true_and, and_true,
      false_or, or_false] <;>
    omega))

/-- The neighbours of a separator are the adjacent row nodes. -/
private theorem separator_nbrs {φ : CNF ℕ} {i j u : ℕ}
    (h : (u, rowNode i (3 * j + 1)) ∈ diamondGraphArcs φ ∨
      (rowNode i (3 * j + 1), u) ∈ diamondGraphArcs φ) :
    u = rowNode i (3 * j) ∨ u = rowNode i (3 * j + 2) := by
  have hm := rowLength_sub_one φ
  rcases h with h | h
  · diamond_arc_omega h
  · diamond_arc_omega h

/-- The neighbours of the left node of the pair of clause `j` are the adjacent row nodes and the
node of clause `j`. -/
private theorem pairLeft_nbrs {φ : CNF ℕ} {i j u : ℕ} (hj : j < φ.length)
    (h : (u, rowNode i (3 * j + 2)) ∈ diamondGraphArcs φ ∨
      (rowNode i (3 * j + 2), u) ∈ diamondGraphArcs φ) :
    u = rowNode i (3 * j + 1) ∨ u = rowNode i (3 * j + 3) ∨ u = clauseNode j := by
  have hm := rowLength_sub_one φ
  rcases h with h | h
  · diamond_arc_omega h
  · diamond_arc_omega h

/-- The neighbours of the right node of the pair of clause `j` are the adjacent row nodes and the
node of clause `j`. -/
private theorem pairRight_nbrs {φ : CNF ℕ} {i j u : ℕ}
    (h : (u, rowNode i (3 * j + 3)) ∈ diamondGraphArcs φ ∨
      (rowNode i (3 * j + 3), u) ∈ diamondGraphArcs φ) :
    u = rowNode i (3 * j + 2) ∨ u = rowNode i (3 * j + 4) ∨ u = clauseNode j := by
  have hm := rowLength_sub_one φ
  rcases h with h | h
  · diamond_arc_omega h
  · diamond_arc_omega h

/-- Arcs into the left end of a row come from the top of its diamond or the next row node. -/
private theorem leftEnd_nbrs {φ : CNF ℕ} {i u : ℕ} (h : (u, rowNode i 0) ∈ diamondGraphArcs φ) :
    u = topNode i ∨ u = rowNode i 1 := by
  have hm := rowLength_sub_one φ
  diamond_arc_omega h

/-- Arcs into the node of clause `j` come from the pair of `j` in the diamond of one of its
literals: from the left node for a positive literal, from the right node for a negative one. -/
private theorem clauseNode_nbrs {φ : CNF ℕ} {j u : ℕ}
    (h : (u, clauseNode j) ∈ diamondGraphArcs φ) :
    ∃ l ∈ φ[j]?.getD [],
      u = rowNode (φ.vars.idxOf l.1) (if l.2 then 3 * j + 2 else 3 * j + 3) := by
  rcases mem_diamondGraphArcs.1 h with
      ⟨i', hi', ⟨h₁, h₂ | h₂⟩ | ⟨h₁ | h₁, h₂⟩ | ⟨a', ha', ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩⟩ |
      ⟨j', hj', l, hl, ⟨hb, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ | ⟨hb, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩⟩ <;>
    simp only [clauseNode_inj, clauseNode_ne_topNode, clauseNode_ne_rowNode] at h₂
  · subst h₂
    exact ⟨l, hl, by simp [h₁, hb]⟩
  · subst h₂
    exact ⟨l, hl, by simp [h₁, hb]⟩

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

/-! ### Hamiltonian paths of the diamond graph give satisfying assignments -/

section PathToAssignment

variable {φ : CNF ℕ} {p : List ℕ}

private theorem rowNode_mem_vertices {i a : ℕ} (hi : i < φ.vars.length) (ha : a < rowLength φ) :
    rowNode i a ∈ diamondGraphVertices φ :=
  mem_diamondGraphVertices.2 (Or.inr (Or.inl ⟨i, hi, a, ha, rfl⟩))

private theorem clauseNode_mem_vertices {j : ℕ} (hj : j < φ.length) :
    clauseNode j ∈ diamondGraphVertices φ :=
  mem_diamondGraphVertices.2 (Or.inr (Or.inr ⟨j, hj, rfl⟩))

/-- In a Hamiltonian path, every node other than the start has a predecessor. -/
private theorem exists_pred
    (hp : (toDirHamPath φ).1.IsDirHamPath (topNode 0) (topNode φ.vars.length) p) {v : ℕ}
    (hv : v ∈ diamondGraphVertices φ) (hne : v ≠ topNode 0) : ∃ u, Follows p u v :=
  exists_follows_of_ne_head ((hp.2.1 v).2 hv) (by
    rw [hp.2.2.1]
    exact fun h => hne (Option.some_injective _ h).symm)

/-- In a Hamiltonian path, every node other than the end has a successor. -/
private theorem exists_succ
    (hp : (toDirHamPath φ).1.IsDirHamPath (topNode 0) (topNode φ.vars.length) p) {v : ℕ}
    (hv : v ∈ diamondGraphVertices φ) (hne : v ≠ topNode φ.vars.length) :
    ∃ w, Follows p v w :=
  exists_follows_of_ne_getLast ((hp.2.1 v).2 hv) (by
    rw [hp.2.2.2.1]
    exact fun h => hne (Option.some_injective _ h).symm)

/-- A separator is traversed either rightwards or leftwards. -/
private theorem separator_dir
    (hp : (toDirHamPath φ).1.IsDirHamPath (topNode 0) (topNode φ.vars.length) p) {i j : ℕ}
    (hi : i < φ.vars.length) (hj : j ≤ φ.length) :
    (Follows p (rowNode i (3 * j)) (rowNode i (3 * j + 1)) ∧
        Follows p (rowNode i (3 * j + 1)) (rowNode i (3 * j + 2))) ∨
      (Follows p (rowNode i (3 * j + 2)) (rowNode i (3 * j + 1)) ∧
        Follows p (rowNode i (3 * j + 1)) (rowNode i (3 * j))) := by
  have hmem := rowNode_mem_vertices (a := 3 * j + 1) hi (by simp only [rowLength]; omega)
  obtain ⟨u, hu⟩ := exists_pred hp hmem (rowNode_ne_topNode _ _ _)
  obtain ⟨w, hw⟩ := exists_succ hp hmem (rowNode_ne_topNode _ _ _)
  rcases separator_nbrs (Or.inl (hu.rel hp.2.2.2.2)) with rfl | rfl <;>
    rcases separator_nbrs (Or.inr (hw.rel hp.2.2.2.2)) with rfl | rfl
  · exact absurd hw (hu.asymm hp.1)
  · exact Or.inl ⟨hu, hw⟩
  · exact Or.inr ⟨hu, hw⟩
  · exact absurd hw (hu.asymm hp.1)

/-- Separator `j + 1` written with the positions of the pair of clause `j`. -/
private theorem separator_dir_succ
    (hp : (toDirHamPath φ).1.IsDirHamPath (topNode 0) (topNode φ.vars.length) p) {i j : ℕ}
    (hi : i < φ.vars.length) (hj : j < φ.length) :
    (Follows p (rowNode i (3 * j + 3)) (rowNode i (3 * j + 4)) ∧
        Follows p (rowNode i (3 * j + 4)) (rowNode i (3 * j + 5))) ∨
      (Follows p (rowNode i (3 * j + 5)) (rowNode i (3 * j + 4)) ∧
        Follows p (rowNode i (3 * j + 4)) (rowNode i (3 * j + 3))) := by
  have h := separator_dir hp hi (j := j + 1) (by omega)
  rwa [show 3 * (j + 1) = 3 * j + 3 by ring, show 3 * j + 3 + 1 = 3 * j + 4 by ring,
    show 3 * j + 3 + 2 = 3 * j + 5 by ring] at h

/-- If the separator before the pair of clause `j` is traversed rightwards, so is the separator
after it. -/
private theorem pair_rightwards
    (hp : (toDirHamPath φ).1.IsDirHamPath (topNode 0) (topNode φ.vars.length) p) {i j : ℕ}
    (hi : i < φ.vars.length) (hj : j < φ.length)
    (h : Follows p (rowNode i (3 * j + 1)) (rowNode i (3 * j + 2))) :
    Follows p (rowNode i (3 * j + 4)) (rowNode i (3 * j + 5)) := by
  have hnd := hp.1
  have hch := hp.2.2.2.2
  have hlt : 3 * j + 5 < rowLength φ := by simp only [rowLength]; omega
  have hq := rowNode_mem_vertices (a := 3 * j + 3) hi (by omega)
  have hpp := rowNode_mem_vertices (a := 3 * j + 2) hi (by omega)
  -- Leaving the right pair node towards the right separator makes it rightward.
  have hright : Follows p (rowNode i (3 * j + 3)) (rowNode i (3 * j + 4)) →
      Follows p (rowNode i (3 * j + 4)) (rowNode i (3 * j + 5)) := fun hq' => by
    rcases separator_dir_succ hp hi hj with ⟨-, h'⟩ | ⟨-, h'⟩
    · exact h'
    · exact absurd h' (hq'.asymm hnd)
  -- The successor of the right pair node lies to its right.
  have hsucc_q : ∀ w, Follows p (rowNode i (3 * j + 3)) w →
      w ≠ rowNode i (3 * j + 2) → w ≠ clauseNode j →
      Follows p (rowNode i (3 * j + 4)) (rowNode i (3 * j + 5)) := fun w hw h₁ h₂ => by
    rcases pairRight_nbrs (Or.inr (hw.rel hch)) with rfl | rfl | rfl
    · exact (h₁ rfl).elim
    · exact hright hw
    · exact (h₂ rfl).elim
  obtain ⟨w, hw⟩ := exists_succ hp hpp (rowNode_ne_topNode _ _ _)
  rcases pairLeft_nbrs hj (Or.inr (hw.rel hch)) with rfl | rfl | rfl
  · exact absurd hw (h.asymm hnd)
  · -- `p → q`: the successor of `q` is neither `p` nor the clause node.
    obtain ⟨w', hw'⟩ := exists_succ hp hq (rowNode_ne_topNode _ _ _)
    refine hsucc_q w' hw' (fun he => ?_) (fun he => ?_)
    · subst he
      exact hw'.asymm hnd hw
    · subst he
      rcases separator_dir_succ hp hi hj with ⟨h₁, -⟩ | ⟨-, h₁⟩
      · exact clauseNode_ne_rowNode _ _ _ (hw'.right_unique hnd h₁)
      · simpa using hw.left_unique hnd h₁
  · -- `p → c`: the successor of `q` is neither `p` nor the clause node.
    obtain ⟨w', hw'⟩ := exists_succ hp hq (rowNode_ne_topNode _ _ _)
    have hw'p : w' ≠ rowNode i (3 * j + 2) := fun he => by
      subst he
      simpa using hw'.left_unique hnd h
    have hw'c : w' ≠ clauseNode j := fun he => by
      subst he
      simpa using hw'.left_unique hnd hw
    exact hsucc_q w' hw' hw'p hw'c

/-- The separator before the pair of clause `j` cannot be traversed leftwards while the separator
after it is traversed rightwards. -/
private theorem not_pair_left_right
    (hp : (toDirHamPath φ).1.IsDirHamPath (topNode 0) (topNode φ.vars.length) p) {i j : ℕ}
    (hi : i < φ.vars.length) (hj : j < φ.length) :
    ¬(Follows p (rowNode i (3 * j + 2)) (rowNode i (3 * j + 1)) ∧
      Follows p (rowNode i (3 * j + 3)) (rowNode i (3 * j + 4))) := by
  rintro ⟨hl, hr⟩
  have hnd := hp.1
  have hch := hp.2.2.2.2
  obtain ⟨u, hu⟩ := exists_pred hp (rowNode_mem_vertices (a := 3 * j + 2) hi
    (by simp only [rowLength]; omega)) (rowNode_ne_topNode _ _ _)
  rcases pairLeft_nbrs hj (Or.inl (hu.rel hch)) with rfl | rfl | rfl
  · exact hu.asymm hnd hl
  · simpa using hu.right_unique hnd hr
  · obtain ⟨u', hu'⟩ := exists_pred hp (rowNode_mem_vertices (a := 3 * j + 3) hi
      (by simp only [rowLength]; omega)) (rowNode_ne_topNode _ _ _)
    rcases pairRight_nbrs (Or.inl (hu'.rel hch)) with rfl | rfl | rfl
    · simpa using hu'.right_unique hnd hl
    · exact hu'.asymm hnd hr
    · simpa using hu'.right_unique hnd hu

/-- All separators of a row are traversed in the same direction. -/
private theorem rightwards_iff
    (hp : (toDirHamPath φ).1.IsDirHamPath (topNode 0) (topNode φ.vars.length) p) {i : ℕ}
    (hi : i < φ.vars.length) :
    ∀ j ≤ φ.length, (Follows p (rowNode i (3 * j + 1)) (rowNode i (3 * j + 2)) ↔
      Follows p (rowNode i 1) (rowNode i 2))
  | 0, _ => Iff.rfl
  | j + 1, hj => by
    have ih := rightwards_iff hp hi j (by omega)
    rw [show 3 * (j + 1) + 1 = 3 * j + 4 by ring, show 3 * (j + 1) + 2 = 3 * j + 5 by ring,
      ← ih]
    refine ⟨fun h => ?_, pair_rightwards hp hi (by omega)⟩
    by_contra hj'
    rcases separator_dir hp hi (j := j) (by omega) with ⟨-, h'⟩ | ⟨h', -⟩
    · exact hj' h'
    · rcases separator_dir_succ hp hi (j := j) (by omega) with ⟨h'', -⟩ | ⟨-, h''⟩
      · exact not_pair_left_right hp hi (by omega) ⟨h', h''⟩
      · simpa using h''.right_unique hp.1 h

/-- A row is traversed rightwards exactly when its diamond is entered at the left end. -/
private theorem rightwards_iff_top
    (hp : (toDirHamPath φ).1.IsDirHamPath (topNode 0) (topNode φ.vars.length) p) {i : ℕ}
    (hi : i < φ.vars.length) :
    Follows p (rowNode i 1) (rowNode i 2) ↔ Follows p (topNode i) (rowNode i 0) := by
  have hnd := hp.1
  have h0 := separator_dir hp hi (j := 0) (Nat.zero_le _)
  simp only [mul_zero, zero_add] at h0
  constructor
  · intro h
    rcases h0 with ⟨h₁, -⟩ | ⟨-, h₁⟩
    · obtain ⟨u, hu⟩ := exists_pred hp (rowNode_mem_vertices (a := 0) hi
        (by simp only [rowLength]; omega)) (rowNode_ne_topNode _ _ _)
      rcases leftEnd_nbrs (hu.rel hp.2.2.2.2) with rfl | rfl
      · exact hu
      · exact (hu.asymm hnd h₁).elim
    · simpa using h.right_unique hnd h₁
  · intro h
    rcases h0 with ⟨-, h₁⟩ | ⟨-, h₁⟩
    · exact h₁
    · simpa using h.left_unique hnd h₁

/-- The node of clause `j` is entered from the diamond of a literal of the clause that holds
under the assignment read off the directions of the rows. -/
private theorem exists_literal
    (hp : (toDirHamPath φ).1.IsDirHamPath (topNode 0) (topNode φ.vars.length) p) {j : ℕ}
    (hj : j < φ.length) :
    ∃ l ∈ φ[j], (Follows p (topNode (φ.vars.idxOf l.1)) (rowNode (φ.vars.idxOf l.1) 0) ↔
      l.2 = true) := by
  have hnd := hp.1
  obtain ⟨u, hu⟩ := exists_pred hp (clauseNode_mem_vertices hj) (clauseNode_ne_topNode _ _)
  obtain ⟨l, hl, rfl⟩ := clauseNode_nbrs (hu.rel hp.2.2.2.2)
  rw [List.getElem?_eq_getElem hj, Option.getD_some] at hl
  have hi : φ.vars.idxOf l.1 < φ.vars.length :=
    List.idxOf_lt_length_iff.2 (List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨_, List.getElem_mem hj, hl⟩,
      rfl⟩)
  refine ⟨l, hl, ?_⟩
  rw [← rightwards_iff_top hp hi]
  cases hb : l.2
  · simp only [hb, Bool.false_eq_true, ite_false] at hu
    rw [← rightwards_iff hp hi (j + 1) (by omega), show 3 * (j + 1) + 1 = 3 * j + 4 by ring,
      show 3 * (j + 1) + 2 = 3 * j + 5 by ring]
    simp only [Bool.false_eq_true, iff_false]
    intro h
    rcases separator_dir_succ hp hi hj with ⟨h₁, -⟩ | ⟨-, h₁⟩
    · simpa using hu.right_unique hnd h₁
    · simpa using h₁.right_unique hnd h
  · simp only [hb, ite_true] at hu
    simp only [iff_true]
    rw [← rightwards_iff hp hi j hj.le]
    rcases separator_dir hp hi (j := j) hj.le with ⟨-, h₁⟩ | ⟨h₁, -⟩
    · exact h₁
    · simpa using hu.right_unique hnd h₁

/-- A Hamiltonian path of the diamond graph yields a satisfying assignment. -/
theorem mem_SAT_of_toDirHamPath_mem {φ : CNF ℕ} (h : toDirHamPath φ ∈ DirHamPath) :
    φ ∈ SAT := by
  classical
  obtain ⟨p, hp⟩ := h
  refine ⟨fun x => decide (Follows p (topNode (φ.vars.idxOf x)) (rowNode (φ.vars.idxOf x) 0)),
    (CNF.eval_eq_true_iff _ _).2 fun c hc => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  obtain ⟨l, hl, hiff⟩ := exists_literal hp hj
  rw [Clause.eval_eq_true_iff]
  refine ⟨l, hl, ?_⟩
  cases hb : l.2 <;> simp_all

end PathToAssignment

/-! ### Satisfying assignments give Hamiltonian paths of the diamond graph -/

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

section AssignmentToPath

variable (φ : CNF ℕ) (σ : ℕ → Bool)

/-- The literal through which the path visits clause `j`: the first literal of the clause that
`σ` makes true. -/
private def chosenLiteral (j : ℕ) : Literal ℕ :=
  ((φ.getD j []).find? (Literal.eval σ)).getD (0, false)

/-- The diamond whose row visits clause `j`: that of the first occurrence of the variable of the
chosen literal. -/
private def assignedDiamond (j : ℕ) : ℕ := φ.vars.idxOf (chosenLiteral φ σ j).1

/-- Row node `a` of diamond `i` in a rightward traversal, followed by the node of the clause whose
pair starts at `a` when that clause is assigned to diamond `i`. -/
private def rightStep (i a : ℕ) : List ℕ :=
  rowNode i a ::
    if a % 3 = 2 ∧ a / 3 < φ.length ∧ assignedDiamond φ σ (a / 3) = i then [clauseNode (a / 3)]
    else []

/-- Row node `a` of diamond `i` in a leftward traversal, followed by the node of the clause whose
pair ends at `a` when that clause is assigned to diamond `i`. -/
private def leftStep (i a : ℕ) : List ℕ :=
  rowNode i a ::
    if a % 3 = 0 ∧ 0 < a ∧ a / 3 - 1 < φ.length ∧ assignedDiamond φ σ (a / 3 - 1) = i then
      [clauseNode (a / 3 - 1)]
    else []

/-- The traversal of the row of diamond `i`: rightwards when `σ` makes the variable of the
diamond true, leftwards otherwise, with the detours of the assigned clauses. -/
private def rowPath (i : ℕ) : List ℕ :=
  if σ (φ.vars.getD i 0) then (List.range (rowLength φ)).flatMap (rightStep φ σ i)
  else (List.range (rowLength φ)).reverse.flatMap (leftStep φ σ i)

/-- The Hamiltonian path of the diamond graph read off `σ`. -/
private def hamPath : List ℕ :=
  (List.range φ.vars.length).flatMap (fun i => topNode i :: rowPath φ σ i) ++
    [topNode φ.vars.length]

variable {φ σ}

private theorem chosenLiteral_spec (hσ : φ.eval σ = true) {j : ℕ} (hj : j < φ.length) :
    chosenLiteral φ σ j ∈ φ[j] ∧ σ (chosenLiteral φ σ j).1 = (chosenLiteral φ σ j).2 := by
  have hc := (CNF.eval_eq_true_iff _ _).1 hσ φ[j] (List.getElem_mem hj)
  rw [Clause.eval_eq_true_iff] at hc
  have hfind : (φ[j].find? (Literal.eval σ)).isSome := by
    rw [Option.isSome_iff_ne_none, Ne, List.find?_eq_none]
    obtain ⟨l, hl, hσl⟩ := hc
    exact fun h => h l hl (by simp [Literal.eval, hσl])
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hfind
  have hget : chosenLiteral φ σ j = l := by
    simp [chosenLiteral, List.getD_eq_getElem?_getD, hj, hl]
  rw [hget]
  refine ⟨List.mem_of_find?_eq_some hl, ?_⟩
  simpa [Literal.eval] using List.find?_some hl

private theorem assignedDiamond_lt (hσ : φ.eval σ = true) {j : ℕ} (hj : j < φ.length) :
    assignedDiamond φ σ j < φ.vars.length :=
  List.idxOf_lt_length_iff.2 (List.mem_map.2
    ⟨_, List.mem_flatten.2 ⟨_, List.getElem_mem hj, (chosenLiteral_spec hσ hj).1⟩, rfl⟩)

/-- The diamond assigned to a clause is traversed in the direction of the chosen literal. -/
private theorem direction_assigned (hσ : φ.eval σ = true) {j : ℕ} (hj : j < φ.length) :
    σ (φ.vars.getD (assignedDiamond φ σ j) 0) = (chosenLiteral φ σ j).2 := by
  have hlt := assignedDiamond_lt hσ hj
  unfold assignedDiamond at hlt ⊢
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
    List.getElem_idxOf hlt]
  exact (chosenLiteral_spec hσ hj).2

private theorem arc_of_mem_diamondArcs {i : ℕ} (hi : i < φ.vars.length) {e : ℕ × ℕ}
    (he : e ∈ diamondArcs φ i) : e ∈ diamondGraphArcs φ :=
  List.mem_append_left _ (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, he⟩)

private theorem arc_of_mem_literalArcs {j : ℕ} (hj : j < φ.length) {l : Literal ℕ}
    (hl : l ∈ φ[j]) {e : ℕ × ℕ} (he : e ∈ literalArcs φ j l) : e ∈ diamondGraphArcs φ :=
  List.mem_append_right _ (List.mem_flatMap.2 ⟨(φ[j], j),
    List.mem_zipIdx_iff_getElem?.2 (by simp [hj]), List.mem_flatMap.2 ⟨l, hl, he⟩⟩)

private theorem arc_row_succ {i a : ℕ} (hi : i < φ.vars.length) (ha : a + 1 < rowLength φ) :
    (rowNode i a, rowNode i (a + 1)) ∈ diamondGraphArcs φ :=
  arc_of_mem_diamondArcs hi (List.mem_append_right _
    (List.mem_flatMap.2 ⟨a, List.mem_range.2 (by omega), by simp⟩))

private theorem arc_row_pred {i a : ℕ} (hi : i < φ.vars.length) (ha : a + 1 < rowLength φ) :
    (rowNode i (a + 1), rowNode i a) ∈ diamondGraphArcs φ :=
  arc_of_mem_diamondArcs hi (List.mem_append_right _
    (List.mem_flatMap.2 ⟨a, List.mem_range.2 (by omega), by simp⟩))

/-- The detour arcs of an assigned clause exist in the direction of its diamond. -/
private theorem arc_detour (hσ : φ.eval σ = true) {j : ℕ} (hj : j < φ.length) :
    let i := assignedDiamond φ σ j
    (σ (φ.vars.getD i 0) = true → (rowNode i (3 * j + 2), clauseNode j) ∈ diamondGraphArcs φ ∧
      (clauseNode j, rowNode i (3 * j + 3)) ∈ diamondGraphArcs φ) ∧
    (σ (φ.vars.getD i 0) = false → (rowNode i (3 * j + 3), clauseNode j) ∈ diamondGraphArcs φ ∧
      (clauseNode j, rowNode i (3 * j + 2)) ∈ diamondGraphArcs φ) := by
  intro i
  have hmem := (chosenLiteral_spec hσ hj).1
  have hdir := direction_assigned hσ hj
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hb : (chosenLiteral φ σ j).2 = true := hdir ▸ h
    exact ⟨arc_of_mem_literalArcs hj hmem (by simp [literalArcs, hb, i, assignedDiamond]),
      arc_of_mem_literalArcs hj hmem (by simp [literalArcs, hb, i, assignedDiamond])⟩
  · have hb : (chosenLiteral φ σ j).2 = false := hdir ▸ h
    exact ⟨arc_of_mem_literalArcs hj hmem (by simp [literalArcs, hb, i, assignedDiamond]),
      arc_of_mem_literalArcs hj hmem (by simp [literalArcs, hb, i, assignedDiamond])⟩

private theorem rightStep_ne_nil (i a : ℕ) : rightStep φ σ i a ≠ [] := List.cons_ne_nil _ _

private theorem leftStep_ne_nil (i a : ℕ) : leftStep φ σ i a ≠ [] := List.cons_ne_nil _ _

private theorem rowLength_pos (φ : CNF ℕ) : 0 < rowLength φ := by
  simp only [rowLength]
  omega

/-- The traversal of a row, its first and last node, and its arcs. -/
private theorem rowPath_spec (hσ : φ.eval σ = true) {i : ℕ} (hi : i < φ.vars.length) :
    (rowPath φ σ i).IsChain (fun u v => (u, v) ∈ diamondGraphArcs φ) ∧
    (∀ x ∈ (rowPath φ σ i).head?, (topNode i, x) ∈ diamondGraphArcs φ) ∧
    (∀ x ∈ (rowPath φ σ i).getLast?, (x, topNode (i + 1)) ∈ diamondGraphArcs φ) ∧
    rowPath φ σ i ≠ [] := by
  have hm := rowLength_sub_one φ
  have hpos := rowLength_pos φ
  have hdiam : ∀ e ∈ diamondArcs φ i, e ∈ diamondGraphArcs φ := fun e he =>
    arc_of_mem_diamondArcs hi he
  unfold rowPath
  split_ifs with hd
  · refine ⟨isChain_flatMap_range (fun a _ => rightStep_ne_nil i a) (fun a ha => ?_)
      (fun a ha => ?_), ?_, ?_, ?_⟩
    · unfold rightStep
      split_ifs with h
      · obtain ⟨h₁, h₂, h₃⟩ := h
        have := ((arc_detour hσ h₂).1 (h₃ ▸ hd)).1
        rw [h₃, show 3 * (a / 3) + 2 = a by omega] at this
        exact List.IsChain.cons_cons this (List.IsChain.singleton _)
      · exact List.IsChain.singleton _
    · intro x hx y hy
      simp only [rightStep, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      unfold rightStep at hx
      split_ifs at hx with h
      · obtain ⟨h₁, h₂, h₃⟩ := h
        simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_def,
          Option.some.injEq] at hx
        subst hx
        have := ((arc_detour hσ h₂).1 (h₃ ▸ hd)).2
        rwa [h₃, show 3 * (a / 3) + 3 = a + 1 by omega] at this
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
      rw [ite_eq_right (by omega)] at hx
      simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
      subst hx
      exact hdiam _ (by simp [diamondArcs])
    · simpa using ⟨0, hpos, rightStep_ne_nil i 0⟩
  · have hd' : σ (φ.vars.getD i 0) = false := by simpa using hd
    refine ⟨isChain_flatMap_range_reverse (fun a _ => leftStep_ne_nil i a) (fun a ha => ?_)
      (fun a ha => ?_), ?_, ?_, ?_⟩
    · unfold leftStep
      split_ifs with h
      · obtain ⟨h₁, h₂, h₃, h₄⟩ := h
        have := ((arc_detour hσ h₃).2 (h₄ ▸ hd')).1
        rw [h₄, show 3 * (a / 3 - 1) + 3 = a by omega] at this
        exact List.IsChain.cons_cons this (List.IsChain.singleton _)
      · exact List.IsChain.singleton _
    · intro x hx y hy
      simp only [leftStep, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      unfold leftStep at hx
      split_ifs at hx with h
      · obtain ⟨h₁, h₂, h₃, h₄⟩ := h
        simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_def,
          Option.some.injEq] at hx
        subst hx
        have := ((arc_detour hσ h₃).2 (h₄ ▸ hd')).2
        rwa [h₄, show 3 * ((a + 1) / 3 - 1) + 2 = a by omega] at this
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
      unfold leftStep at hx
      rw [ite_eq_right (by omega)] at hx
      simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
      subst hx
      exact hdiam _ (by simp [diamondArcs])
    · simpa using ⟨0, hpos, leftStep_ne_nil i 0⟩

private theorem mem_rightStep {i a x : ℕ} : x ∈ rightStep φ σ i a ↔ x = rowNode i a ∨
    ((a % 3 = 2 ∧ a / 3 < φ.length ∧ assignedDiamond φ σ (a / 3) = i) ∧
      x = clauseNode (a / 3)) := by
  unfold rightStep
  split_ifs with h <;> simp [h]

private theorem mem_leftStep {i a x : ℕ} : x ∈ leftStep φ σ i a ↔ x = rowNode i a ∨
    ((a % 3 = 0 ∧ 0 < a ∧ a / 3 - 1 < φ.length ∧ assignedDiamond φ σ (a / 3 - 1) = i) ∧
      x = clauseNode (a / 3 - 1)) := by
  unfold leftStep
  split_ifs with h <;> simp [h]

/-- The traversal of row `i` visits its row nodes and the nodes of the clauses assigned to it. -/
private theorem mem_rowPath {i v : ℕ} :
    v ∈ rowPath φ σ i ↔ (∃ a < rowLength φ, v = rowNode i a) ∨
      (∃ j < φ.length, assignedDiamond φ σ j = i ∧ v = clauseNode j) := by
  have hm := rowLength_sub_one φ
  unfold rowPath
  split_ifs
  · simp only [List.mem_flatMap, List.mem_range, mem_rightStep]
    constructor
    · rintro ⟨a, ha, rfl | ⟨⟨-, h₂, h₃⟩, rfl⟩⟩
      · exact Or.inl ⟨a, ha, rfl⟩
      · exact Or.inr ⟨a / 3, h₂, h₃, rfl⟩
    · rintro (⟨a, ha, rfl⟩ | ⟨j, hj, hji, rfl⟩)
      · exact ⟨a, ha, Or.inl rfl⟩
      · have hj' : (3 * j + 2) / 3 = j := by omega
        exact ⟨3 * j + 2, by omega, Or.inr ⟨⟨by omega, by rw [hj']; exact hj,
          by rw [hj']; exact hji⟩, by rw [hj']⟩⟩
  · simp only [List.mem_flatMap, List.mem_reverse, List.mem_range, mem_leftStep]
    constructor
    · rintro ⟨a, ha, rfl | ⟨⟨-, -, h₃, h₄⟩, rfl⟩⟩
      · exact Or.inl ⟨a, ha, rfl⟩
      · exact Or.inr ⟨a / 3 - 1, h₃, h₄, rfl⟩
    · rintro (⟨a, ha, rfl⟩ | ⟨j, hj, hji, rfl⟩)
      · exact ⟨a, ha, Or.inl rfl⟩
      · have hj' : (3 * j + 3) / 3 - 1 = j := by omega
        exact ⟨3 * j + 3, by omega, Or.inr ⟨⟨by omega, by omega, by rw [hj']; exact hj,
          by rw [hj']; exact hji⟩, by rw [hj']⟩⟩

private theorem nodup_rowPath (i : ℕ) : (rowPath φ σ i).Nodup := by
  unfold rowPath
  split_ifs
  · rw [List.nodup_flatMap]
    refine ⟨fun a _ => ?_, List.nodup_range.pairwise_of_forall_ne fun a _ b _ hab => ?_⟩
    · unfold rightStep
      split_ifs <;> simp
    · intro x hx hx'
      rw [mem_rightStep] at hx hx'
      rcases hx with rfl | ⟨h, rfl⟩ <;> rcases hx' with h' | ⟨h', h''⟩
      · simp only [rowNode_inj] at h'
        omega
      · simp at h''
      · simp at h'
      · simp only [clauseNode_inj] at h''
        omega
  · rw [List.nodup_flatMap]
    refine ⟨fun a _ => ?_,
      (List.nodup_reverse.2 List.nodup_range).pairwise_of_forall_ne fun a _ b _ hab => ?_⟩
    · unfold leftStep
      split_ifs <;> simp
    · intro x hx hx'
      rw [mem_leftStep] at hx hx'
      rcases hx with rfl | ⟨h, rfl⟩ <;> rcases hx' with h' | ⟨h', h''⟩
      · simp only [rowNode_inj] at h'
        omega
      · simp at h''
      · simp at h'
      · simp only [clauseNode_inj] at h''
        omega

/-- The Hamiltonian path read off a satisfying assignment. -/
private theorem isDirHamPath_hamPath (hσ : φ.eval σ = true) :
    (toDirHamPath φ).1.IsDirHamPath (topNode 0) (topNode φ.vars.length) (hamPath φ σ) := by
  have hblock_ne : ∀ i, topNode i :: rowPath φ σ i ≠ [] := fun _ => List.cons_ne_nil _ _
  have hmem_block : ∀ {i v}, v ∈ topNode i :: rowPath φ σ i ↔ v = topNode i ∨
      (∃ a < rowLength φ, v = rowNode i a) ∨
      (∃ j < φ.length, assignedDiamond φ σ j = i ∧ v = clauseNode j) := by
    intro i v
    rw [List.mem_cons, mem_rowPath]
  refine ⟨?_, fun v => ?_, ?_, ?_, ?_⟩
  · -- No repetitions.
    rw [hamPath, List.nodup_append, List.nodup_flatMap]
    refine ⟨⟨fun i _ => List.nodup_cons.2 ⟨fun h => ?_, nodup_rowPath i⟩,
      List.nodup_range.pairwise_of_forall_ne fun i _ i' _ hii' => ?_⟩,
      List.nodup_singleton _, fun v hv w hw => ?_⟩
    · rcases mem_rowPath.1 h with ⟨a, -, h⟩ | ⟨j, -, -, h⟩ <;> simp at h
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
    change v ∈ hamPath φ σ ↔ v ∈ diamondGraphVertices φ
    rw [mem_diamondGraphVertices, hamPath, List.mem_append, List.mem_flatMap,
      List.mem_singleton]
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
      · exact Or.inl ⟨_, List.mem_range.2 (assignedDiamond_lt hσ hj),
          hmem_block.2 (Or.inr (Or.inr ⟨j, hj, rfl, rfl⟩))⟩
  · -- It starts at the top of the first diamond.
    rw [hamPath]
    rcases Nat.eq_zero_or_pos φ.vars.length with h | h
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
    · obtain ⟨hch, hhead, -, -⟩ := rowPath_spec hσ hi
      exact List.isChain_cons.2 ⟨hhead, hch⟩
    · intro x hx y hy
      obtain ⟨-, -, hlast, hne⟩ := rowPath_spec hσ (i := i) (by omega)
      rw [← List.singleton_append, List.getLast?_append_of_ne_nil _ hne] at hx
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact hlast x hx
    · intro x hx y hy
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      rcases Nat.eq_zero_or_pos φ.vars.length with h | h
      · simp [h] at hx
      · obtain ⟨-, -, hlast, hne⟩ := rowPath_spec hσ (i := φ.vars.length - 1) (by omega)
        rw [getLast?_flatMap_range h (hblock_ne _), ← List.singleton_append,
          List.getLast?_append_of_ne_nil _ hne] at hx
        have := hlast x hx
        rwa [Nat.sub_add_cancel h] at this

end AssignmentToPath

/-- **Correctness of the diamond construction.** A formula is satisfiable exactly when its
diamond graph has a Hamiltonian path from the top of the first diamond to the bottom of the last.
-/
theorem toDirHamPath_mem_iff (φ : CNF ℕ) : toDirHamPath φ ∈ DirHamPath ↔ φ ∈ SAT :=
  ⟨mem_SAT_of_toDirHamPath_mem, fun ⟨σ, hσ⟩ => ⟨hamPath φ σ, isDirHamPath_hamPath hσ⟩⟩

end SAT

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

namespace SAT

/-! ### Polynomial-time reductions -/

/-- The diamond graph is computable in polynomial time: node labels are computed in unary from
diamond, row, clause and first-occurrence indices, then converted to binary. -/
@[fun_prop]
theorem computableTidilyInPolyTime_toDirHamPath :
    ComputableTidilyInPolyTime toDirHamPath encCNF (encPair encGraph (encPair encNat encNat)) := by
  have htop : ComputableTidilyInPolyTime (fun i => topNode i) encUnary encNat :=
    unary_to_binary.comp (show ComputableTidilyInPolyTime (fun i => Nat.pair 0 i) _ _ by
      fun_prop)
  have hrow : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => rowNode p.1 p.2)
      (encPair encUnary encUnary) encNat :=
    unary_to_binary.comp (show ComputableTidilyInPolyTime
      (fun p : ℕ × ℕ => Nat.pair 1 (Nat.pair p.1 p.2)) _ _ by fun_prop)
  have hclause : ComputableTidilyInPolyTime (fun j => clauseNode j) encUnary encNat :=
    unary_to_binary.comp (show ComputableTidilyInPolyTime (fun j => Nat.pair 2 j) _ _ by
      fun_prop)
  have hlen : ComputableTidilyInPolyTime rowLength encCNF encUnary := by
    unfold rowLength
    fun_prop
  unfold toDirHamPath diamondGraphVertices diamondGraphArcs diamondArcs literalArcs encGraph
  fun_prop

/-- The reduction from `SAT` to `DirHamCycle`: the diamond graph of `φ` with an arc from the
bottom of the last diamond back to the top of the first. -/
def toDirHamCycle (φ : CNF ℕ) : Graph :=
  (diamondGraphVertices φ, (topNode φ.vars.length, topNode 0) :: diamondGraphArcs φ)

/-- **Correctness of the cycle construction.** A formula is satisfiable exactly when its closed
diamond graph has a Hamiltonian cycle. -/
theorem toDirHamCycle_mem_iff (φ : CNF ℕ) : toDirHamCycle φ ∈ DirHamCycle ↔ φ ∈ SAT := by
  rw [← toDirHamPath_mem_iff]
  refine Graph.mem_DirHamCycle_cons_iff (G := (diamondGraphVertices φ, diamondGraphArcs φ))
    (s := topNode 0) (t := topNode φ.vars.length)
    (mem_diamondGraphVertices.2 (Or.inl ⟨0, Nat.zero_le _, rfl⟩)) fun u hu => ?_
  rcases mem_diamondGraphArcs.1 hu with
      ⟨i, -, ⟨-, h₂ | h₂⟩ | ⟨-, h₂⟩ | ⟨a, -, ⟨-, h₂⟩ | ⟨-, h₂⟩⟩⟩ |
      ⟨j, -, l, -, ⟨-, ⟨-, h₂⟩ | ⟨-, h₂⟩⟩ | ⟨-, ⟨-, h₂⟩ | ⟨-, h₂⟩⟩⟩ <;> simp at h₂

/-- The closed diamond graph is computable in polynomial time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_toDirHamCycle :
    ComputableTidilyInPolyTime toDirHamCycle encCNF encGraph := by
  have hclose : ComputableTidilyInPolyTime (fun x : Graph × ℕ × ℕ => (x.1.1, (x.2.2, x.2.1) ::
      x.1.2)) (encPair encGraph (encPair encNat encNat)) encGraph := by
    unfold encGraph
    fun_prop
  exact hclose.comp computableTidilyInPolyTime_toDirHamPath

end SAT

/-- `SAT` reduces to `DirHamPath` in polynomial time via `SAT.toDirHamPath`. -/
theorem polyTimeReducible_SAT_DirHamPath :
    PolyTimeReducible encCNF (encPair encGraph (encPair encNat encNat)) SAT DirHamPath :=
  ⟨SAT.toDirHamPath, SAT.computableTidilyInPolyTime_toDirHamPath,
    fun φ => (SAT.toDirHamPath_mem_iff φ).symm⟩

/-- `ThreeSAT` reduces to `DirHamPath` in polynomial time: a formula with a clause of more than
three literals is mapped to the diamond graph of the empty clause, which has no Hamiltonian
path. -/
theorem polyTimeReducible_ThreeSAT_DirHamPath :
    PolyTimeReducible encCNF (encPair encGraph (encPair encNat encNat)) ThreeSAT DirHamPath := by
  refine ⟨fun φ => if φ.all (fun c => decide (c.length ≤ 3)) then SAT.toDirHamPath φ
    else SAT.toDirHamPath [[]], by fun_prop, fun φ => ?_⟩
  simp only [ThreeSAT, Set.mem_ofPred_eq]
  split_ifs with h
  · rw [SAT.toDirHamPath_mem_iff, mem_SAT]
    simp only [List.all_eq_true, decide_eq_true_eq] at h
    exact ⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩
  · rw [SAT.toDirHamPath_mem_iff, mem_SAT]
    simp only [List.all_eq_true, decide_eq_true_eq] at h
    refine ⟨fun h' => (h h'.1).elim, fun ⟨σ, hσ⟩ => ?_⟩
    simp at hσ

/-- `DirHamPath` is `NP`-hard. -/
theorem DirHamPath_npHard : NPHard (encPair encGraph (encPair encNat encNat)) DirHamPath :=
  CookLevin.SAT_npHard.trans polyTimeReducible_SAT_DirHamPath

/-- `SAT` reduces to `DirHamCycle` in polynomial time via `SAT.toDirHamCycle`. -/
theorem polyTimeReducible_SAT_DirHamCycle : PolyTimeReducible encCNF encGraph SAT DirHamCycle :=
  ⟨SAT.toDirHamCycle, SAT.computableTidilyInPolyTime_toDirHamCycle,
    fun φ => (SAT.toDirHamCycle_mem_iff φ).symm⟩

/-- `DirHamCycle` is `NP`-hard. -/
theorem DirHamCycle_npHard : NPHard encGraph DirHamCycle :=
  CookLevin.SAT_npHard.trans polyTimeReducible_SAT_DirHamCycle

/-- **`DirHamPath` is NP-complete.** -/
theorem DirHamPath_npComplete :
    NPComplete (encPair encGraph (encPair encNat encNat)) DirHamPath :=
  ⟨DirHamPath.mem_NP, DirHamPath_npHard⟩

/-- **`DirHamCycle` is NP-complete.** -/
theorem DirHamCycle_npComplete : NPComplete encGraph DirHamCycle :=
  ⟨DirHamCycle.mem_NP, DirHamCycle_npHard⟩

end Cslib.Complexity
