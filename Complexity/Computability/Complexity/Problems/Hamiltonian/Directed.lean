/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Hamiltonian.Diamond
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
a true literal. Diamonds of repeated occurrences of a variable carry no detours and can be
traversed either way. This argument is carried out for diamond graphs with any layout of the rows
(`Cslib.Complexity.Diamond.mem_DirHamPath_iff`); the graph here has a slot for each clause in every
row (`SAT.toDirHamPath_eq`). Clauses of every width, including the empty clause, are handled, so
the reduction is from `SAT`; it also reduces `ThreeSAT` after rejecting clauses with more than
three literals.

`Graph.mem_DirHamCycle_cons_iff` closes Hamiltonian paths into cycles with an arc back to a start
vertex that no arc enters. The top of the first diamond is such a vertex, which gives
`SAT.toDirHamCycle`.

## Main definitions

* `Cslib.Complexity.SAT.toDirHamPath`, `Cslib.Complexity.SAT.toDirHamCycle`, with the node labels
  `Cslib.Complexity.SAT.topNode`, `Cslib.Complexity.SAT.rowNode` and
  `Cslib.Complexity.SAT.clauseNode`.

## Main results

* `Cslib.Complexity.SAT.toDirHamPath_eq`: the graph as a diamond graph.
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

/-! ### Correctness -/

/-- The detours of the diamond graph: the literal `l` of clause `j` goes through the node of
clause `j` across slot `j` of the row of the first occurrence of its variable, left to right when
`l` is positive. -/
def diamondDetours (φ : CNF ℕ) : List Diamond.Detour :=
  φ.zipIdx.flatMap fun c => c.1.map fun l => (c.2, φ.vars.idxOf l.1, c.2, l.2)

/-- The diamond graph of `φ` is the diamond graph (`Cslib.Complexity.Diamond.graph`) with a
diamond for each variable occurrence and a slot for each clause in every row. -/
theorem toDirHamPath_eq (φ : CNF ℕ) : toDirHamPath φ =
    (Diamond.graph φ.vars.length (fun _ => φ.length) φ.length (diamondDetours φ),
      Diamond.topNode 0, Diamond.topNode φ.vars.length) := by
  simp only [toDirHamPath, Diamond.graph, diamondGraphArcs, Diamond.arcs, diamondDetours,
    List.flatMap_assoc, List.flatMap_map]
  rfl

private theorem fst_mem_vars {φ : CNF ℕ} {j : ℕ} {l : Literal ℕ} (hj : j < φ.length)
    (hl : l ∈ φ[j]) : l.1 ∈ φ.vars :=
  List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨_, List.getElem_mem hj, hl⟩, rfl⟩

private theorem mem_diamondDetours {φ : CNF ℕ} {d : Diamond.Detour} :
    d ∈ diamondDetours φ ↔ ∃ (j : ℕ) (hj : j < φ.length), ∃ l ∈ φ[j],
      d = (j, φ.vars.idxOf l.1, j, l.2) := by
  simp only [diamondDetours, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨⟨c, j⟩, hc, l, hl, rfl⟩
    obtain ⟨hj, hcj⟩ := List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 hc)
    exact ⟨j, hj, l, by rw [hcj]; exact hl, rfl⟩
  · rintro ⟨j, hj, l, hl, rfl⟩
    exact ⟨(φ[j], j), List.mem_zipIdx_iff_getElem?.2 (by simp [hj]), l, hl, rfl⟩

/-- The diamond graph is well formed: the detours across slot `j` all belong to clause `j`. -/
theorem wellFormed_diamondDetours (φ : CNF ℕ) :
    Diamond.WellFormed φ.vars.length (fun _ => φ.length) φ.length (diamondDetours φ) where
  clause_lt d hd := by
    obtain ⟨j, hj, l, hl, rfl⟩ := mem_diamondDetours.1 hd
    exact hj
  row_lt d hd := by
    obtain ⟨j, hj, l, hl, rfl⟩ := mem_diamondDetours.1 hd
    exact List.idxOf_lt_length_iff.2 (fst_mem_vars hj hl)
  slot_lt d hd := by
    obtain ⟨j, hj, l, hl, rfl⟩ := mem_diamondDetours.1 hd
    exact hj
  clause_eq d hd d' hd' _ hslot := by
    obtain ⟨j, hj, l, hl, rfl⟩ := mem_diamondDetours.1 hd
    obtain ⟨j', hj', l', hl', rfl⟩ := mem_diamondDetours.1 hd'
    exact hslot

/-- Directions of the rows satisfying every clause are satisfying assignments. -/
theorem satisfiable_diamondDetours_iff (φ : CNF ℕ) :
    Diamond.Satisfiable φ.length (diamondDetours φ) ↔ φ ∈ SAT := by
  constructor
  · rintro ⟨dir, hdir⟩
    refine ⟨fun x => dir (φ.vars.idxOf x), (CNF.eval_eq_true_iff _ _).2 fun c hc => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
    obtain ⟨d, hd, hdj, hdd⟩ := hdir j hj
    obtain ⟨j', hj', l, hl, rfl⟩ := mem_diamondDetours.1 hd
    simp only at hdj hdd
    subst hdj
    exact (Clause.eval_eq_true_iff _ _).2 ⟨l, hl, hdd⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨fun i => σ (φ.vars.getD i 0), fun j hj => ?_⟩
    obtain ⟨l, hl, hσl⟩ := (Clause.eval_eq_true_iff _ _).1
      ((CNF.eval_eq_true_iff _ _).1 hσ φ[j] (List.getElem_mem hj))
    have hlt := List.idxOf_lt_length_iff.2 (fst_mem_vars hj hl)
    refine ⟨_, mem_diamondDetours.2 ⟨j, hj, l, hl, rfl⟩, rfl, ?_⟩
    simp only
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
      List.getElem_idxOf hlt]
    exact hσl

/-- **Correctness of the diamond construction.** A formula is satisfiable exactly when its
diamond graph has a Hamiltonian path from the top of the first diamond to the bottom of the last.
-/
theorem toDirHamPath_mem_iff (φ : CNF ℕ) : toDirHamPath φ ∈ DirHamPath ↔ φ ∈ SAT := by
  rw [toDirHamPath_eq]
  exact (Diamond.mem_DirHamPath_iff (wellFormed_diamondDetours φ)).trans
    (satisfiable_diamondDetours_iff φ)

/-- A Hamiltonian path of the diamond graph yields a satisfying assignment. -/
theorem mem_SAT_of_toDirHamPath_mem {φ : CNF ℕ} (h : toDirHamPath φ ∈ DirHamPath) :
    φ ∈ SAT :=
  (toDirHamPath_mem_iff φ).1 h

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
