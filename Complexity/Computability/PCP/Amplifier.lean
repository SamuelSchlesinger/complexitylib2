/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.ConstraintGraph
public import Mathlib.Data.Nat.Log
import Complexity.Foundations.Data.Nat.Log

/-!
# Gap amplifiers and their iteration

Dinur's proof of the PCP theorem [Dinur, Section 4][Dinur2007] iterates a single transformation of
constraint graphs over a fixed alphabet that keeps satisfiable graphs satisfiable, at least doubles
the value of unsatisfiable ones until it reaches a universal threshold `γ`, and multiplies the size
by at most a universal constant. This file packages those properties as an `Amplifier` and derives
the consequence that drives the proof [Dinur, Corollary 4.2][Dinur2007]: after `k` rounds the value
of an unsatisfiable graph is at least `min (2 ^ k UNSAT(G)) γ`, so after `⌈log₂ |E|⌉` rounds it is
at least `γ`, since it was at least `1 / |E|` to begin with, while the size has grown by a factor
polynomial in `|E|` only.

A round changes the types of the vertices and edges: the vertices of Dinur's round are built from
the edges of its input. Its input and output are therefore **bundled** constraint graphs
(`FinConstraintGraph`), which carry their finite types of vertices and edges along. The other
option, numbering the vertices and edges in `Fin n` after every round, would need a reindexing at
every round and gain nothing: the constructions name their vertices and edges by tuples of the old
ones, and the statements only count them.

As a mere function, an amplifier is easy to come by: a function that decides satisfiability can
map the satisfiable constraint graphs to one without edges and the others to a single violated
edge. The interest of an amplifier lies in its construction: Dinur's round
(`Cslib.PCP.Dinur.amplifier`) transforms a constraint graph locally, and can be carried out in
polynomial time given explicit expanders [Dinur, Theorem 4.1][Dinur2007]. This file is only about
the consequences of the interface; running times are not formalized here.

## Main definitions

* `Cslib.PCP.FinConstraintGraph`: a constraint graph bundled with its finite types of vertices and
  edges.
* `Cslib.PCP.Amplifier`: a gap amplifier.
* `Cslib.PCP.Amplifier.iter`: its `k`-fold iterate.

## Main results

* `Cslib.PCP.Amplifier.satisfiable_iter_iff`: the iterates preserve satisfiability.
* `Cslib.PCP.Amplifier.min_le_unsatVal_iter`: the value after `k` rounds is at least
  `min (2 ^ k UNSAT(G)) γ`.
* `Cslib.PCP.Amplifier.gap_le_unsatVal_iter`,
  `Cslib.PCP.Amplifier.unsatVal_iter_eq_zero_or_gap_le`: after `k` rounds with `|E| ≤ 2 ^ k`, the
  value is either zero or at least `γ`.
* `Cslib.PCP.Amplifier.card_edges_iter_le`, `Cslib.PCP.Amplifier.card_vertices_iter_le`: the size
  after `k` rounds.
* `Cslib.PCP.Amplifier.card_edges_iter_clog_le`, `Cslib.PCP.Amplifier.card_vertices_iter_clog_le`:
  after `⌈log₂ |E|⌉` rounds, the size is polynomial in `|E|`.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

universe u v

namespace Cslib.PCP

/-- A **finite constraint graph** over the alphabet `α`: a constraint graph bundled with its finite
types of vertices and edges, so that transformations changing these types can be iterated. -/
structure FinConstraintGraph (α : Type v) where
  /-- The vertices. -/
  V : Type u
  /-- The edges. -/
  E : Type u
  /-- There are finitely many vertices. -/
  [fintypeV : Fintype V]
  /-- There are finitely many edges. -/
  [fintypeE : Fintype E]
  /-- The constraint graph. -/
  graph : ConstraintGraph V E α

attribute [instance] FinConstraintGraph.fintypeV FinConstraintGraph.fintypeE

/-- A **gap amplifier** over the alphabet `α` [Dinur, Theorem 4.1][Dinur2007]: a transformation of
finite constraint graphs over `α` that preserves satisfiability, at least doubles the value up to a
positive threshold `gap`, and multiplies the size by at most `factor`. The size is measured by the
edges of the input alone, which the numbers of vertices and of edges of the output may not exceed
`factor` times: the vertices that no edge touches play no role. -/
structure Amplifier (α : Type v) where
  /-- The transformation. -/
  toFun : FinConstraintGraph.{u} α → FinConstraintGraph.{u} α
  /-- The factor by which the size may grow. -/
  factor : ℕ
  /-- The threshold up to which the value doubles. -/
  gap : ℝ
  /-- The threshold is positive. -/
  gap_pos : 0 < gap
  /-- The threshold is at most one, as every value is. -/
  gap_le_one : gap ≤ 1
  /-- The output has at most `factor` vertices per edge of the input. -/
  card_vertices_le (G : FinConstraintGraph.{u} α) :
    Fintype.card (toFun G).V ≤ factor * Fintype.card G.E
  /-- The output has at most `factor` edges per edge of the input. -/
  card_edges_le (G : FinConstraintGraph.{u} α) :
    Fintype.card (toFun G).E ≤ factor * Fintype.card G.E
  /-- The transformation preserves satisfiability. -/
  satisfiable_iff (G : FinConstraintGraph.{u} α) :
    (toFun G).graph.Satisfiable ↔ G.graph.Satisfiable
  /-- The transformation at least doubles the value, up to the threshold. -/
  min_le_unsatVal (G : FinConstraintGraph.{u} α) :
    min (2 * G.graph.unsatVal) gap ≤ (toFun G).graph.unsatVal

namespace Amplifier

variable {α : Type v} (A : Amplifier.{u} α)

/-- The `k`-fold iterate of an amplifier. -/
def iter (k : ℕ) : FinConstraintGraph.{u} α → FinConstraintGraph.{u} α :=
  A.toFun^[k]

/-- Zero rounds leave a constraint graph unchanged. -/
@[simp]
theorem iter_zero (G : FinConstraintGraph.{u} α) : A.iter 0 G = G :=
  rfl

/-- The `k + 1`-st iterate is one more round after the `k`-th. -/
theorem iter_succ (k : ℕ) (G : FinConstraintGraph.{u} α) :
    A.iter (k + 1) G = A.toFun (A.iter k G) :=
  Function.iterate_succ_apply' _ _ _

/-! ### Satisfiability and value -/

/-- **The iterates of an amplifier preserve satisfiability.** -/
theorem satisfiable_iter_iff (k : ℕ) (G : FinConstraintGraph.{u} α) :
    (A.iter k G).graph.Satisfiable ↔ G.graph.Satisfiable := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iter_succ, A.satisfiable_iff, ih]

/-- **The value after `k` rounds** [Dinur, Corollary 4.2][Dinur2007]: it is at least
`min (2 ^ k UNSAT(G)) γ`. -/
theorem min_le_unsatVal_iter (k : ℕ) (G : FinConstraintGraph.{u} α) :
    min (2 ^ k * G.graph.unsatVal) A.gap ≤ (A.iter k G).graph.unsatVal := by
  induction k with
  | zero =>
    rw [pow_zero, one_mul]
    exact min_le_left _ _
  | succ k ih =>
    rw [iter_succ]
    refine le_trans ?_ (A.min_le_unsatVal _)
    have hγ := A.gap_pos.le
    calc min (2 ^ (k + 1) * G.graph.unsatVal) A.gap
        ≤ min (2 * min (2 ^ k * G.graph.unsatVal) A.gap) A.gap := by
          refine le_min ?_ (min_le_right _ _)
          rw [mul_min_of_nonneg _ _ zero_le_two]
          exact min_le_min (le_of_eq (by ring)) (by linarith)
        _ ≤ min (2 * (A.iter k G).graph.unsatVal) A.gap := by
          gcongr

section Gap

variable [Nonempty α]

/-- **After enough rounds, an unsatisfiable graph has value at least `γ`** [Dinur, Corollary
4.2][Dinur2007]: `k` rounds suffice when `|E| ≤ 2 ^ k`, since the value of an unsatisfiable graph
is at least `1 / |E|`. -/
theorem gap_le_unsatVal_iter {G : FinConstraintGraph.{u} α} (h : ¬ G.graph.Satisfiable) {k : ℕ}
    (hk : Fintype.card G.E ≤ 2 ^ k) : A.gap ≤ (A.iter k G).graph.unsatVal := by
  refine le_trans (le_min ?_ le_rfl) (A.min_le_unsatVal_iter k G)
  have hE : (0 : ℝ) < Fintype.card G.E := by
    refine Nat.cast_pos.2 (Fintype.card_pos_iff.2 ?_)
    by_contra hE
    exact h ⟨fun _ ↦ Classical.arbitrary α, fun e ↦ (not_nonempty_iff.1 hE).elim e⟩
  have hk' : (Fintype.card G.E : ℝ) ≤ 2 ^ k := by exact_mod_cast hk
  calc A.gap ≤ 1 := A.gap_le_one
    _ = Fintype.card G.E * (Fintype.card G.E : ℝ)⁻¹ := (mul_inv_cancel₀ hE.ne').symm
    _ ≤ 2 ^ k * G.graph.unsatVal := by
        gcongr
        exact G.graph.inv_card_le_unsatVal h

/-- **The dichotomy** [Dinur, Corollary 4.2][Dinur2007]: after `k` rounds with `|E| ≤ 2 ^ k`, the
value is either zero, when the graph was satisfiable, or at least `γ`. -/
theorem unsatVal_iter_eq_zero_or_gap_le (G : FinConstraintGraph.{u} α) {k : ℕ}
    (hk : Fintype.card G.E ≤ 2 ^ k) :
    (A.iter k G).graph.unsatVal = 0 ∨ A.gap ≤ (A.iter k G).graph.unsatVal := by
  by_cases h : G.graph.Satisfiable
  · exact .inl ((ConstraintGraph.unsatVal_eq_zero_iff _).2 ((A.satisfiable_iter_iff k G).2 h))
  · exact .inr (A.gap_le_unsatVal_iter h hk)

end Gap

/-! ### Size -/

/-- After `k` rounds, the number of edges has grown by a factor at most `factor ^ k`. -/
theorem card_edges_iter_le (k : ℕ) (G : FinConstraintGraph.{u} α) :
    Fintype.card (A.iter k G).E ≤ A.factor ^ k * Fintype.card G.E := by
  induction k with
  | zero => exact (one_mul _).ge
  | succ k ih =>
    rw [iter_succ, pow_succ', mul_assoc]
    exact (A.card_edges_le _).trans (Nat.mul_le_mul_left _ ih)

/-- After `k` rounds, there are at most `factor ^ k` vertices per edge of the original graph, or
the original vertices if there was no round. -/
theorem card_vertices_iter_le (k : ℕ) (G : FinConstraintGraph.{u} α) :
    Fintype.card (A.iter k G).V ≤ max (Fintype.card G.V) (A.factor ^ k * Fintype.card G.E) := by
  cases k with
  | zero => exact le_max_left _ _
  | succ k =>
    rw [iter_succ, pow_succ', mul_assoc]
    exact le_max_of_le_right
      ((A.card_vertices_le _).trans (Nat.mul_le_mul_left _ (A.card_edges_iter_le k G)))

/-- **After `⌈log₂ |E|⌉` rounds, the number of edges is polynomial**: at most
`2 ^ f |E| ^ (f + 1)`, where `f = ⌈log₂ factor⌉`. -/
theorem card_edges_iter_clog_le (G : FinConstraintGraph.{u} α) :
    Fintype.card (A.iter (Nat.clog 2 (Fintype.card G.E)) G).E ≤
      2 ^ Nat.clog 2 A.factor * Fintype.card G.E ^ (Nat.clog 2 A.factor + 1) := by
  refine (A.card_edges_iter_le _ G).trans ?_
  rcases Nat.eq_zero_or_pos (Fintype.card G.E) with h | h
  · simp [h]
  · rw [pow_succ, ← mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.pow_clog_le_pow_clog_mul_pow_clog one_lt_two _ h)

/-- **After `⌈log₂ |E|⌉` rounds, the number of vertices is polynomial**: at most
`2 ^ f |E| ^ (f + 1)`, where `f = ⌈log₂ factor⌉`, or the original number of vertices if there
was no round. -/
theorem card_vertices_iter_clog_le (G : FinConstraintGraph.{u} α) :
    Fintype.card (A.iter (Nat.clog 2 (Fintype.card G.E)) G).V ≤
      max (Fintype.card G.V)
        (2 ^ Nat.clog 2 A.factor * Fintype.card G.E ^ (Nat.clog 2 A.factor + 1)) := by
  refine (A.card_vertices_iter_le _ G).trans (max_le_max le_rfl ?_)
  rcases Nat.eq_zero_or_pos (Fintype.card G.E) with h | h
  · simp [h]
  · rw [pow_succ, ← mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.pow_clog_le_pow_clog_mul_pow_clog one_lt_two _ h)

end Amplifier

end Cslib.PCP
