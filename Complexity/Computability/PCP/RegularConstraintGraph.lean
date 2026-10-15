/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.ConstraintGraph
public import Complexity.Foundations.Combinatorics.Expander.Loops

/-!
# Constraint graphs on a regular multigraph

The steps of Dinur's proof after preprocessing [Dinur, Section 3][Dinur2007] run on constraint
graphs whose underlying multigraph is regular, since this is what makes random walks and the
spectral expansion `λ` available. A `RegularConstraintGraph V D α` is a `D`-regular multigraph on
`V`, presented by its rotation map (`Cslib.RotationMap`), together with a constraint on each of its
**darts** `(v, i)`, the `i`-th edge at `v` seen from `v`: a relation between the label of `v` and
that of its `i`-th neighbor. Its constraint graph (`toConstraintGraph`) has the darts as edges, so
its proportions of violated constraints are taken over the uniform distribution on darts, which is
the stationary distribution of the edges crossed by the random walk.

An undirected edge has two darts, and their constraints are not required to agree. Nothing is lost:
an undirected constraint is given by the same relation on both darts, read in the two directions,
and the estimates of the proof are stated over darts anyway.

Constraints that always hold may be added on the edges of a second regular multigraph on the same
vertices (`addTrivial`). The violated darts are then the same, and the proportion of violated darts
drops by the factor `|D| / (|D| + |D'|)` (`unsatVal_addTrivial`). Dinur adds the edges of an
expander in this way, to make the underlying multigraph an expander, and self-loops (`addLoops`),
which the powering step needs.

## Main definitions

* `Cslib.PCP.RegularConstraintGraph`: a rotation map with a constraint on each dart.
* `Cslib.PCP.RegularConstraintGraph.toConstraintGraph`: its constraint graph, whose edges are the
  darts.
* `Cslib.PCP.RegularConstraintGraph.addTrivial`: the edges of another regular multigraph added,
  with constraints that always hold.
* `Cslib.PCP.RegularConstraintGraph.addLoops`: self-loops added, with constraints that always hold.

## Main results

* `Cslib.PCP.RegularConstraintGraph.unsatVal_addTrivial`,
  `Cslib.PCP.RegularConstraintGraph.satisfiable_addTrivial_iff`: adding edges with constraints that
  always hold scales the value by `|D| / (|D| + |D'|)` and preserves satisfiability.
* `Cslib.PCP.RegularConstraintGraph.unsatVal_addLoops`,
  `Cslib.PCP.RegularConstraintGraph.satisfiable_addLoops_iff`: the same for self-loops.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP

open Finset

/-- A **regular constraint graph**: a `D`-regular multigraph on `V`, presented by its rotation map,
with a constraint over the alphabet `α` on each of its darts. The constraint `rel (v, i)` relates
the label of `v` to that of its `i`-th neighbor. -/
structure RegularConstraintGraph (V D α : Type*) where
  /-- The underlying regular multigraph. -/
  graph : RotationMap V D
  /-- The constraint on a dart `(v, i)`: a relation between the label of `v` and that of its
  `i`-th neighbor. -/
  rel : V × D → α → α → Prop

namespace RegularConstraintGraph

variable {V D D' α : Type*} (R : RegularConstraintGraph V D α)

/-- The constraint graph of a regular constraint graph: its edges are the darts, the dart `(v, i)`
going from `v` to its `i`-th neighbor. -/
def toConstraintGraph : ConstraintGraph V (V × D) α where
  src := Prod.fst
  dst p := R.graph.neighbor p.1 p.2
  rel := R.rel

variable {R} in
/-- A labelling satisfies a dart when the labels of its ends satisfy its constraint. -/
@[simp]
theorem satisfies_toConstraintGraph_iff {σ : V → α} {p : V × D} :
    R.toConstraintGraph.Satisfies σ p ↔ R.rel p (σ p.1) (σ (R.graph.neighbor p.1 p.2)) :=
  Iff.rfl

/-- The number of violated darts is the proportion of violated darts times the number `|V| |D|`
of darts. -/
theorem card_mul_card_mul_unsatFrac [Fintype V] [Fintype D] (σ : V → α) :
    Fintype.card V * Fintype.card D * R.toConstraintGraph.unsatFrac σ =
      #(R.toConstraintGraph.unsatEdges σ) := by
  rw [← Nat.cast_mul, ← Fintype.card_prod, ConstraintGraph.card_mul_unsatFrac]

section AddTrivial

/-- The regular constraint graph `R` with the edges of `H` added, carrying constraints that always
hold: its underlying multigraph is the union `R.graph.union H`. -/
def addTrivial (H : RotationMap V D') : RegularConstraintGraph V (D ⊕ D') α where
  graph := R.graph.union H
  rel p := p.2.elim (fun i ↦ R.rel (p.1, i)) fun _ _ _ ↦ True

variable (H : RotationMap V D')

/-- The underlying multigraph of `R.addTrivial H` is the union of those of `R` and `H`. -/
@[simp]
theorem graph_addTrivial : (R.addTrivial H).graph = R.graph.union H :=
  rfl

/-- The darts of `R` keep their constraints in `R.addTrivial H`. -/
@[simp]
theorem rel_addTrivial_inl (v : V) (i : D) : (R.addTrivial H).rel (v, .inl i) = R.rel (v, i) :=
  rfl

/-- The constraints on the added darts always hold. -/
@[simp]
theorem rel_addTrivial_inr (v : V) (j : D') (a b : α) : (R.addTrivial H).rel (v, .inr j) a b :=
  trivial

variable {R H} in
/-- The darts of `R` keep their constraints in `R.addTrivial H`. -/
theorem satisfies_addTrivial_inl {σ : V → α} {v : V} {i : D} :
    (R.addTrivial H).toConstraintGraph.Satisfies σ (v, .inl i) ↔
      R.toConstraintGraph.Satisfies σ (v, i) :=
  Iff.rfl

variable {R} in
/-- The added darts are satisfied by every labelling. -/
theorem satisfies_addTrivial_inr (σ : V → α) (v : V) (j : D') :
    (R.addTrivial H).toConstraintGraph.Satisfies σ (v, .inr j) :=
  trivial

/-- Adding edges with constraints that always hold preserves satisfiability. -/
theorem satisfiable_addTrivial_iff :
    (R.addTrivial H).toConstraintGraph.Satisfiable ↔ R.toConstraintGraph.Satisfiable := by
  refine ⟨fun ⟨σ, hσ⟩ ↦ ⟨σ, fun p ↦ hσ (p.1, .inl p.2)⟩, fun ⟨σ, hσ⟩ ↦ ⟨σ, ?_⟩⟩
  rintro ⟨v, i | j⟩
  exacts [hσ (v, i), trivial]

variable [Fintype V] [Fintype D] [Fintype D']

/-- Adding edges with constraints that always hold does not change the number of violated
darts. -/
theorem card_unsatEdges_addTrivial (σ : V → α) :
    #((R.addTrivial H).toConstraintGraph.unsatEdges σ) = #(R.toConstraintGraph.unsatEdges σ) := by
  refine (card_bij (fun p _ ↦ (p.1, .inl p.2)) (fun p hp ↦ ?_) (fun p _ q _ h ↦ ?_)
    fun q hq ↦ ?_).symm
  · simpa using hp
  · simp only [Prod.mk.injEq, Sum.inl.injEq] at h
    exact Prod.ext h.1 h.2
  · obtain ⟨v, i | j⟩ := q
    · exact ⟨(v, i), by simpa using hq, rfl⟩
    · simp at hq

/-- Adding edges with constraints that always hold scales the proportion of violated darts by
`|D| / (|D| + |D'|)`. -/
theorem unsatFrac_addTrivial (σ : V → α) :
    (R.addTrivial H).toConstraintGraph.unsatFrac σ =
      Fintype.card D / (Fintype.card D + Fintype.card D') * R.toConstraintGraph.unsatFrac σ := by
  have hk := R.toConstraintGraph.card_unsatEdges_le σ
  simp only [ConstraintGraph.unsatFrac, card_unsatEdges_addTrivial, Fintype.card_prod,
    Fintype.card_sum] at hk ⊢
  rcases Nat.eq_zero_or_pos #(R.toConstraintGraph.unsatEdges σ) with h₀ | h₀
  · simp [h₀]
  have h := h₀.trans_le hk
  have hV : Fintype.card V ≠ 0 := by rintro h'; simp [h'] at h
  have hD : Fintype.card D ≠ 0 := by rintro h'; simp [h'] at h
  push_cast
  field_simp

/-- **Adding edges with constraints that always hold** scales the value by
`|D| / (|D| + |D'|)`. -/
theorem unsatVal_addTrivial :
    (R.addTrivial H).toConstraintGraph.unsatVal =
      Fintype.card D / (Fintype.card D + Fintype.card D') * R.toConstraintGraph.unsatVal := by
  rw [ConstraintGraph.unsatVal, ConstraintGraph.unsatVal, Real.mul_iInf_of_nonneg (by positivity)]
  exact iInf_congr (R.unsatFrac_addTrivial H)

end AddTrivial

section AddLoops

variable (E : Type*)

/-- The regular constraint graph `R` with a self-loop added at every vertex for each `j : E`,
carrying constraints that always hold: its underlying multigraph is `R.graph.addLoops E`. -/
def addLoops : RegularConstraintGraph V (D ⊕ E) α :=
  R.addTrivial (RotationMap.loops V E)

/-- The underlying multigraph of `R.addLoops E` is that of `R` with self-loops added. -/
@[simp]
theorem graph_addLoops : (R.addLoops E).graph = R.graph.addLoops E :=
  rfl

/-- Adding self-loops with constraints that always hold preserves satisfiability. -/
theorem satisfiable_addLoops_iff :
    (R.addLoops E).toConstraintGraph.Satisfiable ↔ R.toConstraintGraph.Satisfiable :=
  R.satisfiable_addTrivial_iff _

/-- **Adding self-loops** with constraints that always hold scales the value by
`|D| / (|D| + |E|)`. -/
theorem unsatVal_addLoops [Fintype V] [Fintype D] [Fintype E] :
    (R.addLoops E).toConstraintGraph.unsatVal =
      Fintype.card D / (Fintype.card D + Fintype.card E) * R.toConstraintGraph.unsatVal :=
  R.unsatVal_addTrivial _

end AddLoops

end RegularConstraintGraph

end Cslib.PCP
