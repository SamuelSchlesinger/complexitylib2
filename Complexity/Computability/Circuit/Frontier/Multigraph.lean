/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Combinatorics.Graph.Connected.EdgeCut
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Lattice.Nat
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Multigraphs, layouts, and the layout hypothesis

A `Multigraph V E` gives every edge two endpoints. Parallel edges are distinct elements of `E`,
and the orientation of an edge plays no role: incidence, cuts and connectivity depend only on
the unordered pair `G.ends e`. A multigraph is the spanning case of Mathlib's `Graph V E`
(`Multigraph.toGraph`), presented with the vertices and edges as types, so that layouts are
numberings of a type and assignments of values to the edges are functions on `E`.

A *layout* numbers the vertices `v₀, v₁, ...`, and its *frontier* at time `t` is the edge cut
between the first `t` vertices and the rest. The *width* of a layout is the size of its largest
frontier.

For a connected graph, the *cycle rank* `β₁ = |E| - |V| + 1` counts its independent cycles.
The frontier method needs one fact from graph theory: that graphs of maximum degree `d` have
layouts whose width is at most a fixed multiple `A` of their cycle rank, up to lower-order terms.
`LayoutBound d A` states this as a hypothesis, so that any layout theorem can be plugged in.

## Main definitions

* `Cslib.Circuits.Frontier.Multigraph`: a multigraph, with `incidenceSet`, `MaxDegreeLE`,
  `Loopless`, `toSimpleGraph` (whose connectivity is that of the multigraph), `edgeCut`, and
  `cycleRank`.
* `Cslib.Circuits.Frontier.Layout V`: a numbering of the vertices, with `Layout.initial`.
* `Cslib.Circuits.Frontier.Multigraph.frontier`, `Multigraph.width`: the frontiers of a layout
  and its width.
* `Cslib.Circuits.Frontier.LayoutBound d A`: the layout hypothesis for maximum degree `d` with
  coefficient `A`.

## Main results

* `Cslib.Circuits.Frontier.Multigraph.edgeCut_toGraph`: edge cuts are those of Mathlib's
  multigraphs.
* `Cslib.Circuits.Frontier.Multigraph.card_le_card_add_one_of_connected`: a connected graph has
  at least `|V| - 1` edges, so its cycle rank `|E| + 1 - |V|` involves no truncation.
* `Cslib.Circuits.Frontier.Multigraph.frontier_succ_subset`: consecutive frontiers differ only
  at the edges of the vertex processed in between.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set

/-- A multigraph with vertices `V` and edges `E`: every edge has two endpoints, its *source*
and its *target*. Parallel edges are distinct elements of `E`, and loops are allowed. The
orientation plays no role in what follows. -/
structure Multigraph (V E : Type*) where
  /-- One endpoint of an edge. -/
  src : E → V
  /-- The other endpoint of an edge. -/
  tgt : E → V

namespace Multigraph

variable {V E : Type*} (G : Multigraph V E)

/-- The ends of an edge, as an unordered pair. -/
def ends (e : E) : Sym2 V :=
  s(G.src e, G.tgt e)

/-- The edges incident to a vertex. -/
def incidenceSet (v : V) : Set E :=
  {e | G.src e = v ∨ G.tgt e = v}

/-- Every vertex is incident to at most `d` edges. In a loopless multigraph this says that the
maximum degree is at most `d`. -/
def MaxDegreeLE (d : ℕ) : Prop :=
  ∀ v, (G.incidenceSet v).ncard ≤ d

/-- No edge joins a vertex to itself. -/
def Loopless : Prop :=
  ∀ e, G.src e ≠ G.tgt e

/-- The simple graph underlying a multigraph: two distinct vertices are adjacent when an edge
joins them. A multigraph is connected when this simple graph is. -/
def toSimpleGraph : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (range G.ends)

/-- The *edge cut* of a set of vertices `L`: the edges with exactly one endpoint in `L`. -/
def edgeCut (L : Set V) : Set E :=
  {e | ¬(G.src e ∈ L ↔ G.tgt e ∈ L)}

/-- The edges with an endpoint in `L`. -/
def touching (L : Set V) : Set E :=
  {e | G.src e ∈ L ∨ G.tgt e ∈ L}

/-- The *cycle rank* `|E| + 1 - |V|`. For a nonempty connected multigraph this is the number of
independent cycles, the dimension of its cycle space; on disconnected graphs it is not the sum of
the cycle ranks of the components. -/
noncomputable def cycleRank (_G : Multigraph V E) : ℕ :=
  Nat.card E + 1 - Nat.card V

variable {G}

theorem mem_incidenceSet {v : V} {e : E} : e ∈ G.incidenceSet v ↔ G.src e = v ∨ G.tgt e = v :=
  Iff.rfl

theorem mem_edgeCut {L : Set V} {e : E} : e ∈ G.edgeCut L ↔ ¬(G.src e ∈ L ↔ G.tgt e ∈ L) :=
  Iff.rfl

theorem mem_touching {L : Set V} {e : E} : e ∈ G.touching L ↔ G.src e ∈ L ∨ G.tgt e ∈ L :=
  Iff.rfl

theorem toSimpleGraph_adj {u v : V} :
    G.toSimpleGraph.Adj u v ↔ u ≠ v ∧ ∃ e, G.ends e = s(u, v) := by
  simp [toSimpleGraph, and_comm]

variable (G)

/-- The endpoints of an edge are joined in the underlying simple graph. -/
theorem reachable_src_tgt (e : E) : G.toSimpleGraph.Reachable (G.src e) (G.tgt e) := by
  by_cases h : G.src e = G.tgt e
  · exact h ▸ SimpleGraph.Reachable.refl _
  · exact (toSimpleGraph_adj.mpr ⟨h, e, rfl⟩).reachable

@[simp] theorem edgeCut_empty : G.edgeCut ∅ = ∅ := by
  ext e; simp [mem_edgeCut]

@[simp] theorem edgeCut_univ : G.edgeCut univ = ∅ := by
  ext e; simp [mem_edgeCut]

/-- The edges of the cut of `L` touch `L`. -/
theorem edgeCut_subset_touching (L : Set V) : G.edgeCut L ⊆ G.touching L := by
  intro e he
  by_contra h
  simp only [mem_touching, not_or] at h
  exact he (iff_of_false h.1 h.2)

/-- Adding a vertex changes a cut only at the edges incident to it. -/
theorem edgeCut_insert_subset (v : V) (L : Set V) :
    G.edgeCut (insert v L) ⊆ G.edgeCut L ∪ G.incidenceSet v := by
  intro e he
  by_cases hv : G.src e = v ∨ G.tgt e = v
  · exact Or.inr hv
  · rw [not_or] at hv
    left
    simpa [mem_edgeCut, hv.1, hv.2] using he

/-- **A connected multigraph has at least `|V| - 1` edges**: its cycle rank `|E| + 1 - |V|`
involves no truncation. -/
theorem card_le_card_add_one_of_connected [Finite E] (h : G.toSimpleGraph.Connected) :
    Nat.card V ≤ Nat.card E + 1 := by
  refine h.card_vert_le_card_edgeSet_add_one.trans (Nat.add_le_add_right ?_ 1)
  rw [toSimpleGraph, SimpleGraph.edgeSet_fromEdgeSet, Nat.card_coe_set_eq]
  exact (ncard_le_ncard sdiff_subset (finite_range _)).trans
    ((Nat.card_coe_set_eq _).symm.trans_le (Finite.card_range_le _))

/-! ### Mathlib's multigraphs -/

/-- A multigraph as a Mathlib `Graph` whose vertex set and edge set are everything. -/
def toGraph : Graph V E where
  vertexSet := univ
  edgeSet := univ
  IsLink e x y := G.ends e = s(x, y)
  isLink_symm _ _ := ⟨fun _ _ h => h.trans Sym2.eq_swap⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := by
    rcases Sym2.eq_iff.mp (h.symm.trans h') with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  edge_mem_iff_exists_isLink e := iff_of_true (mem_univ e) ⟨_, _, rfl⟩
  left_mem_of_isLink _ _ _ _ := mem_univ _

@[simp] theorem toGraph_isLink {e : E} {x y : V} : G.toGraph.IsLink e x y ↔ G.ends e = s(x, y) :=
  Iff.rfl

/-- The edge cuts of a multigraph are those of Mathlib's `Graph`. -/
@[simp] theorem edgeCut_toGraph (L : Set V) : G.toGraph.edgeCut L = G.edgeCut L := by
  ext e
  rw [(show G.toGraph.IsLink e (G.src e) (G.tgt e) from rfl).mem_edgeCut_iff, mem_edgeCut]
  tauto

/-- The incidence sets of a multigraph are those of Mathlib's `Graph`. -/
@[simp] theorem incidenceSet_toGraph (v : V) : G.toGraph.incidenceSet v = G.incidenceSet v := by
  ext e
  simp only [Graph.incidenceSet, Graph.Inc, toGraph_isLink, ends, Sym2.eq_iff, mem_ofPred_eq,
    mem_incidenceSet]
  constructor
  · rintro ⟨y, ⟨h, -⟩ | ⟨-, h⟩⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨G.tgt e, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨G.src e, Or.inr ⟨rfl, h⟩⟩

end Multigraph

/-! ### Layouts -/

/-- A *layout* of a finite set of vertices: a numbering `v₀, v₁, ..., v_{N-1}`. -/
abbrev Layout (V : Type*) :=
  V ≃ Fin (Nat.card V)

namespace Layout

variable {V : Type*} (π : Layout V)

instance [Finite V] : Nonempty (Layout V) :=
  ⟨Finite.equivFin V⟩

/-- The first `t` vertices of a layout. -/
def initial (t : ℕ) : Set V :=
  {v | (π v : ℕ) < t}

theorem mem_initial {t : ℕ} {v : V} : v ∈ π.initial t ↔ (π v : ℕ) < t :=
  Iff.rfl

@[simp] theorem initial_zero : π.initial 0 = ∅ := by
  ext v; simp [mem_initial]

theorem initial_of_card_le {t : ℕ} (ht : Nat.card V ≤ t) : π.initial t = univ := by
  ext v; simpa [mem_initial] using (π v).isLt.trans_le ht

/-- The first `t + 1` vertices are the first `t` and the vertex numbered `t`. -/
theorem initial_succ {t : ℕ} (ht : t < Nat.card V) :
    π.initial (t + 1) = insert (π.symm ⟨t, ht⟩) (π.initial t) := by
  ext v
  simp only [mem_initial, mem_insert_iff, Equiv.eq_symm_apply, Fin.ext_iff]
  omega

/-- The first `t ≤ |V|` vertices of a layout are `t` vertices. -/
theorem ncard_initial {t : ℕ} (ht : t ≤ Nat.card V) : (π.initial t).ncard = t := by
  have : π.initial t = range (π.symm ∘ Fin.castLE ht) := by
    ext v
    simp only [mem_initial, mem_range]
    exact ⟨fun h => ⟨⟨π v, h⟩, by simp [Fin.castLE]⟩, by rintro ⟨j, rfl⟩; simp⟩
  rw [this, ncard_range_of_injective (π.symm.injective.comp (Fin.castLE_injective ht)),
    Nat.card_eq_fintype_card, Fintype.card_fin]

end Layout

namespace Multigraph

variable {V E : Type*} (G : Multigraph V E) (π : Layout V)

/-- The *frontier* of a layout at time `t`: the edge cut between the first `t` vertices and the
rest. -/
def frontier (t : ℕ) : Set E :=
  G.edgeCut (π.initial t)

/-- The *width* of a layout: the size of its largest frontier. -/
noncomputable def width : ℕ :=
  (Finset.range (Nat.card V)).sup fun t => (G.frontier π t).ncard

/-- An edge is on the frontier at time `t` when exactly one of its ends is among the first `t`
vertices. -/
theorem mem_frontier {t : ℕ} {e : E} :
    e ∈ G.frontier π t ↔ ¬((π (G.src e) : ℕ) < t ↔ (π (G.tgt e) : ℕ) < t) :=
  Iff.rfl

@[simp] theorem frontier_zero : G.frontier π 0 = ∅ := by
  simp [frontier]

theorem frontier_of_card_le {t : ℕ} (ht : Nat.card V ≤ t) : G.frontier π t = ∅ := by
  rw [frontier, π.initial_of_card_le ht, edgeCut_univ]

/-- Consecutive frontiers differ only at the edges of the vertex processed in between. -/
theorem frontier_succ_subset {t : ℕ} (ht : t < Nat.card V) :
    G.frontier π (t + 1) ⊆ G.frontier π t ∪ G.incidenceSet (π.symm ⟨t, ht⟩) := by
  rw [frontier, π.initial_succ ht]
  exact G.edgeCut_insert_subset _ _

theorem ncard_frontier_le_width (t : ℕ) : (G.frontier π t).ncard ≤ G.width π := by
  rcases lt_or_ge t (Nat.card V) with ht | ht
  · exact Finset.le_sup (f := fun t => (G.frontier π t).ncard) (Finset.mem_range.mpr ht)
  · simp [G.frontier_of_card_le π ht]

theorem width_le_iff {w : ℕ} : G.width π ≤ w ↔ ∀ t, (G.frontier π t).ncard ≤ w :=
  ⟨fun h t => (G.ncard_frontier_le_width π t).trans h,
    fun h => Finset.sup_le fun t _ => h t⟩

end Multigraph

/-- **The layout hypothesis** for maximum degree `d`, with coefficient `A`. For every `η > 0`
there is a constant `C` such that every connected, loopless multigraph of maximum degree `d`
has a layout of width at most `(A + η) β₁ + η |V| + C`, where `β₁` is the cycle rank.

Only the coefficient `A` matters for the circuit lower bounds: any error term that is sublinear
in the number of vertices may be absorbed into `η |V| + C`. -/
def LayoutBound (d : ℕ) (A : ℝ) : Prop :=
  ∀ η > 0, ∃ C : ℝ, ∀ (V E : Type) [Finite V] [Finite E] (G : Multigraph V E),
    G.toSimpleGraph.Connected → G.Loopless → G.MaxDegreeLE d →
      ∃ π : Layout V, (G.width π : ℝ) ≤ (A + η) * G.cycleRank + η * Nat.card V + C

end Cslib.Circuits.Frontier
