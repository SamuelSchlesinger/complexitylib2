/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.AssignmentTester
public import Complexity.Computability.PCP.Encoded.Constraints
public import Complexity.Computability.PCP.Composition
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Complexity.Tactic.PolyTime
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases

/-!
# Executable composition with the Hadamard assignment tester

Composition replaces each original edge by the tester's coin-to-query edges. Supplied finite
numberings give disjoint identifiers to input-table bits, proof-table bits, and coin vertices.
Explicit lists enumerate coins and queries; the exact interpretation and soundness results
require each list to enumerate its type once. The program itself also handles empty or incomplete
lists, and preserves endpoint bounds for every well-formed input graph.

The alphabet, its numbering, and the coin/query lists are fixed independently of the input graph.
The uniform polynomial-time certificate charges graph enumeration, tester queries, copying, and
output storage. These constants can be enormous: this establishes asymptotic constructibility,
not a practical bound on the size of a fully expanded tester gadget.

`composeTabulated` materializes each output constraint as a Boolean table over the fixed answer
alphabet. Its certificate hides internal coin/query encodings and composes with a graph routine
written in the client's input representation.

## Main definitions

* `Cslib.PCP.Encoded.Graph.compose`: executable gadget enumeration and vertex numbering.
* `Cslib.PCP.Encoded.Graph.composeTabulated`: composition with tabulated output constraints.

## Main results

* `Cslib.PCP.Encoded.Graph.isPolyTime_composeTabulated`: uniform, compositional cost certificate.
* `Cslib.PCP.Encoded.Graph.toGraph_compose`: exact agreement with mathematical composition.
* `Cslib.PCP.Encoded.Graph.le_unsatVal_compose`: the existing `1/476` gap bound transfers.
* `Cslib.PCP.Encoded.Graph.satisfiable_composeTabulated_iff`: satisfiability is preserved.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.PCP.Encoded

open Cslib.PCP.HadamardTester Turing.MultiTapeTM

namespace Graph

variable {α Input : Type} [Fintype α] [DecidableEq α]
  {input : Input ↪ List Bool} {width : ℕ}

/-- The local slots in one numbered block: an input-table bit, a proof-table bit, or a coin
vertex. The block's owner is the old vertex or edge index. -/
abbrev ComposeSlot (α : Type) : Type :=
  (α → Bool) ⊕ (LinPos α ⊕ QuadPos α) ⊕ Rand α

/-- Number a queried proof position using a supplied finite slot numbering. -/
def composePosition (number : ComposeSlot α ≃ Fin width) (edge src dst : ℕ) : Pos α → ℕ :=
  Sum.elim (fun p => (if p.1 = 0 then src else dst) * width + (number (.inl p.2)).val)
    fun p => edge * width + (number (.inr (.inl p))).val

/-- Build the edge from one coin vertex to one of the seventeen queried proof positions. -/
def composeEdge (number : ComposeSlot α ≃ Fin width) (edge : Edge (α → α → Bool))
    (index : ℕ) (coins : Rand α) (i : Query) : Edge ((α → α → Bool) × Rand α × Query) :=
  ⟨index * width + (number (.inr (.inr coins))).val,
    composePosition number index edge.src edge.dst
      (Encoded.HadamardTester.query edge.constraint coins i),
    (edge.constraint, coins, i)⟩

/-- Verify the claimed answers and their agreement with the queried proof symbol. -/
def composeEval (descriptor : (α → α → Bool) × Rand α × Query)
    (a b : Bool × (Query → Bool)) : Bool :=
  Encoded.HadamardTester.accepts descriptor.1 descriptor.2.1 a.2 &&
    (a.2 descriptor.2.2 == b.1)

/-- Enumerate all supplied random strings and queries for every original edge, in list order. -/
def composeDarts (coins : List (Rand α)) (queries : List Query)
    (g : Graph (α → α → Bool)) : List ((ℕ × Rand α) × Query) :=
  ((List.range g.edges.length).product coins).product queries

/-- Compose an encoded graph with a specified list of coins and queries.
Full alphabet reduction requires each of those lists to enumerate its type exactly once. -/
def compose (number : ComposeSlot α ≃ Fin width) (coins : List (Rand α))
    (queries : List Query) (g : Graph (α → α → Bool)) :
    Graph ((α → α → Bool) × Rand α × Query) :=
  ⟨(g.vertices + g.edges.length) * width,
    (g.composeDarts coins queries).map fun p =>
      composeEdge number (g.edgeAt (fun _ _ => false) p.1.1) p.1.1 p.1.2 p.2⟩

omit [Fintype α] [DecidableEq α] in
/-- Position numbering charges all runtime indices; finite dispatch only concerns the fixed
alphabet's local proof position. -/
@[fun_prop]
theorem isPolyTime_composePosition [Finite α] (number : ComposeSlot α ≃ Fin width)
    {edge src dst : Input → ℕ} {position : Input → Pos α}
    {positionEncoding : Pos α ↪ List Bool}
    (hedge : ComputableTidilyInPolyTime edge input encUnary)
    (hsrc : ComputableTidilyInPolyTime src input encUnary)
    (hdst : ComputableTidilyInPolyTime dst input encUnary)
    (hposition : ComputableTidilyInPolyTime position input positionEncoding) :
    ComputableTidilyInPolyTime
      (fun x => composePosition number (edge x) (src x) (dst x) (position x)) input encUnary := by
  apply ComputableTidilyInPolyTime.finite_cases
    (branch := fun p x => composePosition number (edge x) (src x) (dst x) p) hposition
  rintro (⟨b, r⟩ | p)
  · dsimp only [composePosition, Sum.elim_inl]
    split_ifs <;> polytime
  · dsimp only [composePosition, Sum.elim_inr]
    polytime

/-- A gadget edge is computed uniformly in the original edge, its index, coins, and query. -/
@[fun_prop]
theorem isPolyTime_composeEdge (number : ComposeSlot α ≃ Fin width)
    {edge : Input → Edge (α → α → Bool)} {index : Input → ℕ}
    {coins : Input → Rand α} {query : Input → Query}
    {coinsEncoding : Rand α ↪ List Bool} {queryEncoding : Query ↪ List Bool}
    (hedge : ComputableTidilyInPolyTime edge input (Edge.encoding (encPi (encPi encBool))))
    (hindex : ComputableTidilyInPolyTime index input encUnary)
    (hcoins : ComputableTidilyInPolyTime coins input coinsEncoding)
    (hquery : ComputableTidilyInPolyTime query input queryEncoding) :
    ComputableTidilyInPolyTime (fun x => composeEdge number (edge x) (index x) (coins x) (query x))
      input (Edge.encoding (encPair (encPi (encPi encBool))
        (encPair coinsEncoding queryEncoding))) := by
  have hnumber : ComputableTidilyInPolyTime (fun ω => (number (.inr (.inr ω))).val)
      coinsEncoding encUnary := .of_finite _
  have hposition := Encoded.HadamardTester.isPolyTime_query coinsEncoding queryEncoding
    (encFinite (Pos α))
  have hposition' := hposition.comp
    ((Edge.isPolyTime_constraint hedge).prod (hcoins.prod hquery))
  have hdst' := isPolyTime_composePosition number hindex (Edge.isPolyTime_src hedge)
    (Edge.isPolyTime_dst hedge) hposition'
  exact Edge.isPolyTime_mk
    (ComputableTidilyInPolyTime.unary_add.comp
      ((ComputableTidilyInPolyTime.unary_mul.comp (hindex.prod (.const width))).prod
        (hnumber.comp hcoins))) hdst'
    ((Edge.isPolyTime_constraint hedge).prod (hcoins.prod hquery))

/-- The verifier's edge predicate charges all supplied finite tables and query answers. -/
@[fun_prop]
theorem isPolyTime_composeEval (coinsEncoding : Rand α ↪ List Bool)
    (queryEncoding : Query ↪ List Bool) :
    ComputableTidilyInPolyTime
      (fun p : ((α → α → Bool) × Rand α × Query) ×
          (Bool × (Query → Bool)) × (Bool × (Query → Bool)) => composeEval p.1 p.2.1 p.2.2)
      (encPair (encPair (encPi (encPi encBool)) (encPair coinsEncoding queryEncoding))
        (encPair (encPair encBool (encPi encBool)) (encPair encBool (encPi encBool)))) encBool :=
  .of_finite _

/-- The full construction charges the old graph, enumeration, each tester call, copying,
and the complete output graph. The finite alphabet and supplied lists are fixed. -/
@[fun_prop]
theorem isPolyTime_compose (number : ComposeSlot α ≃ Fin width) (coins : List (Rand α))
    (queries : List Query) (coinsEncoding : Rand α ↪ List Bool)
    (queryEncoding : Query ↪ List Bool) :
    ComputableTidilyInPolyTime (compose number coins queries)
      (encoding (encPi (encPi encBool)))
      (encoding (encPair (encPi (encPi encBool)) (encPair coinsEncoding queryEncoding))) := by
  have hdarts : ComputableTidilyInPolyTime (composeDarts coins queries)
      (encoding (encPi (encPi encBool)))
      (encList (encPair (encPair encUnary coinsEncoding) queryEncoding)) := by
    unfold composeDarts List.product
    fun_prop
  unfold compose
  fun_prop

/-- Return composition to the fixed Boolean-table descriptor type over its answer alphabet. -/
def composeTabulated (number : ComposeSlot α ≃ Fin width) (coins : List (Rand α))
    (queries : List Query) (g : Graph (α → α → Bool)) :
    Graph ((Bool × (Query → Bool)) → (Bool × (Query → Bool)) → Bool) :=
  (g.compose number coins queries).mapConstraints composeEval

/-- Tabulated composition fixes its internal finite encodings, so clients only certify the
input graph in their own input representation. Every output constraint table is charged. -/
@[fun_prop]
theorem isPolyTime_composeTabulated {graph : Input → Graph (α → α → Bool)}
    (hgraph : ComputableTidilyInPolyTime graph input (encoding (encPi (encPi encBool))))
    (number : ComposeSlot α ≃ Fin width) (coins : List (Rand α)) (queries : List Query) :
    ComputableTidilyInPolyTime (fun x => (graph x).composeTabulated number coins queries)
      input (encoding (encPi (encPi encBool))) :=
  (isPolyTime_tabulateConstraints
    (isPolyTime_composeEval (encFinite (Rand α)) (encFinite Query))).comp
      ((isPolyTime_compose number coins queries (encFinite (Rand α)) (encFinite Query)).comp hgraph)

/-- Each original edge produces one edge for every supplied pair of coins and query. -/
@[simp]
theorem length_edges_compose (number : ComposeSlot α ≃ Fin width)
    (coins : List (Rand α)) (queries : List Query) (g : Graph (α → α → Bool)) :
    (g.compose number coins queries).edges.length =
      g.edges.length * coins.length * queries.length := by
  simp only [compose, List.length_map, composeDarts]
  change (((List.range g.edges.length) ×ˢ coins) ×ˢ queries).length = _
  simp only [List.length_product, List.length_range]

/-- The declared vertex count grows by a fixed factor in the old vertices and edges. -/
@[simp]
theorem vertices_compose (number : ComposeSlot α ≃ Fin width)
    (coins : List (Rand α)) (queries : List Query) (g : Graph (α → α → Bool)) :
    (g.compose number coins queries).vertices = (g.vertices + g.edges.length) * width := rfl

/-- Split a mathematical composed vertex into its owner index and local slot. -/
def composeOwner {E : Type} (index : E → ℕ) :
    ConstraintGraph.ComposePos ℕ E α ⊕ E × Rand α → ℕ × ComposeSlot α :=
  Sum.elim
    (Sum.elim (fun p => (p.1, .inl p.2)) (fun p => (index p.1, .inr (.inl p.2))))
    (fun p => (index p.1, .inr (.inr p.2)))

/-- The same explicit numbering on all mathematical proof positions and coin vertices. -/
def composeVertex {E : Type} (number : ComposeSlot α ≃ Fin width) (index : E → ℕ)
    (vertex : ConstraintGraph.ComposePos ℕ E α ⊕ E × Rand α) : ℕ :=
  (composeOwner index vertex).1 * width + (number (composeOwner index vertex).2).val

omit [Fintype α] [DecidableEq α] in
/-- Distinct table positions and coin vertices retain distinct identifiers. -/
theorem composeVertex_injective {E : Type} (number : ComposeSlot α ≃ Fin width)
    {index : E → ℕ} (hindex : Function.Injective index) :
    Function.Injective (composeVertex number index) := by
  have howner : Function.Injective (composeOwner (α := α) index) := by
    rintro ((⟨v, r⟩ | ⟨e, p⟩) | ⟨e, ω⟩) ((⟨v', r'⟩ | ⟨e', p'⟩) | ⟨e', ω'⟩) h <;>
      simp only [composeOwner, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq, Sum.inl.injEq,
        Sum.inr.injEq, reduceCtorEq, and_false] at h
    · rcases h with ⟨rfl, rfl⟩
      rfl
    · rcases h with ⟨h, rfl⟩
      cases hindex h
      rfl
    · rcases h with ⟨h, rfl⟩
      cases hindex h
      rfl
  let : NeZero width := (number (.inr (.inr default))).neZero
  exact (Nat.divModEquiv width).symm.injective.comp
    ((Equiv.prodCongr (Equiv.refl ℕ) number).injective.comp howner)

omit [Fintype α] [DecidableEq α] in
/-- The explicit endpoint selection agrees with `ConstraintGraph.testerPos`. -/
theorem composePosition_eq (number : ComposeSlot α ≃ Fin width)
    (g : Graph (α → α → Bool)) (e : Fin g.edges.length) (p : Pos α) :
    composePosition number e.val (g.edges.get e).src (g.edges.get e).dst p =
      composeVertex number Fin.val (.inl ((g.toGraph id).testerPos e p)) := by
  rcases p with ⟨b, r⟩ | p
  · fin_cases b <;> rfl
  · rfl

omit [Fintype α] [DecidableEq α] in
/-- The dart enumeration includes exactly the valid old indices and listed coins/queries. -/
@[simp]
theorem mem_composeDarts_iff (coins : List (Rand α)) (queries : List Query)
    (g : Graph (α → α → Bool)) (p : (ℕ × Rand α) × Query) :
    p ∈ g.composeDarts coins queries ↔
      p.1.1 < g.edges.length ∧ p.1.2 ∈ coins ∧ p.2 ∈ queries := by
  rcases p with ⟨⟨e, ω⟩, i⟩
  change ((e, ω), i) ∈ ((List.range g.edges.length ×ˢ coins) ×ˢ queries) ↔ _
  simp only [List.mem_product, List.mem_range, and_assoc]

/-- Valid old endpoints give valid output endpoints, even for empty or incomplete coin lists. -/
theorem WellFormed.compose (number : ComposeSlot α ≃ Fin width)
    (coins : List (Rand α)) (queries : List Query) {g : Graph (α → α → Bool)}
    (hg : g.WellFormed) : (g.compose number coins queries).WellFormed := by
  have hnumber {owner bound : ℕ} (howner : owner < bound) (slot : ComposeSlot α) :
      owner * width + (number slot).val < bound * width :=
    (Nat.add_lt_add_left (number slot).isLt _).trans_le
      (by simpa only [Nat.succ_mul] using Nat.mul_le_mul_right width howner)
  intro edge hedge
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hedge
  have hp := (g.mem_composeDarts_iff coins queries p).mp hp
  have heq : g.edgeAt (fun _ _ => false) p.1.1 = g.edges[p.1.1] :=
    List.getD_eq_getElem _ _ hp.1
  have he := hg _ (List.getElem_mem hp.1)
  have hi : p.1.1 < g.vertices + g.edges.length := hp.1.trans_le (Nat.le_add_left ..)
  have hsrc : (g.edges[p.1.1]).src < g.vertices + g.edges.length :=
    he.1.trans_le (Nat.le_add_right ..)
  have hdst : (g.edges[p.1.1]).dst < g.vertices + g.edges.length :=
    he.2.trans_le (Nat.le_add_right ..)
  constructor
  · exact hnumber hi _
  · change composePosition number p.1.1 _ _ _ < _
    rw [heq]
    rcases Encoded.HadamardTester.query (g.edges[p.1.1]).constraint p.1.2 p.2 with
      ⟨b, r⟩ | q
    · dsimp only [composePosition, Sum.elim_inl]
      split_ifs
      · exact hnumber hsrc _
      · exact hnumber hdst _
    · exact hnumber hi _

omit [Fintype α] [DecidableEq α] in
/-- Listing each coin and query once lists each composed dart once. -/
theorem nodup_composeDarts (coins : List (Rand α)) (queries : List Query)
    (g : Graph (α → α → Bool)) (hcoins : coins.Nodup) (hqueries : queries.Nodup) :
    (g.composeDarts coins queries).Nodup :=
  (List.nodup_range.product hcoins).product hqueries

open Classical in
/-- Composition retains the ordered edge, coin and query occurrences, even when stored
edge values coincide. -/
noncomputable def composeEnumeration (number : ComposeSlot α ≃ Fin width)
    (coins : List (Rand α)) (queries : List Query) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    List.Enumeration (g.compose number coins queries).edges
      (fun p : (Fin g.edges.length × Rand α) × Query =>
        composeEdge number (g.edgeAt (fun _ _ => false) p.1.1.val) p.1.1.val p.1.2 p.2) :=
  (((List.Enumeration.range g.edges.length).prod
    (List.Enumeration.ofNodup coins hcoins hmemCoins)).prod
      (List.Enumeration.ofNodup queries hqueries hmemQueries)).map
        (fun p => composeEdge number (g.edgeAt (fun _ _ => false) p.1.1) p.1.1 p.1.2 p.2)

/-- Enumerating every coin and query once gives exactly the existing composed graph, with
the specified vertex numbering and the explicit output edge order. -/
theorem toGraph_compose (number : ComposeSlot α ≃ Fin width)
    (coins : List (Rand α)) (queries : List Query) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    (g.compose number coins queries).toGraph composeEval =
      ((g.toGraph id).compose.map (composeVertex number Fin.val)).comap
        (g.composeEnumeration number coins queries hcoins hqueries
          hmemCoins hmemQueries).equiv := by
  apply toGraph_eq_comap _ _ (g.composeEnumeration number coins queries hcoins hqueries
    hmemCoins hmemQueries)
  · intro p
    rfl
  · intro p
    simp only [composeEdge, edgeAt, List.getD_eq_get, ConstraintGraph.compose,
      LocalTest.toConstraintGraph, ConstraintGraph.composeTest,
      LocalTest.mix, LocalTest.map, composeVertex]
    rw [Encoded.HadamardTester.query_eq, composePosition_eq]
    rfl
  · intro p a b
    simp only [composeEdge, edgeAt, List.getD_eq_get, ConstraintGraph.compose,
      LocalTest.toConstraintGraph, ConstraintGraph.composeTest, LocalTest.mix, LocalTest.map,
      composeEval, Bool.and_eq_true, beq_iff_eq, Encoded.HadamardTester.accepts_eq_true,
      toGraph, id_eq]

/-- Exact interpretation and injective numbering preserve the mathematical composition value. -/
theorem unsatVal_compose_eq (number : ComposeSlot α ≃ Fin width)
    (coins : List (Rand α)) (queries : List Query) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    ((g.compose number coins queries).toGraph composeEval).unsatVal =
      (g.toGraph id).compose.unsatVal := by
  rw [toGraph_compose number coins queries g hcoins hqueries hmemCoins hmemQueries,
    ConstraintGraph.unsatVal_comap_equiv,
    ConstraintGraph.unsatVal_map _ (composeVertex_injective number Fin.val_injective)]

/-- Full executable composition preserves satisfiability. -/
theorem satisfiable_compose_iff [Nonempty α] (number : ComposeSlot α ≃ Fin width)
    (coins : List (Rand α)) (queries : List Query) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    ((g.compose number coins queries).toGraph composeEval).Satisfiable ↔
      (g.toGraph id).Satisfiable := by
  rw [toGraph_compose number coins queries g hcoins hqueries hmemCoins hmemQueries,
    ConstraintGraph.satisfiable_comap_iff _ (Equiv.surjective _),
    ConstraintGraph.satisfiable_map _ (composeVertex_injective number Fin.val_injective),
    ConstraintGraph.satisfiable_compose_iff]

/-- Full executable composition retains at least the existing `1/476` fraction of the gap. -/
theorem le_unsatVal_compose [Nonempty α] (number : ComposeSlot α ≃ Fin width)
    (coins : List (Rand α)) (queries : List Query) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    (g.toGraph id).unsatVal / 476 ≤
      ((g.compose number coins queries).toGraph composeEval).unsatVal := by
  rw [unsatVal_compose_eq number coins queries g hcoins hqueries hmemCoins hmemQueries]
  exact ConstraintGraph.le_unsatVal_compose _

/-- Tabulating the output constraints preserves the exact mathematical composition value. -/
theorem unsatVal_composeTabulated_eq (number : ComposeSlot α ≃ Fin width)
    (coins : List (Rand α)) (queries : List Query) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    ((g.composeTabulated number coins queries).toGraph id).unsatVal =
      (g.toGraph id).compose.unsatVal := by
  rw [composeTabulated, unsatVal_mapConstraints]
  exact unsatVal_compose_eq number coins queries g hcoins hqueries hmemCoins hmemQueries

/-- Tabulated full composition preserves satisfiability. -/
theorem satisfiable_composeTabulated_iff [Nonempty α] (number : ComposeSlot α ≃ Fin width)
    (coins : List (Rand α)) (queries : List Query) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    ((g.composeTabulated number coins queries).toGraph id).Satisfiable ↔
      (g.toGraph id).Satisfiable := by
  rw [composeTabulated, satisfiable_mapConstraints_iff]
  exact satisfiable_compose_iff number coins queries g hcoins hqueries hmemCoins hmemQueries

end Graph

end Cslib.PCP.Encoded
