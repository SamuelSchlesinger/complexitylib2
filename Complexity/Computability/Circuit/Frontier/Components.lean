/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Layouts.Basic
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Layouts of disconnected graphs

The layout hypothesis `Cslib.Circuits.Frontier.LayoutBound` is stated for connected graphs. A
disconnected graph is laid out one connected component after another, each component by the
layout hypothesis (`LayoutBound.exists_layout_componentwise`). Every frontier of the result lies
among the edges of a single component, and is bounded in terms of the cycle rank of that
component alone.

A set of vertices `W` is *closed* when no edge leaves it: `G.edgeCut W = ∅`. Every union of
connected components is closed, and adding a disjoint closed set to a set of vertices does not
change its edge cut (`Multigraph.edgeCut_union_of_edgeCut_eq_empty`). So the frontiers of the
concatenated layout are those of the layouts of the components. The cycle rank of a closed set
`W` is `|E(W)| + 1 - |W|`, where `E(W)` are the edges with an endpoint in `W`
(`Multigraph.cycleRankOn`); it is the cycle rank of the subgraph induced on `W`.

## Main definitions

* `Cslib.Circuits.Frontier.Multigraph.cycleRankOn`: the cycle rank of a set of vertices.
* `Cslib.Circuits.Frontier.Multigraph.component`: the connected component of a vertex.
* `Cslib.Circuits.Frontier.Multigraph.induce`: the subgraph induced on a set of vertices.

## Main results

* `Cslib.Circuits.Frontier.Multigraph.edgeCut_union_of_edgeCut_eq_empty`: closed sets do not
  change edge cuts.
* `Cslib.Circuits.Frontier.Multigraph.edgeCut_component`: components are closed.
* `Cslib.Circuits.Frontier.Multigraph.connected_induce_component`: components are connected.
* `Cslib.Circuits.Frontier.Multigraph.ncard_component_le`: a component `W` has at least
  `|W| - 1` edges.
* `Cslib.Circuits.Frontier.LayoutBound.exists_layout_componentwise`: under the layout hypothesis,
  every loopless graph of maximum degree `d`, connected or not, has a layout whose frontiers at
  each step lie among the edges of the component of the vertex processed and are at most
  `(A + η) β₁ + η |V| + C`, for the cycle rank `β₁` of that component.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set

namespace Multigraph

variable {V E : Type*} (G : Multigraph V E)

/-- The truncated expression `|E(W)| + 1 - |W|`, where `E(W)` are the edges with an endpoint
in `W`. For a connected component it is the number of independent cycles of the component; it
need not be additive over components. -/
noncomputable def cycleRankOn (W : Set V) : ℕ :=
  (G.touching W).ncard + 1 - W.ncard

/-! ### Closed sets -/

/-- A set of vertices is closed exactly when every edge has either both endpoints in it or
none. -/
theorem edgeCut_eq_empty_iff {W : Set V} : G.edgeCut W = ∅ ↔ ∀ e, (G.src e ∈ W ↔ G.tgt e ∈ W) := by
  simp [eq_empty_iff_forall_notMem, mem_edgeCut]

/-- A larger set of vertices touches more edges. -/
theorem touching_mono {L M : Set V} (h : L ⊆ M) : G.touching L ⊆ G.touching M :=
  fun _ he => he.imp (@h _) (@h _)

/-- **Closed sets do not change edge cuts.** Adding a closed set `K` to a set `L` disjoint from
it does not change the edge cut of `L`. -/
theorem edgeCut_union_of_edgeCut_eq_empty {K L : Set V} (hK : G.edgeCut K = ∅)
    (h : Disjoint K L) : G.edgeCut (K ∪ L) = G.edgeCut L := by
  ext e
  have hKe := G.edgeCut_eq_empty_iff.1 hK e
  by_cases hs : G.src e ∈ K
  · have ht := hKe.1 hs
    simp [mem_edgeCut, hs, ht, disjoint_left.1 h hs, disjoint_left.1 h ht]
  · simp [mem_edgeCut, hs, mt hKe.2 hs]

/-- The edges touching a closed set `W` are those with both endpoints in `W`. -/
theorem touching_eq_of_edgeCut_eq_empty {W : Set V} (hW : G.edgeCut W = ∅) :
    G.touching W = {e | G.src e ∈ W ∧ G.tgt e ∈ W} := by
  ext e
  have := G.edgeCut_eq_empty_iff.1 hW e
  simp only [touching, mem_ofPred_eq]
  tauto

/-! ### Connected components -/

/-- The endpoints of an edge lie in the same connected component. -/
theorem connectedComponentMk_src (e : E) :
    G.toSimpleGraph.connectedComponentMk (G.src e) =
      G.toSimpleGraph.connectedComponentMk (G.tgt e) :=
  SimpleGraph.ConnectedComponent.sound (G.reachable_src_tgt e)

/-- **Unions of components are closed.** A set of vertices described by their connected
components has an empty edge cut. -/
theorem edgeCut_setOf_connectedComponentMk (P : G.toSimpleGraph.ConnectedComponent → Prop) :
    G.edgeCut {v | P (G.toSimpleGraph.connectedComponentMk v)} = ∅ :=
  G.edgeCut_eq_empty_iff.2 fun e => by simp only [mem_ofPred_eq, G.connectedComponentMk_src e]

/-- The connected component of a vertex `v`: the vertices joined to `v` by a walk. -/
def component (v : V) : Set V :=
  (G.toSimpleGraph.connectedComponentMk v).supp

theorem mem_component {u v : V} :
    u ∈ G.component v ↔ G.toSimpleGraph.connectedComponentMk u =
      G.toSimpleGraph.connectedComponentMk v :=
  Iff.rfl

/-- Every vertex lies in its own component. -/
theorem mem_component_self (v : V) : v ∈ G.component v :=
  rfl

/-- **Connected components are closed.** -/
theorem edgeCut_component (v : V) : G.edgeCut (G.component v) = ∅ :=
  G.edgeCut_setOf_connectedComponentMk (· = _)

/-! ### Induced subgraphs -/

/-- The subgraph induced on a set of vertices `W`: the edges with both endpoints in `W`. -/
def induce (W : Set V) : Multigraph W {e // G.src e ∈ W ∧ G.tgt e ∈ W} where
  src e := ⟨G.src e, e.2.1⟩
  tgt e := ⟨G.tgt e, e.2.2⟩

variable {G} in
/-- Induced subgraphs of loopless graphs are loopless. -/
theorem Loopless.induce (hG : G.Loopless) (W : Set V) : (G.induce W).Loopless :=
  fun e h => hG e (congrArg Subtype.val h)

variable {G} in
/-- Induced subgraphs have no larger degrees. -/
theorem MaxDegreeLE.induce [Finite E] {d : ℕ} (hG : G.MaxDegreeLE d) (W : Set V) :
    (G.induce W).MaxDegreeLE d := fun w =>
  (ncard_le_ncard_of_injOn Subtype.val (fun _ he => he.imp (congrArg Subtype.val)
    (congrArg Subtype.val)) Subtype.val_injective.injOn).trans (hG w)

/-- The simple graph underlying an induced subgraph is the induced simple graph. -/
theorem toSimpleGraph_induce (W : Set V) :
    (G.induce W).toSimpleGraph = G.toSimpleGraph.induce W := by
  ext u v
  simp only [toSimpleGraph_adj, SimpleGraph.comap_adj, Function.Embedding.subtype_apply, ne_eq,
    Subtype.ext_iff]
  refine and_congr_right fun _ => ⟨fun ⟨e, he⟩ => ⟨e.1, ?_⟩, fun ⟨e, he⟩ => ?_⟩
  · simpa [ends, induce, Sym2.map_mk] using congrArg (Sym2.map Subtype.val) he
  · -- An edge between two vertices of `W` is an edge of the induced subgraph.
    have hends : s(G.src e, G.tgt e) = s((u : V), v) := he
    have hW : G.src e ∈ W ∧ G.tgt e ∈ W := by
      rcases Sym2.eq_iff.1 hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;>
        simp [u.2, v.2]
    refine ⟨⟨e, hW⟩, ?_⟩
    rcases Sym2.eq_iff.1 hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Sym2.eq_iff.2 (Or.inl ⟨Subtype.ext h₁, Subtype.ext h₂⟩)
    · exact Sym2.eq_iff.2 (Or.inr ⟨Subtype.ext h₁, Subtype.ext h₂⟩)

/-- **Components are connected.** -/
theorem connected_induce_component (v : V) :
    (G.induce (G.component v)).toSimpleGraph.Connected := by
  rw [toSimpleGraph_induce]
  exact (G.toSimpleGraph.connectedComponentMk v).connected_toSimpleGraph

/-- The subgraph induced on a closed set `W` has the cycle rank of `W`. -/
theorem cycleRank_induce {W : Set V} (hW : G.edgeCut W = ∅) :
    (G.induce W).cycleRank = G.cycleRankOn W := by
  rw [cycleRankOn, G.touching_eq_of_edgeCut_eq_empty hW, ← Nat.card_coe_set_eq,
    ← Nat.card_coe_set_eq]
  rfl

/-- **A component `W` has at least `|W| - 1` edges**, so its cycle rank `|E(W)| + 1 - |W|`
involves no truncation. -/
theorem ncard_component_le [Finite E] (v : V) :
    (G.component v).ncard ≤ (G.touching (G.component v)).ncard + 1 := by
  have h := (G.induce (G.component v)).card_le_card_add_one_of_connected
    (G.connected_induce_component v)
  rwa [G.touching_eq_of_edgeCut_eq_empty (G.edgeCut_component v), ← Nat.card_coe_set_eq,
    ← Nat.card_coe_set_eq]

/-- On a closed set `W`, the edge cuts of the induced subgraph are those of `G`. -/
theorem edgeCut_image_val {W : Set V} (hW : G.edgeCut W = ∅) (S : Set W) :
    G.edgeCut (Subtype.val '' S) = Subtype.val '' (G.induce W).edgeCut S := by
  have key (e : {e // G.src e ∈ W ∧ G.tgt e ∈ W}) :
      e.1 ∈ G.edgeCut (Subtype.val '' S) ↔ e ∈ (G.induce W).edgeCut S := by
    change ¬(((G.induce W).src e : V) ∈ _ ↔ ((G.induce W).tgt e : V) ∈ _) ↔ _
    rw [Subtype.val_injective.mem_set_image, Subtype.val_injective.mem_set_image]
    rfl
  ext e
  refine ⟨fun he => ?_, fun ⟨e', he', hee'⟩ => hee' ▸ (key e').2 he'⟩
  -- An edge of the cut has an endpoint in `W`, hence both, as `W` is closed.
  have hW' := G.edgeCut_eq_empty_iff.1 hW e
  have hs : G.src e ∈ W :=
    (G.touching_mono (Subtype.coe_image_subset W S) (G.edgeCut_subset_touching _ he)).elim id
      hW'.2
  exact ⟨⟨e, hs, hW'.1 hs⟩, (key _).1 he, rfl⟩

end Multigraph

/-! ### Laying out components one after another -/

/-- **Layouts of disconnected graphs.** Under the layout hypothesis for maximum degree `d`, every
loopless graph of maximum degree `d`, connected or not, has a layout such that at every step `t`,
with `W` the component of the vertex processed, the frontiers at times `t` and `t + 1` lie among
the edges of `W` and have at most `(A + η) β₁(W) + η |V| + C` edges.

The components are laid out one after another, each by the layout hypothesis. -/
theorem LayoutBound.exists_layout_componentwise {d : ℕ} {A : ℝ} (h : LayoutBound d A) {η : ℝ}
    (hη : 0 < η) :
    ∃ C : ℝ, ∀ (V E : Type) [Finite V] [Finite E] (G : Multigraph V E),
      G.Loopless → G.MaxDegreeLE d →
        ∃ π : Layout V, ∀ t (ht : t < Nat.card V), ∀ s, t ≤ s → s ≤ t + 1 →
          G.frontier π s ⊆ G.touching (G.component (π.symm ⟨t, ht⟩)) ∧
          ((G.frontier π s).ncard : ℝ) ≤
            (A + η) * G.cycleRankOn (G.component (π.symm ⟨t, ht⟩)) + η * Nat.card V + C := by
  obtain ⟨C, hC⟩ := h η hη
  refine ⟨C, fun V E _ _ G hG hd => ?_⟩
  set Γ := G.toSimpleGraph
  -- Lay out each component by the layout hypothesis.
  have hlay (K : Γ.ConnectedComponent) : ∃ ρ : Layout K.supp, ∀ s,
      (((G.induce K.supp).frontier ρ s).ncard : ℝ) ≤
        (A + η) * G.cycleRankOn K.supp + η * Nat.card V + C := by
    obtain ⟨v, rfl⟩ := K.nonempty_supp
    obtain ⟨ρ, hρ⟩ := hC _ _ (G.induce (G.component v)) (G.connected_induce_component v)
      (hG.induce _) (hd.induce _)
    refine ⟨ρ, fun s =>
      ((Nat.cast_le.2 ((G.induce _).ncard_frontier_le_width ρ s)).trans hρ).trans ?_⟩
    rw [G.cycleRank_induce (G.edgeCut_component v)]
    have : (Nat.card (G.component v) : ℝ) ≤ Nat.card V := by
      exact_mod_cast Finite.card_subtype_le _
    change _ ≤ (A + η) * G.cycleRankOn (G.component v) + η * Nat.card V + C
    gcongr
  choose ρ hρ using hlay
  -- Order the vertices by their component, then by their place in its layout.
  set num := Finite.equivFin Γ.ConnectedComponent
  set key : V → ℕ ×ₗ ℕ := fun v =>
    toLex ((num (Γ.connectedComponentMk v) : ℕ),
      (ρ (Γ.connectedComponentMk v) ⟨v, rfl⟩ : ℕ)) with hkey
  have hpos (v : V) (K : Γ.ConnectedComponent) (hv : v ∈ K.supp) :
      (ρ (Γ.connectedComponentMk v) ⟨v, rfl⟩ : ℕ) = ρ K ⟨v, hv⟩ := by
    obtain rfl : Γ.connectedComponentMk v = K := hv
    rfl
  have hinj : key.Injective := by
    intro v w hvw
    simp only [hkey, toLex_inj, Prod.mk.injEq] at hvw
    have hK := num.injective (Fin.ext hvw.1)
    rw [hpos w _ hK.symm] at hvw
    exact congrArg Subtype.val ((ρ _).injective (Fin.ext hvw.2))
  obtain ⟨π, hπ⟩ := Layout.exists_lt_iff hinj
  refine ⟨π, fun t ht => ?_⟩
  -- The vertex processed at step `t`, its component `K`, and its place `p` in the layout of `K`.
  set v := π.symm ⟨t, ht⟩
  set K := Γ.connectedComponentMk v
  set p : ℕ := (ρ K ⟨v, rfl⟩ : ℕ)
  have hp : p < Nat.card K.supp := (ρ K ⟨v, rfl⟩).isLt
  have hK : G.edgeCut K.supp = ∅ := G.edgeCut_setOf_connectedComponentMk (· = K)
  -- The components before `K`.
  set B : Set V := {u | num (Γ.connectedComponentMk u) < num K}
  have hB : G.edgeCut B = ∅ := G.edgeCut_setOf_connectedComponentMk (num · < num K)
  have hBK (S : Set K.supp) : Disjoint B (Subtype.val '' S) := by
    refine disjoint_left.2 fun u hu ⟨u', _, hu'⟩ => ?_
    have hu : num (Γ.connectedComponentMk u) < num K := hu
    rw [← hu', u'.2] at hu
    exact lt_irrefl _ hu
  -- The first `t` vertices are the components before `K` and the first `p` vertices of `K`.
  have hinit : π.initial t = B ∪ Subtype.val '' (ρ K).initial p := by
    ext u
    rw [Layout.initial_eq_of_lt_iff hπ ht, mem_ofPred_eq, hkey, Prod.Lex.toLex_lt_toLex]
    simp only [Fin.val_fin_lt, Fin.val_inj, B, mem_union, mem_ofPred_eq, mem_image,
      Layout.mem_initial]
    refine or_congr_right ⟨fun ⟨hu, hlt⟩ => ?_, fun ⟨u', hu', hu'u⟩ => ?_⟩
    · obtain hu := num.injective hu
      exact ⟨⟨u, hu⟩, by rwa [← hpos u K hu], rfl⟩
    · subst hu'u
      refine ⟨congrArg num u'.2, ?_⟩
      rwa [hpos _ K u'.2]
  have hinit' : π.initial (t + 1) = B ∪ Subtype.val '' (ρ K).initial (p + 1) := by
    rw [π.initial_succ ht, hinit, (ρ K).initial_succ hp, image_insert_eq, union_insert]
    congr 1
    change v = ((ρ K).symm (ρ K ⟨v, rfl⟩) : V)
    rw [Equiv.symm_apply_apply]
  -- Both frontiers are frontiers of the layout of `K`.
  have hfront (q : ℕ) : G.edgeCut (B ∪ Subtype.val '' (ρ K).initial q) =
      Subtype.val '' (G.induce K.supp).frontier (ρ K) q := by
    rw [G.edgeCut_union_of_edgeCut_eq_empty hB (hBK _), G.edgeCut_image_val hK]
    rfl
  intro s hts hst
  obtain ⟨q, hq⟩ : ∃ q, G.frontier π s = Subtype.val '' (G.induce K.supp).frontier (ρ K) q := by
    rcases (show s = t ∨ s = t + 1 by omega) with rfl | rfl
    · exact ⟨p, by rw [Multigraph.frontier, hinit, hfront]⟩
    · exact ⟨p + 1, by rw [Multigraph.frontier, hinit', hfront]⟩
  rw [hq, ncard_image_of_injective _ Subtype.val_injective]
  exact ⟨fun _ ⟨e, _, he⟩ => he ▸ Or.inl e.2.1, hρ K q⟩

end Cslib.Circuits.Frontier
