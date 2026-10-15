/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Cheeger
public import Complexity.Foundations.Combinatorics.Expander.Products
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Unions, self-loops and the lazy walk

Two regular multigraphs `G` and `H` on the same vertices, of degrees `|D|` and `|E|`, superpose
to a multigraph `G.union H` of degree `|D| + |E|`, whose edges at a vertex are those of `G`
followed by those of `H`. One step of its random walk is a step of `G` with probability
`|D| / (|D| + |E|)` and a step of `H` otherwise, so its walk operator is the weighted average of
theirs (`walk_union_apply`) and its spectral expansion is at most the weighted average of
theirs (`spectralExpansion_union_le`).

The simplest such `H` is `loops V E`, with a self-loop at every vertex for each label `i : E` and no
other edge, whose walk operator is the identity; `loops V Unit` is `refl V`. Superposing it adds
self-loops to `G` (`addLoops`); with as many self-loops as edges at each vertex this is the **lazy
graph** `G.lazy`, whose walk stays put with probability `1 / 2` and otherwise takes a step of the
walk on `G`. Its walk operator `(1 + G.walk) / 2` is positive semidefinite, so Cheeger's inequality
[Hoory, Linial and Wigderson, Theorem 2.4][HooryLinialWigderson2006] bounds its spectral expansion
by the edge expansion of `G`: `λ(G.lazy) ≤ 1 - h(G)² / (4 |D|²)`
(`spectralExpansion_lazy_le_one_sub_edgeExpansion_sq_div`). This turns edge expanders into spectral
expanders, even those, such as bipartite ones, whose walk operators have the eigenvalue `-1`.

Renaming the edge labels along an equivalence (`relabel`) changes neither the walk operator nor
the spectral expansion; it lets constructions with structured label types, such as `D ⊕ D`,
present their results with labels `Fin d`.

## Main definitions

* `Cslib.RotationMap.relabel`: the same multigraph with its edge labels renamed.
* `Cslib.RotationMap.union`: the superposition of two regular multigraphs on the same vertices.
* `Cslib.RotationMap.loops`: a self-loop at every vertex for each label.
* `Cslib.RotationMap.addLoops`: a regular multigraph with self-loops added at every vertex.
* `Cslib.RotationMap.lazy`: the lazy graph, with a self-loop for every edge at each vertex.

## Main results

* `Cslib.RotationMap.spectralExpansion_relabel`: relabelling preserves the spectral expansion.
* `Cslib.RotationMap.walk_union_apply`, `Cslib.RotationMap.spectralExpansion_union_le`: the walk
  operator and the spectral expansion of a union.
* `Cslib.RotationMap.walk_addLoops_apply`, `Cslib.RotationMap.spectralExpansion_addLoops_le`:
  the same for adding self-loops.
* `Cslib.RotationMap.walk_lazy_apply`: the lazy walk is `(f + G.walk f) / 2`.
* `Cslib.RotationMap.spectralExpansion_lazy_le_one_add_secondEigenvalue_div_two`:
  `λ(G.lazy) ≤ (1 + λ₂(G)) / 2`.
* `Cslib.RotationMap.spectralExpansion_lazy_le_one_sub_edgeExpansion_sq_div`,
  `Cslib.RotationMap.spectralExpansion_lazy_le_of_mul_card_le_card_interedges_compl`: edge
  expansion bounds the spectral expansion of the lazy graph.

## References

* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset
open scoped BigOperators

variable {V D E : Type*}

section Relabel

/-- The same multigraph with its edge labels renamed along `e : D ≃ E`: the `e i`-th edge at a
vertex of `G.relabel e` is its `i`-th edge in `G`. -/
def relabel (G : RotationMap V D) (e : D ≃ E) : RotationMap V E where
  rot := Prod.map id e ∘ G.rot ∘ Prod.map id e.symm
  rot_involutive p := by
    have h (q : V × D) : Prod.map id e.symm (Prod.map id e q) = q :=
      Prod.ext rfl (e.symm_apply_apply q.2)
    simp only [Function.comp_apply, h, rot_rot]
    exact Prod.ext rfl (e.apply_symm_apply p.2)

/-- The rotation map of a relabelled multigraph. -/
@[simp]
theorem rot_relabel (G : RotationMap V D) (e : D ≃ E) (p : V × E) :
    (G.relabel e).rot p = Prod.map id e (G.rot (p.1, e.symm p.2)) :=
  rfl

/-- The `i`-th neighbor in a relabelled multigraph is the `e.symm i`-th neighbor in the
original. -/
@[simp]
theorem neighbor_relabel (G : RotationMap V D) (e : D ≃ E) (v : V) (i : E) :
    (G.relabel e).neighbor v i = G.neighbor v (e.symm i) :=
  rfl

/-- Relabelling the edges does not change the walk operator. -/
@[simp]
theorem walk_relabel [Fintype D] [Fintype E] (G : RotationMap V D) (e : D ≃ E) :
    (G.relabel e).walk = G.walk :=
  LinearMap.ext fun _ ↦ funext fun _ ↦ Fintype.expect_equiv e.symm _ _ fun _ ↦ rfl

/-- Two regular multigraphs on the same vertices with the same walk operator have the same
spectral expansion, whatever their edge labels. -/
theorem spectralExpansion_eq_of_walk_eq [Fintype V] [Fintype D] [Fintype E]
    {G : RotationMap V D} {H : RotationMap V E} (h : G.walk = H.walk) :
    G.spectralExpansion = H.spectralExpansion := by
  simp only [spectralExpansion, h]

/-- Relabelling the edges does not change the spectral expansion. -/
@[simp]
theorem spectralExpansion_relabel [Fintype V] [Fintype D] [Fintype E] (G : RotationMap V D)
    (e : D ≃ E) : (G.relabel e).spectralExpansion = G.spectralExpansion :=
  spectralExpansion_eq_of_walk_eq (G.walk_relabel e)

end Relabel

section Union

/-- The **union** of two regular multigraphs `G` and `H` on the same vertices: the multigraph whose
edges at a vertex are those of `G`, labelled by `Sum.inl`, followed by those of `H`, labelled by
`Sum.inr`. Its degree is the sum of their degrees. -/
def union (G : RotationMap V D) (H : RotationMap V E) : RotationMap V (D ⊕ E) where
  rot p := p.2.elim (fun i ↦ Prod.map id Sum.inl (G.rot (p.1, i)))
    fun j ↦ Prod.map id Sum.inr (H.rot (p.1, j))
  rot_involutive := by
    rintro ⟨v, i | j⟩ <;> simp

variable (G : RotationMap V D) (H : RotationMap V E)

/-- The rotation map of a union on an edge of the first multigraph. -/
@[simp]
theorem rot_union_inl (v : V) (i : D) :
    (G.union H).rot (v, .inl i) = Prod.map id Sum.inl (G.rot (v, i)) :=
  rfl

/-- The rotation map of a union on an edge of the second multigraph. -/
@[simp]
theorem rot_union_inr (v : V) (j : E) :
    (G.union H).rot (v, .inr j) = Prod.map id Sum.inr (H.rot (v, j)) :=
  rfl

/-- The neighbors of a vertex in a union along the edges of the first multigraph. -/
@[simp]
theorem neighbor_union_inl (v : V) (i : D) : (G.union H).neighbor v (.inl i) = G.neighbor v i :=
  rfl

/-- The neighbors of a vertex in a union along the edges of the second multigraph. -/
@[simp]
theorem neighbor_union_inr (v : V) (j : E) : (G.union H).neighbor v (.inr j) = H.neighbor v j :=
  rfl

variable [Fintype D] [Fintype E]

/-- The walk operator of a union is the average of the walk operators of the two multigraphs,
weighted by their degrees. -/
theorem walk_union_apply (f : V → ℝ) (v : V) :
    (G.union H).walk f v =
      (Fintype.card D * G.walk f v + Fintype.card E * H.walk f v) /
        (Fintype.card D + Fintype.card E) := by
  rw [walk_apply, walk_apply, walk_apply, Fintype.expect_eq_sum_div_card, Fintype.sum_sum_type,
    Fintype.card_mul_expect, Fintype.card_mul_expect, Fintype.card_sum, Nat.cast_add]
  rfl

/-- If `𝔼 X² ≤ α² A` and `𝔼 Y² ≤ β² A`, then `𝔼 (a X + b Y)² ≤ (a α + b β)² A` for `a, b ≥ 0`:
the triangle inequality for the norm `√(𝔼 f²)`, squared. -/
private theorem expect_add_sq_le [Fintype V] {X Y : V → ℝ} {a b α β A : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hA : 0 ≤ A) (hX : 𝔼 v, X v ^ 2 ≤ α ^ 2 * A)
    (hY : 𝔼 v, Y v ^ 2 ≤ β ^ 2 * A) :
    𝔼 v, (a * X v + b * Y v) ^ 2 ≤ (a * α + b * β) ^ 2 * A := by
  have hXY : 𝔼 v, X v * Y v ≤ α * β * A := by
    refine (le_abs_self _).trans (abs_le_of_sq_le_sq ?_ (by positivity))
    calc (𝔼 v, X v * Y v) ^ 2 ≤ (𝔼 v, X v ^ 2) * 𝔼 v, Y v ^ 2 := expect_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ (α ^ 2 * A) * (β ^ 2 * A) :=
        mul_le_mul hX hY (expect_nonneg fun _ _ ↦ sq_nonneg _) (by positivity)
      _ = (α * β * A) ^ 2 := by ring
  calc 𝔼 v, (a * X v + b * Y v) ^ 2
      = a ^ 2 * 𝔼 v, X v ^ 2 + 2 * a * b * 𝔼 v, X v * Y v + b ^ 2 * 𝔼 v, Y v ^ 2 := by
        simp only [mul_expect, ← expect_add_distrib]
        exact expect_congr rfl fun v _ ↦ by ring
    _ ≤ a ^ 2 * (α ^ 2 * A) + 2 * a * b * (α * β * A) + b ^ 2 * (β ^ 2 * A) := by gcongr
    _ = (a * α + b * β) ^ 2 * A := by ring

/-- **The spectral expansion of a union** is at most the average of the spectral expansions of
the two multigraphs, weighted by their degrees. -/
theorem spectralExpansion_union_le [Fintype V] :
    (G.union H).spectralExpansion ≤
      (Fintype.card D * G.spectralExpansion + Fintype.card E * H.spectralExpansion) /
        (Fintype.card D + Fintype.card E) := by
  have hG := G.spectralExpansion_nonneg
  have hH := H.spectralExpansion_nonneg
  refine spectralExpansion_le (by positivity) fun f hf ↦ ?_
  set d : ℝ := (Fintype.card D : ℝ)
  set e : ℝ := (Fintype.card E : ℝ)
  rcases (by positivity : (0 : ℝ) ≤ d + e).eq_or_lt with hde | hde
  · have hw (v : V) : (G.union H).walk f v = 0 := by rw [walk_union_apply, ← hde, div_zero]
    simp only [hw, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, expect_const_zero]
    positivity
  have hw (v : V) : (G.union H).walk f v = d / (d + e) * G.walk f v + e / (d + e) * H.walk f v := by
    rw [walk_union_apply]
    ring
  simp only [hw]
  refine (expect_add_sq_le (by positivity) (by positivity) hG hH
    (expect_nonneg fun _ _ ↦ sq_nonneg _) (G.expect_walk_sq_le_spectralExpansion_sq_mul hf)
    (H.expect_walk_sq_le_spectralExpansion_sq_mul hf)).trans_eq ?_
  ring

end Union

section Loops

/-- The multigraph on `V` with a self-loop at every vertex for each label `i : E`, and no other
edge: its rotation map is the identity. -/
def loops (V E : Type*) : RotationMap V E where
  rot := id
  rot_involutive _ := rfl

/-- The rotation map of `loops V E` is the identity. -/
@[simp]
theorem rot_loops (p : V × E) : (loops V E).rot p = p :=
  rfl

/-- Every edge of `loops V E` is a self-loop. -/
@[simp]
theorem neighbor_loops (v : V) (i : E) : (loops V E).neighbor v i = v :=
  rfl

/-- One self-loop at every vertex is `refl V`. -/
theorem loops_unit : loops V Unit = refl V :=
  rfl

/-- With at least one self-loop at every vertex, the walk operator of `loops V E` is the
identity. -/
@[simp]
theorem walk_loops [Fintype E] [Nonempty E] : (loops V E).walk = LinearMap.id :=
  LinearMap.ext fun f ↦ funext fun v ↦ by simp [walk_apply]

/-- `G` with a self-loop added at every vertex for each label `i : E`: the union of `G` with
`loops V E`. -/
def addLoops (G : RotationMap V D) (E : Type*) : RotationMap V (D ⊕ E) :=
  G.union (loops V E)

variable (G : RotationMap V D)

/-- The neighbors of a vertex in `G.addLoops E` along the edges of `G`. -/
@[simp]
theorem neighbor_addLoops_inl (v : V) (i : D) :
    (G.addLoops E).neighbor v (.inl i) = G.neighbor v i :=
  rfl

/-- The added edges of `G.addLoops E` are self-loops. -/
@[simp]
theorem neighbor_addLoops_inr (v : V) (j : E) : (G.addLoops E).neighbor v (.inr j) = v :=
  rfl

variable [Fintype D] [Fintype E]

/-- The walk operator of `G` with `|E|` self-loops added at every vertex stays put with
probability `|E| / (|D| + |E|)` and otherwise takes a step of the walk on `G`. -/
theorem walk_addLoops_apply (f : V → ℝ) (v : V) :
    (G.addLoops E).walk f v =
      (Fintype.card D * G.walk f v + Fintype.card E * f v) / (Fintype.card D + Fintype.card E) := by
  rw [addLoops, walk_union_apply]
  rcases isEmpty_or_nonempty E with hE | hE
  · simp [Fintype.card_eq_zero]
  · rw [walk_loops, LinearMap.id_apply]

/-- **Adding self-loops** to a multigraph of degree `|D|`, `|E|` at every vertex, gives spectral
expansion at most `(|D| λ(G) + |E|) / (|D| + |E|)`. -/
theorem spectralExpansion_addLoops_le [Fintype V] :
    (G.addLoops E).spectralExpansion ≤
      (Fintype.card D * G.spectralExpansion + Fintype.card E) /
        (Fintype.card D + Fintype.card E) := by
  refine (G.spectralExpansion_union_le (loops V E)).trans ?_
  have := (loops V E).spectralExpansion_le_one
  gcongr
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) this

end Loops

section Lazy

/-- The **lazy graph** of `G`: `G` with a self-loop added at every vertex for each of its edges
there. Its random walk stays put with probability `1 / 2` and otherwise takes a step of the
random walk on `G`. -/
def lazy (G : RotationMap V D) : RotationMap V (D ⊕ D) :=
  G.addLoops D

variable (G : RotationMap V D) [Fintype D]

/-- The walk operator of the lazy graph is `(1 + G.walk) / 2`. -/
theorem walk_lazy_apply [Nonempty D] (f : V → ℝ) (v : V) :
    G.lazy.walk f v = (f v + G.walk f v) / 2 := by
  rw [lazy, walk_addLoops_apply]
  have : (0 : ℝ) < Fintype.card D := Nat.cast_pos.2 Fintype.card_pos
  field_simp
  ring

variable [Fintype V]

/-- **The spectral expansion of the lazy graph** is at most `(1 + λ₂(G)) / 2`: its walk operator
is positive semidefinite, so its spectral expansion is its second eigenvalue. -/
theorem spectralExpansion_lazy_le_one_add_secondEigenvalue_div_two :
    G.lazy.spectralExpansion ≤ (1 + G.secondEigenvalue) / 2 := by
  rcases isEmpty_or_nonempty D with hD | hD
  · have : G.lazy.spectralExpansion ≤ 0 :=
      spectralExpansion_le le_rfl fun f _ ↦ by simp [walk_apply]
    linarith [G.neg_one_le_secondEigenvalue]
  · exact G.spectralExpansion_le_one_add_secondEigenvalue_div_two G.lazy G.walk_lazy_apply

/-- **Edge expansion bounds the spectral expansion of the lazy graph**
[Hoory, Linial and Wigderson, Theorem 2.4][HooryLinialWigderson2006]:
`λ(G.lazy) ≤ 1 - h(G)² / (4 |D|²)`. -/
theorem spectralExpansion_lazy_le_one_sub_edgeExpansion_sq_div [DecidableEq V] :
    G.lazy.spectralExpansion ≤ 1 - G.edgeExpansion ^ 2 / (4 * Fintype.card D ^ 2) := by
  rcases isEmpty_or_nonempty D with hD | hD
  · simpa [Fintype.card_eq_zero] using G.lazy.spectralExpansion_le_one
  · exact G.spectralExpansion_le_one_sub_edgeExpansion_sq_div G.lazy G.walk_lazy_apply

/-- **Edge expansion bounds the spectral expansion of the lazy graph**
[Hoory, Linial and Wigderson, Theorem 2.4][HooryLinialWigderson2006]: on at least two vertices, if
`c ≥ 0` and at least `c |S|` edges leave every set `S` of at most half of the vertices, then
`λ(G.lazy) ≤ 1 - c² / (4 |D|²)`. -/
theorem spectralExpansion_lazy_le_of_mul_card_le_card_interedges_compl [DecidableEq V]
    [Nontrivial V] {c : ℝ} (hc₀ : 0 ≤ c)
    (hc : ∀ S : Finset V, 2 * #S ≤ Fintype.card V → c * #S ≤ #(G.interedges S Sᶜ)) :
    G.lazy.spectralExpansion ≤ 1 - c ^ 2 / (4 * Fintype.card D ^ 2) := by
  refine G.spectralExpansion_lazy_le_one_sub_edgeExpansion_sq_div.trans ?_
  have := G.le_edgeExpansion_iff.2 hc
  gcongr

end Lazy

end Cslib.RotationMap
