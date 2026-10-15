/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Basic
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Unions and self-loops

Two regular multigraphs `G` and `H` on the same vertices, of degrees `|D|` and `|E|`, superpose
to a multigraph `G.union H` of degree `|D| + |E|`, whose edges at a vertex are those of `G`
followed by those of `H`. One step of its random walk is a step of `G` with probability
`|D| / (|D| + |E|)` and a step of `H` otherwise, so its walk operator is the weighted average of
theirs (`walk_union_apply`) and its spectral expansion is at most the weighted average of
theirs (`spectralExpansion_union_le`).

The simplest such `H` is `loops V E`, with a self-loop at every vertex for each label `i : E` and no
other edge, whose walk operator is the identity as soon as there is a label (`walk_loops`); with a
single label, `loops V Unit` is the multigraph whose tensor products with `H` are disjoint copies of
`H`. Superposing `loops V E` adds self-loops to `G` (`addLoops`). A few of them, as Dinur's
preprocessing adds, close at most the proportion `|E| / (|D| + |E|)` of the gap between the
spectral expansion and `1` (`spectralExpansion_addLoops_le`). As many self-loops as edges at each
vertex give the lazy graph `Cslib.RotationMap.lazy`, whose walk stays put half of the time.

Renaming the edge labels along an equivalence (`relabel`) changes neither the walk operator nor
the spectral expansion; it lets constructions with structured label types, such as `D ⊕ D`,
present their results with labels `Fin d`.

## Main definitions

* `Cslib.RotationMap.relabel`: the same multigraph with its edge labels renamed.
* `Cslib.RotationMap.union`: the superposition of two regular multigraphs on the same vertices.
* `Cslib.RotationMap.loops`: a self-loop at every vertex for each label.
* `Cslib.RotationMap.addLoops`: a regular multigraph with self-loops added at every vertex.

## Main results

* `Cslib.RotationMap.spectralExpansion_relabel`: relabelling preserves the spectral expansion.
* `Cslib.RotationMap.walk_union_apply`, `Cslib.RotationMap.spectralExpansion_union_le`: the walk
  operator and the spectral expansion of a union.
* `Cslib.RotationMap.walk_loops`: the walk operator of the self-loops is the identity.
* `Cslib.RotationMap.walk_addLoops_apply`, `Cslib.RotationMap.spectralExpansion_addLoops_le`:
  the same for adding self-loops.

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

end Cslib.RotationMap
