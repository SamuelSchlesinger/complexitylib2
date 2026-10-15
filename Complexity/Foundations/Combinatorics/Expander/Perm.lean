/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Cheeger

/-!
# Regular multigraphs of permutations

A family `σ : K → Equiv.Perm V` of permutations of the vertices gives a regular multigraph of degree
`2 |K|` (`ofPerms`): at every vertex `v`, each permutation `σ k` contributes an edge to `σ k v` and,
as the other end of the edge from `(σ k)⁻¹ v`, an edge to `(σ k)⁻¹ v`. Following an edge forwards
along `σ k` and then backwards along `(σ k)⁻¹` returns to its start, so the rotation map is an
involution. When the permutations are the actions of the generators of a group, this is the Schreier
graph of the action with respect to the generators and their inverses
[Hoory, Linial and Wigderson, Section 11.1.2][HooryLinialWigderson2006].

The edges leaving a set `S` of vertices are counted exactly by how many points of `S` each
permutation moves out of `S`: `σ k` moves as many points of `S` out of `S` as its inverse does, and
each such point is the start of an edge leaving `S` (`card_interedges_compl_ofPerms`). So if every
set of at most half of the vertices has a constant fraction of its points moved out of it by the
permutations, the multigraph is an edge expander (`le_edgeExpansion_ofPerms`). Random permutations
have this property (`Cslib.exists_perms_card_le_mul_card_filter_notMem`): their multigraph is the
permutation model of random regular graphs
[Hoory, Linial and Wigderson, Section 7.2.1][HooryLinialWigderson2006], and random regular graphs
are expanders [Hoory, Linial and Wigderson, Theorem 4.16][HooryLinialWigderson2006]
[Arora and Barak, Chapter 21][AroraBarak09].

## Main definitions

* `Cslib.RotationMap.ofPerms`: the regular multigraph of a family of permutations.

## Main results

* `Cslib.RotationMap.card_interedges_compl_ofPerms`: the edges leaving a set count the points the
  permutations move out of it, twice.
* `Cslib.RotationMap.le_edgeExpansion_ofPerms`: a lower bound on these counts for every set of at
  most half of the vertices bounds the edge expansion.

## References

* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset
open scoped BigOperators

variable {V K : Type*}

/-- The regular multigraph of a family `σ : K → Equiv.Perm V` of permutations, of degree `2 |K|`, as
in the permutation model of random regular graphs
[Hoory, Linial and Wigderson, Section 7.2.1][HooryLinialWigderson2006]: the edge `(k, false)` at `v`
leads to `σ k v`, where it is the edge `(k, true)`, which leads back along the inverse permutation.
-/
def ofPerms (σ : K → Equiv.Perm V) : RotationMap V (K × Bool) where
  rot p := bif p.2.2 then ((σ p.2.1).symm p.1, (p.2.1, false)) else (σ p.2.1 p.1, (p.2.1, true))
  rot_involutive := by
    rintro ⟨v, k, _ | _⟩ <;> simp

variable (σ : K → Equiv.Perm V)

/-- The rotation map of `ofPerms σ` on a forward edge. -/
@[simp]
theorem rot_ofPerms_false (v : V) (k : K) :
    (ofPerms σ).rot (v, (k, false)) = (σ k v, (k, true)) :=
  rfl

/-- The rotation map of `ofPerms σ` on a backward edge. -/
@[simp]
theorem rot_ofPerms_true (v : V) (k : K) :
    (ofPerms σ).rot (v, (k, true)) = ((σ k).symm v, (k, false)) :=
  rfl

/-- The forward edge labelled `k` at `v` leads to `σ k v`. -/
@[simp]
theorem neighbor_ofPerms_false (v : V) (k : K) : (ofPerms σ).neighbor v (k, false) = σ k v :=
  rfl

/-- The backward edge labelled `k` at `v` leads to `(σ k)⁻¹ v`. -/
@[simp]
theorem neighbor_ofPerms_true (v : V) (k : K) :
    (ofPerms σ).neighbor v (k, true) = (σ k).symm v :=
  rfl

/-- A permutation moves as many points of a finite set out of the set as its inverse does. -/
private theorem card_filter_symm_apply_notMem [DecidableEq V] (τ : Equiv.Perm V)
    (S : Finset V) : #{v ∈ S | τ.symm v ∉ S} = #{v ∈ S | τ v ∉ S} := by
  have h : #{v ∈ S | τ.symm v ∈ S} = #{v ∈ S | τ v ∈ S} := by
    refine card_nbij' τ.symm τ (fun v hv ↦ ?_) (fun v hv ↦ ?_) (fun v _ ↦ by simp)
      (fun v _ ↦ by simp) <;>
    · simp only [coe_filter] at hv ⊢
      simpa using hv.symm
  have h₁ := card_filter_add_card_filter_not (s := S) fun v ↦ τ.symm v ∈ S
  have h₂ := card_filter_add_card_filter_not (s := S) fun v ↦ τ v ∈ S
  omega

variable [Fintype V] [DecidableEq V] [Fintype K]

/-- **The edges leaving a set** in the multigraph of `σ`: each permutation `σ k` contributes twice
the number of points of `S` it moves out of `S`, once along `σ k` and once along its inverse. -/
theorem card_interedges_compl_ofPerms (S : Finset V) :
    #((ofPerms σ).interedges S Sᶜ) = 2 * ∑ k, #{v ∈ S | σ k v ∉ S} := by
  rw [interedges, card_filter, sum_product, mul_sum]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, neighbor_ofPerms_false,
    neighbor_ofPerms_true, mem_compl]
  rw [sum_comm]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [sum_add_distrib, two_mul]
  nth_rw 1 [← card_filter_symm_apply_notMem (σ k) S]
  rw [card_filter, card_filter]
  rfl

/-- **Edge expansion from moved points**: on at least two vertices, if the permutations together
move at least `c |S|` points of every set `S` of at most half of the vertices out of `S`, then the
edge expansion of their multigraph is at least `2 c`. -/
theorem le_edgeExpansion_ofPerms [Nontrivial V] {c : ℝ}
    (h : ∀ S : Finset V, 2 * #S ≤ Fintype.card V → c * #S ≤ ∑ k, #{v ∈ S | σ k v ∉ S}) :
    2 * c ≤ (ofPerms σ).edgeExpansion := by
  refine (ofPerms σ).le_edgeExpansion_iff.2 fun S hS ↦ ?_
  rw [card_interedges_compl_ofPerms]
  have := h S hS
  push_cast at this ⊢
  linarith

end Cslib.RotationMap
