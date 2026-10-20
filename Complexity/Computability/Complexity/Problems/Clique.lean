/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.IndependentSet
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Cliques

`Clique` is the set of graphs with a clique of a given number of their vertices [Arora and Barak,
Section 2.4][AroraBarak09]. A set of vertices is independent in a graph exactly when it is a clique
in the complement of the graph on its vertices (`Graph.compl`), so complementing the graph reduces
`IndependentSet` to `Clique` [Karp1972]. The verifier is `Cslib.Complexity.Graph.verifySubset` for
adjacency, an instance of the subset-witness verifier `Cslib.Complexity.subsetVerifier`.

## Main definitions

* `Cslib.Complexity.Clique`, `Cslib.Complexity.Graph.compl`.
* `Cslib.Complexity.Graph.cliqueNum`: the clique number.
* `Cslib.Complexity.Clique.verifier`.

## Main results

* `Cslib.Complexity.Graph.compl_mem_Clique_iff`: `(G.compl, m) ∈ Clique ↔ (G, m) ∈ IndependentSet`.
* `Cslib.Complexity.Graph.le_cliqueNum_iff`, `Cslib.Complexity.Graph.cliqueNum_compl`: the clique
  number is the largest target of `Clique`, and that of the complement is the independence number.
* `Cslib.Complexity.Graph.computableTidilyInPolyTime_compl`: complementing a graph on its declared
  vertices is polynomial-time.
* `Cslib.Complexity.Clique.mem_NP`: `Clique ∈ NP (encPair encGraph encNat)`.
* `Cslib.Complexity.polyTimeReducible_IndependentSet_Clique`: `IndependentSet` reduces to `Clique`
  in polynomial time.
* `Cslib.Complexity.Clique_npHard`: `Clique` is `NP`-hard.
* `Cslib.Complexity.Clique_npComplete`: `Clique` is `NP`-complete.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- The graphs with a clique of `m` of their vertices. -/
def Clique : Set (Graph × ℕ) :=
  {x | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.1.1) ∧ x.1.toSimpleGraph.IsNClique x.2 S}

namespace Graph

/-- The complement of a graph on its vertices: an edge between any two distinct vertices that are
not adjacent. -/
def compl (G : Graph) : Graph :=
  (G.1, G.1.flatMap fun u =>
    (G.1.filter fun v => decide (u ≠ v ∧ (u, v) ∉ G.2 ∧ (v, u) ∉ G.2)).map fun v => (u, v))

/-- On the vertices of a graph, adjacency in the complement is non-adjacency in the graph. -/
theorem compl_adj_iff {G : Graph} {u v : ℕ} (hu : u ∈ G.1) (hv : v ∈ G.1) :
    G.compl.toSimpleGraph.Adj u v ↔ u ≠ v ∧ ¬G.toSimpleGraph.Adj u v := by
  have hedge : ∀ {a b}, (a, b) ∈ G.compl.2 ↔ a ∈ G.1 ∧ b ∈ G.1 ∧
      (a ≠ b ∧ (a, b) ∉ G.2 ∧ (b, a) ∉ G.2) := by
    intro a b
    simp only [compl, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq,
      Prod.mk.injEq]
    constructor
    · rintro ⟨a', ha', b', ⟨hb', hne⟩, rfl, rfl⟩
      exact ⟨ha', hb', hne⟩
    · rintro ⟨ha, hb, hne⟩
      exact ⟨a, ha, b, ⟨hb, hne⟩, rfl, rfl⟩
  simp only [toSimpleGraph, SimpleGraph.fromRel_adj, ne_eq, hedge]
  constructor
  · rintro ⟨huv, ⟨-, -, -, h₁, h₂⟩ | ⟨-, -, -, h₁, h₂⟩⟩
    · exact ⟨huv, fun ⟨_, h⟩ => h.elim h₁ h₂⟩
    · exact ⟨huv, fun ⟨_, h⟩ => h.elim h₂ h₁⟩
  · rintro ⟨huv, h⟩
    refine ⟨huv, Or.inl ⟨hu, hv, huv, fun h₁ => h ⟨huv, Or.inl h₁⟩, fun h₂ => h ⟨huv, Or.inr h₂⟩⟩⟩

/-- **Independent sets are cliques of the complement.** -/
theorem compl_mem_Clique_iff (G : Graph) (m : ℕ) :
    (G.compl, m) ∈ Clique ↔ (G, m) ∈ IndependentSet := by
  refine exists_congr fun S => ?_
  simp only [compl]
  refine and_congr_right fun hS => ?_
  have hpair : (↑S : Set ℕ).Pairwise G.compl.toSimpleGraph.Adj ↔
      (↑S : Set ℕ).Pairwise fun u v => ¬G.toSimpleGraph.Adj u v := by
    refine ⟨fun h u hu v hv huv => ((compl_adj_iff (hS u hu) (hS v hv)).1 (h hu hv huv)).2,
      fun h u hu v hv huv => (compl_adj_iff (hS u hu) (hS v hv)).2 ⟨huv, h hu hv huv⟩⟩
  exact ⟨fun ⟨h₁, h₂⟩ => ⟨hpair.1 h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨hpair.2 h₁, h₂⟩⟩

/-- Complementing a graph on its declared vertices is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_compl :
    ComputableTidilyInPolyTime compl encGraph encGraph := by
  have hdec : ∀ (G : Graph) (u v : ℕ),
      decide (u ≠ v ∧ (u, v) ∉ G.2 ∧ (v, u) ∉ G.2) = (!decide (u = v) && !G.adjBool u v) := by
    intro G u v
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      adjBool_eq_false_iff, toSimpleGraph, SimpleGraph.fromRel_adj, ne_eq, not_and, not_or]
    tauto
  unfold compl
  simp_rw [hdec]
  unfold adjBool encGraph
  fun_prop

end Graph

namespace Clique

/-- The verifier for `Clique`: select distinct declared vertices from the certificate mask, check
that their count equals `m`, and check that every two distinct selected vertices are adjacent. -/
def verifier : (Graph × ℕ) × List Bool → Bool :=
  Graph.verifySubset Graph.adjBool

/-- `Clique.verifier` verifies `Clique` with certificates as long as the encoded instance. -/
theorem isVerifier :
    IsVerifier (encPair encGraph encNat) Polynomial.X verifier Clique := by
  have h := Graph.isVerifier_verifySubset (rel := Graph.adjBool)
    (P := fun G u v => G.toSimpleGraph.Adj u v)
    (fun G u v _ => by rw [Graph.adjBool_eq_true_iff])
  intro x
  simpa only [Clique, Set.mem_ofPred_eq, SimpleGraph.isNClique_iff, SimpleGraph.IsClique,
    verifier] using h x

/-- The `Clique` verifier is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_verifier :
    ComputableTidilyInPolyTime verifier
      (encPair (encPair encGraph encNat) encBits) encBool :=
  Graph.computableTidilyInPolyTime_verifySubset Graph.computableTidilyInPolyTime_adjBool

/-- `Clique` belongs to `NP`. -/
theorem mem_NP : Clique ∈ NP (encPair encGraph encNat) :=
  ⟨Polynomial.X, verifier, computableTidilyInPolyTime_verifier, isVerifier⟩

end Clique

/-- `IndependentSet` reduces to `Clique` in polynomial time by complementing the graph on its
declared vertices. -/
theorem polyTimeReducible_IndependentSet_Clique :
    PolyTimeReducible (encPair encGraph encNat) (encPair encGraph encNat) IndependentSet Clique :=
  ⟨fun x => (x.1.compl, x.2), by fun_prop, fun ⟨G, m⟩ => (Graph.compl_mem_Clique_iff G m).symm⟩

/-- `Clique` is `NP`-hard. -/
theorem Clique_npHard : NPHard (encPair encGraph encNat) Clique :=
  IndependentSet_npHard.trans polyTimeReducible_IndependentSet_Clique

/-- **`Clique` is NP-complete.** -/
theorem Clique_npComplete : NPComplete (encPair encGraph encNat) Clique :=
  ⟨Clique.mem_NP, Clique_npHard⟩

/-! ### The clique number -/

namespace Graph

/-- The **clique number** of a graph: the largest number of declared vertices that are pairwise
adjacent. -/
noncomputable def cliqueNum (G : Graph) : ℕ := sSup {k | (G, k) ∈ Clique}

variable {G : Graph} {k k' : ℕ}

/-- Fewer vertices of a clique form a clique. -/
theorem mem_Clique_of_le (h : (G, k) ∈ Clique) (hk : k' ≤ k) : (G, k') ∈ Clique := by
  obtain ⟨S, hSV, hS⟩ := h
  have hc : S.card = k := hS.card_eq
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (hc ▸ hk)
  exact ⟨T, fun v hv => hSV v (hTS hv), ⟨hS.isClique.subset (Finset.coe_subset.2 hTS), hT⟩⟩

/-- A clique has at most as many vertices as the distinct declared vertices. -/
theorem le_card_of_mem_Clique (h : (G, k) ∈ Clique) : k ≤ G.1.toFinset.card := by
  obtain ⟨S, hSV, hS⟩ := h
  have hc : S.card = k := hS.card_eq
  rw [← hc]
  exact Finset.card_le_card fun v hv => List.mem_toFinset.2 (hSV v hv)

/-- **The clique number is the largest target of `Clique`.** -/
theorem le_cliqueNum_iff : k ≤ G.cliqueNum ↔ (G, k) ∈ Clique := by
  have hbdd : BddAbove {k | (G, k) ∈ Clique} := ⟨_, fun _ => le_card_of_mem_Clique⟩
  have h0 : (G, 0) ∈ Clique := ⟨∅, by simp, ⟨by simp, rfl⟩⟩
  exact ⟨fun hk => mem_Clique_of_le (Nat.sSup_mem ⟨0, h0⟩ hbdd) hk,
    fun hk => le_csSup hbdd hk⟩

/-- **Cliques of the complement are independent sets**: the clique number of the complement on
the declared vertices is the independence number. -/
theorem cliqueNum_compl (G : Graph) : G.compl.cliqueNum = G.indepNum := by
  simp only [cliqueNum, indepNum, compl_mem_Clique_iff]

end Graph

end Cslib.Complexity
