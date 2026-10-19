/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.Parity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.BooleanRing

/-!
# Tseitin formulas

A finite multigraph on the vertices `V` with edges `E`, parallel edges and self-loops allowed, is
given here by the map `ends : E → Sym2 V` sending each edge to its unordered pair of ends; a
self-loop has equal ends. Given a *charge* `χ v` for every vertex `v`, the **Tseitin formula**
`CNF.tseitin ends χ` [Tseitin][Tseitin1983] [Urquhart][Urquhart1987] has a variable for each edge
and says, for every vertex `v`, that the parity of the edges at `v` is the charge of `v`. A
self-loop at `v` would count twice towards the parity of `v`, so it does not count at all; the
parity of `v` is that of the edges at `v` that are not self-loops (`Tseitin.incidence`), and the
constraint is expressed by the formula `CNF.parityOnEq` with a clause per assignment to those edges
of the wrong parity. A vertex with `d` edges other than self-loops thus contributes at most `2 ^ d`
clauses of `d` literals each. Relabelling the edges along an equivalence changes none of the
quantities below (`Tseitin.card_incidence_comp`, `Tseitin.expansion_comp`, ...).

Every edge other than a self-loop is at exactly two vertices, so summing the constraints of all
vertices gives `0 = ∑ χ`: if the total charge is odd, the Tseitin formula is unsatisfiable
(`CNF.not_satisfiable_tseitin`). On a connected multigraph the converse holds, and more: the
constraints of all vertices but one are satisfiable, whatever the charges
(`Tseitin.exists_forall_mem_parityOn_incidence_eq`). Flipping the value of an edge flips the
parities of its two ends, so flipping the edges of a path flips the parities of its two ends only;
combining such flips moves the parities to any target, up to the vertex left out.

These facts underlie the resolution lower bounds for Tseitin formulas on expanders
(`Complexity/Logics/Propositional/Resolution/Tseitin.lean`). The relevant measure of expansion is
`Tseitin.expansion`, the least number of edges between a set of between a third and two thirds of
the vertices and its complement [Ben-Sasson and Wigderson][BenSassonWigderson2001].

## Main definitions

* `Cslib.Logic.PL.Tseitin.graph`: the simple graph underlying a multigraph.
* `Cslib.Logic.PL.Tseitin.incidence`: the edges at a vertex other than self-loops.
* `Cslib.Logic.PL.Tseitin.boundary`: the edges between a set of vertices and its complement.
* `Cslib.Logic.PL.Tseitin.expansion`: the expansion `e(G)` of Ben-Sasson and Wigderson.
* `Cslib.Logic.PL.CNF.tseitin`: the Tseitin formula of a multigraph with charges.

## Main results

* `Cslib.Logic.PL.CNF.eval_tseitin_eq_true_iff`: the semantics of Tseitin formulas.
* `Cslib.Logic.PL.CNF.not_satisfiable_tseitin`: Tseitin formulas with odd total charge are
  unsatisfiable.
* `Cslib.Logic.PL.CNF.satisfiable_tseitin_iff`: on a connected multigraph, the Tseitin formula is
  satisfiable exactly when the total charge is even.
* `Cslib.Logic.PL.Tseitin.exists_forall_mem_parityOn_incidence_eq`: on a connected multigraph, the
  constraints of the vertices of any set other than the set of all vertices are satisfiable.
* `Cslib.Logic.PL.Tseitin.connected_graph_iff`: a multigraph is connected exactly when an edge
  leaves every nonempty set of vertices other than the set of all vertices.
* `Cslib.Logic.PL.Tseitin.le_expansion_iff`: the characterization of `e(G)`.
* `Cslib.Logic.PL.CNF.length_le_of_mem_tseitin`, `Cslib.Logic.PL.CNF.length_tseitin_le`: the
  clauses of a Tseitin formula have at most as many literals as a vertex has edges, and there are
  at most `|V| 2 ^ k` of them when every vertex has at most `k` edges.

## References

* [G. S. Tseitin, *On the complexity of derivation in propositional calculus*][Tseitin1983]
* [A. Urquhart, *Hard examples for resolution*][Urquhart1987]
* [E. Ben-Sasson, A. Wigderson, *Short proofs are narrow—resolution made
  simple*][BenSassonWigderson2001]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Chapter 18][Jukna2012]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Finset Function

variable {V E E' : Type*}

namespace Tseitin

/-! ### Multigraphs -/

section Graph

variable (ends : E → Sym2 V)

/-- The simple graph underlying the multigraph `ends`: distinct vertices are adjacent when an edge
joins them. Self-loops are dropped and parallel edges merged. -/
def graph : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (Set.range ends)

variable {ends} in
theorem graph_adj {u v : V} : (graph ends).Adj u v ↔ u ≠ v ∧ ∃ e, ends e = s(u, v) := by
  rw [graph, SimpleGraph.fromEdgeSet_adj, Set.mem_range, and_comm]

/-- Relabelling the edges does not change the underlying simple graph. -/
theorem graph_comp (f : E' ≃ E) : graph (ends ∘ f) = graph ends := by
  rw [graph, graph, Set.range_comp, f.range_eq_univ, Set.image_univ]

variable [Fintype E] [DecidableEq V]

/-- The edges at `v` other than self-loops: the edges whose values count towards the parity of
`v`. -/
def incidence (v : V) : Finset E :=
  {e | v ∈ ends e ∧ ¬(ends e).IsDiag}

variable {ends} in
@[simp] theorem mem_incidence {v : V} {e : E} :
    e ∈ incidence ends v ↔ v ∈ ends e ∧ ¬(ends e).IsDiag := by
  simp [incidence]

variable {ends} in
/-- An edge with ends `a` and `b` is at `v`, and not a self-loop, when `v` is one of its ends and
`a ≠ b`. -/
theorem mem_incidence_of_ends_eq {v a b : V} {e : E} (h : ends e = s(a, b)) :
    e ∈ incidence ends v ↔ (v = a ∨ v = b) ∧ a ≠ b := by
  rw [mem_incidence, h, Sym2.mem_iff, Sym2.mk_isDiag_iff]

/-- Relabelling the edges does not change the number of edges at a vertex. -/
theorem card_incidence_comp [Fintype E'] (f : E' ≃ E) (v : V) :
    #(incidence (ends ∘ f) v) = #(incidence ends v) :=
  card_equiv f fun _ => by simp

variable [Fintype V]

/-- The edges between `S` and its complement. -/
def boundary (S : Finset V) : Finset E :=
  {e | ∃ v ∈ S, ∃ w ∈ Sᶜ, ends e = s(v, w)}

variable {ends} in
theorem mem_boundary {S : Finset V} {e : E} :
    e ∈ boundary ends S ↔ ∃ v ∈ S, ∃ w ∈ Sᶜ, ends e = s(v, w) := by
  simp only [boundary, mem_filter, mem_univ, true_and]

/-- The edges between a set and its complement are those between the complement and the set. -/
theorem boundary_compl (S : Finset V) : boundary ends Sᶜ = boundary ends S := by
  ext e
  simp only [mem_boundary, compl_compl]
  exact ⟨fun ⟨v, hv, w, hw, h⟩ => ⟨w, hw, v, hv, h.trans Sym2.eq_swap⟩,
    fun ⟨v, hv, w, hw, h⟩ => ⟨w, hw, v, hv, h.trans Sym2.eq_swap⟩⟩

/-- Relabelling the edges does not change the number of edges leaving a set. -/
theorem card_boundary_comp [Fintype E'] (f : E' ≃ E) (S : Finset V) :
    #(boundary (ends ∘ f) S) = #(boundary ends S) :=
  card_equiv f fun _ => by simp [mem_boundary]

/-- The **expansion** `e(G)` of the multigraph `ends`
[Ben-Sasson and Wigderson][BenSassonWigderson2001]: the least number of edges
between a set `S` of vertices with `|V| / 3 ≤ |S| ≤ 2 |V| / 3` and its complement. With fewer than
two vertices there is no such nonempty set; then `e(G) = 0` by convention. -/
noncomputable def expansion : ℕ :=
  sInf {k | ∃ S : Finset V, Fintype.card V ≤ 3 * #S ∧ 3 * #S ≤ 2 * Fintype.card V ∧
    #(boundary ends S) = k}

/-- `e(G)` is at most the number of edges leaving any set of between a third and two thirds of
the vertices. -/
theorem expansion_le_card_boundary {S : Finset V} (h₁ : Fintype.card V ≤ 3 * #S)
    (h₂ : 3 * #S ≤ 2 * Fintype.card V) : expansion ends ≤ #(boundary ends S) :=
  Nat.sInf_le ⟨S, h₁, h₂, rfl⟩

/-- With at least two vertices, `e(G)` is the number of edges leaving some set of between a third
and two thirds of the vertices. -/
theorem exists_card_boundary_eq_expansion (hV : 2 ≤ Fintype.card V) :
    ∃ S : Finset V, Fintype.card V ≤ 3 * #S ∧ 3 * #S ≤ 2 * Fintype.card V ∧
      #(boundary ends S) = expansion ends := by
  obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset V))
    (n := (Fintype.card V + 2) / 3) (by rw [card_univ]; omega)
  exact Nat.sInf_mem (s := {k | ∃ S : Finset V, Fintype.card V ≤ 3 * #S ∧
    3 * #S ≤ 2 * Fintype.card V ∧ #(boundary ends S) = k}) ⟨_, S, by omega, by omega, rfl⟩

/-- With at least two vertices, `k ≤ e(G)` exactly when at least `k` edges leave every set of
between a third and two thirds of the vertices. -/
theorem le_expansion_iff (hV : 2 ≤ Fintype.card V) {k : ℕ} :
    k ≤ expansion ends ↔ ∀ S : Finset V, Fintype.card V ≤ 3 * #S →
      3 * #S ≤ 2 * Fintype.card V → k ≤ #(boundary ends S) := by
  refine ⟨fun h S h₁ h₂ => h.trans (expansion_le_card_boundary ends h₁ h₂), fun h => ?_⟩
  obtain ⟨S, h₁, h₂, hS⟩ := exists_card_boundary_eq_expansion ends hV
  exact hS ▸ h S h₁ h₂

/-- With at most one vertex, `e(G) = 0` by convention. -/
theorem expansion_eq_zero_of_subsingleton [Subsingleton V] : expansion ends = 0 := by
  have hV : Fintype.card V ≤ 1 := Fintype.card_le_one_iff_subsingleton.2 ‹_›
  rw [expansion, Nat.sInf_eq_zero]
  rcases Nat.lt_or_ge (Fintype.card V) 1 with h0 | h1
  · exact Or.inl ⟨∅, by omega, by simp, by simp [boundary]⟩
  · refine Or.inr (Set.eq_empty_of_forall_notMem fun k ⟨S, h₁, h₂, _⟩ => ?_)
    have := (card_le_univ S).trans hV
    omega

/-- Relabelling the edges does not change the expansion. -/
theorem expansion_comp [Fintype E'] (f : E' ≃ E) : expansion (ends ∘ f) = expansion ends := by
  simp only [expansion, card_boundary_comp]

/-- **Connectivity as a cut condition**: a multigraph is connected exactly when it has a vertex
and an edge leaves every nonempty set of vertices other than the set of all vertices. -/
theorem connected_graph_iff :
    (graph ends).Connected ↔
      Nonempty V ∧ ∀ S : Finset V, S.Nonempty → S ≠ univ → (boundary ends S).Nonempty := by
  classical
  refine ⟨fun hG => ⟨hG.nonempty, fun S ⟨u, hu⟩ hS => ?_⟩, fun ⟨hV, h⟩ => ?_⟩
  · -- a walk from inside `S` to outside crosses the boundary
    obtain ⟨w, hw⟩ : ∃ w, w ∉ S := by
      by_contra! h'
      exact hS (eq_univ_of_forall h')
    obtain ⟨p⟩ := hG.preconnected u w
    obtain ⟨d, -, hd₁, hd₂⟩ := p.exists_boundary_dart (S : Set V) hu hw
    obtain ⟨-, e, he⟩ := graph_adj.1 d.adj
    exact ⟨e, mem_boundary.2 ⟨_, hd₁, _, mem_compl.2 hd₂, he⟩⟩
  · -- the vertices reachable from a vertex have no edge leaving them
    obtain ⟨u⟩ := hV
    refine (SimpleGraph.connected_iff_exists_forall_reachable _).2 ⟨u, fun w => ?_⟩
    let R : Finset V := {w | (graph ends).Reachable u w}
    suffices hR : R = univ by
      have hw : w ∈ R := by rw [hR]; exact mem_univ w
      simpa [R] using hw
    by_contra hR
    obtain ⟨e, he⟩ := h R ⟨u, by simp [R]⟩ hR
    obtain ⟨a, ha, b, hb, hab⟩ := mem_boundary.1 he
    have ha' : (graph ends).Reachable u a := by simpa [R] using ha
    have hne : a ≠ b := fun h => mem_compl.1 hb (h ▸ ha)
    exact mem_compl.1 hb (by simpa [R] using ha'.trans (graph_adj.2 ⟨hne, e, hab⟩).reachable)

end Graph

/-! ### Parities at the vertices -/

section Parity

variable {ends : E → Sym2 V} [Fintype E] [DecidableEq V]

/-- Flipping the value of an edge flips the parities at its ends, and only there. -/
theorem parityOn_incidence_update_not [DecidableEq E] (σ : E → Bool) (e : E) (v : V) :
    parityOn (incidence ends v) (update σ e !σ e) =
      (decide (e ∈ incidence ends v) ^^ parityOn (incidence ends v) σ) := by
  by_cases he : e ∈ incidence ends v
  · rw [parityOn_update_not he, decide_eq_true he, Bool.true_xor]
  · rw [parityOn_update_of_notMem he, decide_eq_false he, Bool.false_xor]

/-- On a connected multigraph, the parities at any two vertices `u` and `w`, and nowhere else, can
be flipped: some assignment has parity `1` exactly at `u` and `w` (and nowhere if `u = w`). -/
theorem exists_forall_parityOn_incidence_eq_xor [Finite V] (hG : (graph ends).Connected)
    (u w : V) :
    ∃ τ : E → Bool, ∀ v, parityOn (incidence ends v) τ = (decide (v = u) ^^ decide (v = w)) := by
  classical
  have := Fintype.ofFinite V
  let R : Finset V :=
    {w | ∃ τ : E → Bool, ∀ v, parityOn (incidence ends v) τ = (decide (v = u) ^^ decide (v = w))}
  suffices hR : R = univ by
    have hw : w ∈ R := by rw [hR]; exact mem_univ w
    simpa [R] using hw
  by_contra hR
  have hu : u ∈ R := by
    simp only [R, mem_filter, mem_univ, true_and, Bool.xor_self]
    exact ⟨fun _ => false, fun v => by simp [parityOn]⟩
  obtain ⟨e, he⟩ := ((connected_graph_iff ends).1 hG).2 R ⟨u, hu⟩ hR
  obtain ⟨a, ha, b, hb, hab⟩ := mem_boundary.1 he
  obtain ⟨τ, hτ⟩ := by simpa [R] using ha
  have hne : a ≠ b := fun h => mem_compl.1 hb (h ▸ ha)
  -- flipping `e` moves the parity `1` from `a` to `b`
  have hb' : b ∈ R := by
    simp only [R, mem_filter, mem_univ, true_and]
    refine ⟨update τ e !τ e, fun v => ?_⟩
    rw [parityOn_incidence_update_not, hτ]
    simp only [mem_incidence_of_ends_eq hab]
    by_cases hva : v = a
    · subst hva
      simp [hne]
    · by_cases hvb : v = b
      · subst hvb
        simp [hva, hne]
      · simp [hva, hvb]
  exact mem_compl.1 hb hb'

variable [Fintype V]

/-- **The handshake argument**: the parities at all vertices of an assignment to the edges add up
to `0`, since every edge other than a self-loop is at exactly two vertices. -/
theorem parityOn_univ_parityOn_incidence (σ : E → Bool) :
    parityOn univ (fun v => parityOn (incidence ends v) σ) = false := by
  simp only [parityOn_eq_sum]
  rw [sum_comm' (t' := univ) (s' := fun e => {v | v ∈ ends e ∧ ¬(ends e).IsDiag}) (by simp)]
  refine sum_eq_zero fun e _ => ?_
  obtain ⟨a, b, hab⟩ : ∃ a b, ends e = s(a, b) := Sym2.ind (f := fun z => ∃ a b, z = s(a, b))
    (fun a b => ⟨a, b, rfl⟩) (ends e)
  by_cases h : a = b
  · rw [filter_false_of_mem fun v _ => by simp [hab, h], sum_empty]
  · rw [show ({v | v ∈ ends e ∧ ¬(ends e).IsDiag} : Finset V) = {a, b} by
      ext v
      simp [hab, h], sum_pair h, BooleanRing.add_self]

/-- An assignment satisfying the constraints of all vertices has even total charge. -/
theorem parityOn_univ_eq_false_of_forall {σ : E → Bool} {χ : V → Bool}
    (h : ∀ v, parityOn (incidence ends v) σ = χ v) : parityOn univ χ = false := by
  rw [← parityOn_univ_parityOn_incidence (ends := ends) σ]
  exact parityOn_congr fun v _ => (h v).symm

/-- On a connected multigraph, for every vertex `u` some assignment satisfies the constraints of
all vertices except possibly `u`: its parity at `v` is `χ v`, flipped at `u` when the total charge
is odd. -/
theorem exists_forall_parityOn_incidence_eq (hG : (graph ends).Connected) (χ : V → Bool) (u : V) :
    ∃ σ : E → Bool, ∀ v,
      parityOn (incidence ends v) σ = ((parityOn univ χ && decide (v = u)) ^^ χ v) := by
  choose τ hτ using exists_forall_parityOn_incidence_eq_xor hG u
  refine ⟨∑ w, if χ w then τ w else 0, fun v => ?_⟩
  have hite (b x : Bool) : (if b then x else 0) = b * x := by cases b <;> rfl
  have key : parityOn (incidence ends v) (∑ w, if χ w then τ w else 0) =
      ∑ w, χ w * (decide (v = u) + decide (v = w)) := by
    rw [← parityOnAddMonoidHom_apply, map_sum]
    refine sum_congr rfl fun w _ => ?_
    rw [apply_ite (parityOnAddMonoidHom _), map_zero, parityOnAddMonoidHom_apply, hτ, hite]
    rfl
  have hv : ∑ w, χ w * decide (v = w) = χ v := by
    rw [sum_eq_single v (fun w _ hw => by rw [decide_eq_false (Ne.symm hw)]; exact mul_zero _)
      (by simp), decide_eq_true rfl]
    exact mul_one _
  rw [key, parityOn_eq_sum]
  simp only [mul_add, sum_add_distrib, ← sum_mul, hv]
  rfl

/-- **Satisfiable subsystems**: on a connected multigraph, the constraints of the vertices of any
set other than the set of all vertices are satisfiable, whatever the charges. -/
theorem exists_forall_mem_parityOn_incidence_eq (hG : (graph ends).Connected) (χ : V → Bool)
    {S : Finset V} (hS : S ≠ univ) :
    ∃ σ : E → Bool, ∀ v ∈ S, parityOn (incidence ends v) σ = χ v := by
  obtain ⟨u, hu⟩ : ∃ u, u ∉ S := by
    by_contra! h'
    exact hS (eq_univ_of_forall h')
  obtain ⟨σ, hσ⟩ := exists_forall_parityOn_incidence_eq hG χ u
  refine ⟨σ, fun v hv => ?_⟩
  rw [hσ, decide_eq_false (ne_of_mem_of_not_mem hv hu), Bool.and_false, Bool.false_xor]

end Parity

end Tseitin

/-! ### Tseitin formulas -/

section Formula

variable [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The **Tseitin formula** of the multigraph `ends` with charges `χ`
[Tseitin][Tseitin1983] [Urquhart][Urquhart1987]: a variable for each edge, and for each vertex `v`
the clauses of `CNF.parityOnEq` saying that the parity of the edges at `v` other than self-loops is
`χ v`. -/
noncomputable def CNF.tseitin (ends : E → Sym2 V) (χ : V → Bool) : CNF E :=
  (univ : Finset V).toList.flatMap fun v => CNF.parityOnEq (Tseitin.incidence ends v) (χ v)

variable {ends : E → Sym2 V} {χ : V → Bool}

namespace CNF

theorem mem_tseitin {c : Clause E} :
    c ∈ tseitin ends χ ↔ ∃ v, c ∈ parityOnEq (Tseitin.incidence ends v) (χ v) := by
  simp [tseitin]

/-- An assignment satisfies the Tseitin formula when its parity at every vertex is the charge. -/
theorem eval_tseitin_eq_true_iff (σ : E → Bool) :
    (tseitin ends χ).eval σ = true ↔ ∀ v, parityOn (Tseitin.incidence ends v) σ = χ v := by
  simp [tseitin, eval_flatMap_eq_true_iff, eval_parityOnEq_eq_true_iff]

/-- **Tseitin formulas with odd total charge are unsatisfiable**
[Urquhart][Urquhart1987]. -/
theorem not_satisfiable_tseitin (h : parityOn univ χ = true) : ¬ (tseitin ends χ).Satisfiable :=
  fun ⟨σ, hσ⟩ => by
    rw [Tseitin.parityOn_univ_eq_false_of_forall ((eval_tseitin_eq_true_iff σ).1 hσ)] at h
    exact Bool.false_ne_true h

/-- On a connected multigraph, **the Tseitin formula is satisfiable exactly when the total charge
is even** [Urquhart][Urquhart1987]. -/
theorem satisfiable_tseitin_iff (hG : (Tseitin.graph ends).Connected) :
    (tseitin ends χ).Satisfiable ↔ parityOn univ χ = false := by
  refine ⟨fun ⟨σ, hσ⟩ => Tseitin.parityOn_univ_eq_false_of_forall
    ((eval_tseitin_eq_true_iff σ).1 hσ), fun h => ?_⟩
  obtain ⟨u⟩ := hG.nonempty
  obtain ⟨σ, hσ⟩ := Tseitin.exists_forall_parityOn_incidence_eq hG χ u
  exact ⟨σ, (eval_tseitin_eq_true_iff σ).2 fun v => by rw [hσ, h, Bool.false_and, Bool.false_xor]⟩

/-- A clause of a Tseitin formula has as many literals as some vertex has edges other than
self-loops. -/
theorem exists_length_eq_of_mem_tseitin {c : Clause E} (hc : c ∈ tseitin ends χ) :
    ∃ v, c.length = #(Tseitin.incidence ends v) := by
  obtain ⟨v, hv⟩ := mem_tseitin.1 hc
  exact ⟨v, length_of_mem_parityOnEq hv⟩

/-- If every vertex has at most `k` edges other than self-loops, the clauses of the Tseitin
formula have at most `k` literals. -/
theorem length_le_of_mem_tseitin {k : ℕ} (hk : ∀ v, #(Tseitin.incidence ends v) ≤ k)
    {c : Clause E} (hc : c ∈ tseitin ends χ) : c.length ≤ k := by
  obtain ⟨v, hv⟩ := exists_length_eq_of_mem_tseitin hc
  exact hv ▸ hk v

/-- If every vertex has at most `k` edges other than self-loops, the Tseitin formula has at most
`|V| 2 ^ k` clauses. -/
theorem length_tseitin_le {k : ℕ} (hk : ∀ v, #(Tseitin.incidence ends v) ≤ k) :
    (tseitin ends χ).length ≤ Fintype.card V * 2 ^ k := by
  rw [tseitin, List.length_flatMap, ← card_univ, ← length_toList]
  rw [← List.length_map (f := fun v => (parityOnEq (Tseitin.incidence ends v) (χ v)).length),
    ← smul_eq_mul]
  refine List.sum_le_length_nsmul _ _ fun n hn => ?_
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hn
  exact (length_parityOnEq_le _ _).trans (Nat.pow_le_pow_right two_pos (hk v))

/-- The variables of a Tseitin formula are edges. -/
theorem card_vars_tseitin_le : (tseitin ends χ).vars.toFinset.card ≤ Fintype.card E :=
  card_le_univ _

end CNF

end Formula

end Cslib.Logic.PL
