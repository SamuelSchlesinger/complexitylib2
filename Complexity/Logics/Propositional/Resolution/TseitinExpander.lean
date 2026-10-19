/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Cheeger
public import Complexity.Foundations.Combinatorics.Expander.Existence
public import Complexity.Logics.Propositional.Resolution.Tseitin

/-!
# Tseitin formulas on expanders are hard for resolution

A `D`-regular multigraph presented by a rotation map `G` (`Cslib.RotationMap`) has an edge for each
unordered pair `{p, G.rot p}` of a dart and its reversal (`Cslib.RotationMap.edges`), joining the
vertices of the two darts (`Cslib.RotationMap.edgeEnds`); self-loops and parallel edges are
allowed, as for rotation maps. The edges between a set of vertices `S` and its complement are the
darts from `S` to its complement, so the edge expansion `h(G)` of
`Cslib.RotationMap.edgeExpansion` bounds the expansion `e(G)` of Ben-Sasson and Wigderson:
`h(G) |V| / 3 ≤ e(G)`, as every set of between a third and two thirds of the vertices, or its
complement, has at most half and at least a third of the vertices
(`Cslib.RotationMap.edgeExpansion_mul_card_div_three_le_expansion`). If `h(G) > 0`, the multigraph
is connected, and Tseitin formulas on it need resolution refutations of width at least
`h(G) |V| / 3` and, when `|D| + 2 ≤ h(G) |V| / 3`, of at least
`exp ((h(G) |V| / 3 - |D| - 2)² / (8 |V| |D|))` lines.

Constant-degree expanders (`Cslib.RotationMap.expander`) have `120` labels and edge expansion at
least `1 / 6000`, by the easy half of Cheeger's inequality. Their Tseitin formulas with a single
charged vertex form **an explicit-size family of unsatisfiable formulas with `O(n)` variables and
clauses of constant width whose resolution refutations have `2 ^ Ω(n)` lines**
(`Cslib.Logic.PL.CNF.exists_forall_refutableInSize_exp_le`) [Urquhart][Urquhart1987]
[Ben-Sasson and Wigderson][BenSassonWigderson2001]. The expanders, and so the
formulas, are obtained non-constructively, from a counting argument (`Expander/Existence.lean`).

## Main definitions

* `Cslib.RotationMap.edges`, `Cslib.RotationMap.edgeEnds`: the edges of a rotation map and their
  ends.

## Main results

* `Cslib.RotationMap.card_boundary_edgeEnds`: the edges leaving a set are the darts leaving it.
* `Cslib.RotationMap.edgeExpansion_mul_card_div_three_le_expansion`: `h(G) |V| / 3 ≤ e(G)`.
* `Cslib.RotationMap.connected_graph_edgeEnds`: a rotation map of positive edge expansion is
  connected.
* `Cslib.RotationMap.edgeExpansion_mul_card_div_three_le_of_refutableInWidth`,
  `Cslib.RotationMap.exp_le_of_refutableInSize_tseitin`: the width and size lower bounds for
  Tseitin formulas on rotation maps, in terms of edge expansion.
* `Cslib.Logic.PL.CNF.exists_forall_refutableInSize_exp_le`: unsatisfiable formulas with `O(n)`
  variables and clauses of constant width need resolution refutations of `exp (Ω(n))` lines.

## References

* [A. Urquhart, *Hard examples for resolution*][Urquhart1987]
* [E. Ben-Sasson, A. Wigderson, *Short proofs are narrow—resolution made
  simple*][BenSassonWigderson2001]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Chapter 18][Jukna2012]
* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
-/

@[expose] public section

namespace Cslib

open Finset Logic.PL

namespace RotationMap

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]
  (G : RotationMap V D)

/-! ### The edges of a rotation map -/

/-- The edges of `G`: the unordered pairs `{p, G.rot p}` of a dart and its reversal. A dart fixed
by `G.rot` is a self-loop. -/
def edges : Finset (Sym2 (V × D)) :=
  univ.image fun p => s(p, G.rot p)

/-- The ends of an edge of `G`: the vertices of its two darts. -/
def edgeEnds (e : G.edges) : Sym2 V :=
  e.1.map Prod.fst

theorem mk_mem_edges (p : V × D) : s(p, G.rot p) ∈ G.edges :=
  mem_image_of_mem _ (mem_univ p)

variable {G} in
theorem exists_eq_of_mem_edges {e : Sym2 (V × D)} (he : e ∈ G.edges) :
    ∃ p, s(p, G.rot p) = e := by
  simpa [edges] using he

/-- `G` has at most `|V| |D|` edges. -/
theorem card_edges_le : #G.edges ≤ Fintype.card V * Fintype.card D :=
  card_image_le.trans (by rw [card_univ, Fintype.card_prod])

/-- The edges between `S` and its complement are the darts from `S` to its complement. -/
theorem card_boundary_edgeEnds (S : Finset V) :
    #(Tseitin.boundary G.edgeEnds S) = #(G.interedges S Sᶜ) := by
  symm
  refine card_bij (fun p _ => ⟨s(p, G.rot p), G.mk_mem_edges p⟩) (fun p hp => ?_)
    (fun p hp q hq h => ?_) (fun e he => ?_)
  · rw [mem_interedges] at hp
    exact Tseitin.mem_boundary.2 ⟨p.1, hp.1, (G.rot p).1, hp.2, rfl⟩
  · rw [mem_interedges] at hp hq
    simp only [Subtype.mk.injEq, Sym2.eq_iff] at h
    rcases h with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · -- `p = G.rot q` leads from `S` to its complement and back
      refine absurd hq.1 (mem_compl.1 ?_)
      have : G.rot p = q := by rw [h, rot_rot]
      rw [← this]
      exact hp.2
  · rcases e with ⟨e, he'⟩
    obtain ⟨v, hv, w, hw, hvw⟩ := Tseitin.mem_boundary.1 he
    obtain ⟨p, rfl⟩ := exists_eq_of_mem_edges he'
    change s(p.1, (G.rot p).1) = s(v, w) at hvw
    rcases Sym2.eq_iff.1 hvw with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · refine ⟨p, mem_interedges.2 ⟨h₁ ▸ hv, ?_⟩, rfl⟩
      change (G.rot p).1 ∈ Sᶜ
      rw [h₂]
      exact hw
    · refine ⟨G.rot p, mem_interedges.2 ⟨h₂ ▸ hv, ?_⟩, Subtype.ext ?_⟩
      · change (G.rot (G.rot p)).1 ∈ Sᶜ
        rw [rot_rot, h₁]
        exact hw
      · change s(G.rot p, G.rot (G.rot p)) = s(p, G.rot p)
        rw [rot_rot, Sym2.eq_swap]

/-- A vertex of `G` has at most `|D|` edges other than self-loops. -/
theorem card_incidence_edgeEnds_le (v : V) :
    #(Tseitin.incidence G.edgeEnds v) ≤ Fintype.card D := by
  have hsub : Tseitin.incidence G.edgeEnds v ⊆
      univ.image fun i : D => (⟨s((v, i), G.rot (v, i)), G.mk_mem_edges _⟩ : G.edges) := by
    intro e he
    rcases e with ⟨e, he'⟩
    obtain ⟨p, rfl⟩ := exists_eq_of_mem_edges he'
    have hv : v ∈ s(p.1, (G.rot p).1) := (Tseitin.mem_incidence.1 he).1
    rcases Sym2.mem_iff.1 hv with h | h
    · refine mem_image.2 ⟨p.2, mem_univ _, Subtype.ext ?_⟩
      simp only [h]
    · refine mem_image.2 ⟨(G.rot p).2, mem_univ _, Subtype.ext ?_⟩
      simp only [h, Prod.mk.eta, rot_rot, Sym2.eq_swap]
  exact (card_le_card hsub).trans (card_image_le.trans card_univ.le)

/-! ### Edge expansion -/

omit [DecidableEq D] in
/-- At least `h(G) |V| / 3` edges leave every set of between a third and two thirds of the
vertices: the set, or its complement, has at most half and at least a third of the vertices. -/
theorem edgeExpansion_mul_card_div_three_le_card_interedges {S : Finset V}
    (h₁ : Fintype.card V ≤ 3 * #S) (h₂ : 3 * #S ≤ 2 * Fintype.card V) :
    G.edgeExpansion * Fintype.card V / 3 ≤ #(G.interedges S Sᶜ) := by
  have hc := card_add_card_compl S
  rcases le_or_gt (2 * #S) (Fintype.card V) with h | h
  · have hS : (Fintype.card V : ℝ) ≤ 3 * #S := by exact_mod_cast h₁
    have := G.edgeExpansion_mul_card_le h
    nlinarith [G.edgeExpansion_nonneg]
  · have hle : 2 * #Sᶜ ≤ Fintype.card V := by omega
    have hS : (Fintype.card V : ℝ) ≤ 3 * #Sᶜ := by exact_mod_cast (show _ ≤ _ by omega)
    have := G.edgeExpansion_mul_card_le hle
    rw [compl_compl, card_interedges_comm] at this
    nlinarith [G.edgeExpansion_nonneg]

/-- **Edge expansion bounds the expansion of Ben-Sasson and Wigderson**: `h(G) |V| / 3 ≤ e(G)`. -/
theorem edgeExpansion_mul_card_div_three_le_expansion :
    G.edgeExpansion * Fintype.card V / 3 ≤ Tseitin.expansion G.edgeEnds := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [G.edgeExpansion_eq_zero_of_subsingleton]
    simp
  obtain ⟨S, h₁, h₂, hS⟩ := Tseitin.exists_card_boundary_eq_expansion G.edgeEnds
    Fintype.one_lt_card
  rw [← hS, card_boundary_edgeEnds]
  exact G.edgeExpansion_mul_card_div_three_le_card_interedges h₁ h₂

/-- A rotation map of positive edge expansion is connected. -/
theorem connected_graph_edgeEnds (hG : 0 < G.edgeExpansion) :
    (Tseitin.graph G.edgeEnds).Connected := by
  have : Nontrivial V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hG.ne' G.edgeExpansion_eq_zero_of_subsingleton
  refine (Tseitin.connected_graph_iff _).2 ⟨inferInstance, fun S hS hSu => ?_⟩
  rw [← card_pos, card_boundary_edgeEnds, ← Nat.cast_pos (α := ℝ)]
  rcases le_or_gt (2 * #S) (Fintype.card V) with h | h
  · have hpos : (0 : ℝ) < #S := by exact_mod_cast hS.card_pos
    exact (mul_pos hG hpos).trans_le (G.edgeExpansion_mul_card_le h)
  · have hc := card_add_card_compl S
    have hle : 2 * #Sᶜ ≤ Fintype.card V := by omega
    have hpos : (0 : ℝ) < #Sᶜ := by
      exact_mod_cast (compl_ne_univ_iff_nonempty Sᶜ |>.1 (by rwa [compl_compl])).card_pos
    have := G.edgeExpansion_mul_card_le hle
    rw [compl_compl, card_interedges_comm] at this
    exact (mul_pos hG hpos).trans_le this

/-! ### Resolution lower bounds -/

/-- **The width lower bound for Tseitin formulas on rotation maps**
[Ben-Sasson and Wigderson][BenSassonWigderson2001]: if `h(G) > 0`, every resolution
refutation of a Tseitin formula on `G` has width at least `h(G) |V| / 3`. -/
theorem edgeExpansion_mul_card_div_three_le_of_refutableInWidth (hG : 0 < G.edgeExpansion)
    {χ : V → Bool} {w : ℕ} (h : (CNF.tseitin G.edgeEnds χ).RefutableInWidth w) :
    G.edgeExpansion * Fintype.card V / 3 ≤ w :=
  G.edgeExpansion_mul_card_div_three_le_expansion.trans
    (by exact_mod_cast Tseitin.expansion_le_of_refutableInWidth (G.connected_graph_edgeEnds hG) h)

/-- **The size lower bound for Tseitin formulas on rotation maps**
[Ben-Sasson and Wigderson, Corollary 3.6][BenSassonWigderson2001]: if
`|D| + 2 ≤ h(G) |V| / 3`, every resolution refutation of a Tseitin formula on `G` has at least
`exp ((h(G) |V| / 3 - |D| - 2)² / (8 |V| |D|))` lines. -/
theorem exp_le_of_refutableInSize_tseitin
    (hG : Fintype.card D + 2 ≤ G.edgeExpansion * Fintype.card V / 3) {χ : V → Bool} {s : ℕ}
    (hs : (CNF.tseitin G.edgeEnds χ).RefutableInSize s) :
    Real.exp ((G.edgeExpansion * Fintype.card V / 3 - Fintype.card D - 2) ^ 2 /
      (8 * Fintype.card V * Fintype.card D)) ≤ s := by
  have hh : 0 < G.edgeExpansion := by
    by_contra h
    have : G.edgeExpansion = 0 := le_antisymm (not_lt.1 h) G.edgeExpansion_nonneg
    rw [this, zero_mul, zero_div] at hG
    linarith [(Fintype.card D).cast_nonneg (α := ℝ)]
  have he := G.edgeExpansion_mul_card_div_three_le_expansion
  have hke : Fintype.card D + 2 ≤ Tseitin.expansion G.edgeEnds := by
    exact_mod_cast hG.trans he
  have hsize := Tseitin.exp_le_of_refutableInSize (N := Fintype.card V * Fintype.card D)
    (G.connected_graph_edgeEnds hh) G.card_incidence_edgeEnds_le
    (by rw [Fintype.card_coe]; exact G.card_edges_le) hke hs
  refine le_trans (Real.exp_le_exp.2 ?_) hsize
  push_cast
  rw [mul_assoc]
  gcongr
  linarith

end RotationMap

/-! ### Hard formulas -/

namespace Logic.PL.CNF

/-- **Unsatisfiable formulas with `O(n)` variables and clauses of constant width need resolution
refutations of `2 ^ Ω(n)` lines** [Urquhart][Urquhart1987]
[Ben-Sasson and Wigderson][BenSassonWigderson2001]
[Jukna, Chapter 18][Jukna2012]. For every `n ≥ 4392000` there is an unsatisfiable formula with at
most `120 n` variables and `2 ^ 120 n` clauses of width at most `120` whose resolution refutations
all have at least `exp (n / (960 · 36000²))` lines. It is the Tseitin formula, with a single
charged vertex, of a `120`-regular expander on `n` vertices (`Cslib.RotationMap.expander`), whose
existence is proved non-constructively. -/
theorem exists_forall_refutableInSize_exp_le :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ m ≤ 120 * n, ∃ φ : CNF (Fin m),
      φ.length ≤ 2 ^ 120 * n ∧ (∀ c ∈ φ, c.width ≤ 120) ∧ ¬ φ.Satisfiable ∧
      ∀ s, φ.RefutableInSize s → Real.exp (n / (960 * 36000 ^ 2)) ≤ s := by
  refine ⟨4392000, fun n hn => ?_⟩
  have : NeZero n := ⟨by omega⟩
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  set G := RotationMap.expander (Fin n)
  let f : Fin (Fintype.card G.edges) ≃ G.edges := (Fintype.equivFin G.edges).symm
  let ends := G.edgeEnds ∘ f
  let χ : Fin n → Bool := fun v => decide (v = 0)
  have hdeg (v : Fin n) : #(Tseitin.incidence ends v) ≤ 120 := by
    rw [Tseitin.card_incidence_comp]
    simpa using G.card_incidence_edgeEnds_le v
  have hm : Fintype.card G.edges ≤ 120 * n := by
    rw [Fintype.card_coe, mul_comm]
    simpa using G.card_edges_le
  refine ⟨_, hm, tseitin ends χ, ?_, fun c hc => ?_, not_satisfiable_tseitin ?_, fun s hs => ?_⟩
  · simpa [mul_comm] using length_tseitin_le (χ := χ) hdeg
  · exact (List.toFinset_card_le c).trans (length_le_of_mem_tseitin hdeg hc)
  · simp [χ, parityOn, filter_eq']
  -- the edge expansion is at least `1 / 6000`, by the easy half of Cheeger's inequality
  have hlam : G.secondEigenvalue ≤ 1 - 1 / 360000 :=
    G.secondEigenvalue_le_spectralExpansion.trans (RotationMap.spectralExpansion_expander_le _)
  have hh : 1 / 6000 ≤ G.edgeExpansion := by
    have := G.card_mul_one_sub_secondEigenvalue_div_two_le_edgeExpansion
    simp only [Fintype.card_fin, Nat.cast_ofNat] at this
    linarith
  have he : (n : ℝ) / 18000 ≤ Tseitin.expansion ends := by
    rw [Tseitin.expansion_comp]
    have := G.edgeExpansion_mul_card_div_three_le_expansion
    simp only [Fintype.card_fin] at this
    nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hn' : (4392000 : ℝ) ≤ n := by exact_mod_cast hn
  have hke : 120 + 2 ≤ Tseitin.expansion ends := by
    have : (122 : ℝ) ≤ Tseitin.expansion ends := by linarith
    exact_mod_cast this
  have hG : (Tseitin.graph ends).Connected := by
    rw [Tseitin.graph_comp]
    exact G.connected_graph_edgeEnds (by linarith)
  have hsize := Tseitin.exp_le_of_refutableInSize hG hdeg (by simpa using hm) hke hs
  refine le_trans (Real.exp_le_exp.2 ?_) hsize
  -- `e(G) - 122 ≥ n / 36000`
  have hx : (n : ℝ) / 36000 ≤ (Tseitin.expansion ends : ℝ) - 120 - 2 := by linarith
  have hsq := pow_le_pow_left₀ (by positivity) hx 2
  have hnpos : (0 : ℝ) < n := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  nlinarith

end Logic.PL.CNF

end Cslib
