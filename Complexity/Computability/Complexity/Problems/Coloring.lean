/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.IndependentSet
public import Complexity.Computability.Complexity.Problems.ThreeSAT
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Graph coloring

`KColoring k` is the set of graphs, given by a list of vertices and a list of edges, whose
declared vertices can be colored with `k` colors so that adjacent vertices get different colors
[Karp1972]; `ThreeColoring` is `KColoring 3`. Graphs are read through
`Cslib.Complexity.Graph.toSimpleGraph` restricted to the declared vertices (`SimpleGraph.induce`),
and colorings through `SimpleGraph.Colorable`. Edges with an undeclared endpoint and self-loops
are therefore ignored.

A certificate for `KColoring k` gives each declared vertex `k` bits, at the position of its first
occurrence; the color is the number of set bits, which must be below `k`.

The reduction `SAT.toThreeColoring` is the palette, variable and clause gadget construction
[Sipser, Problem 7.29][Sipser2013]. Three palette vertices `T`, `F` and `B` form a triangle; the
two literals of each variable form a triangle with `B`, so they take the colors of `T` and `F` in
some order. The gadget of a clause is a chain of OR gadgets: its stage `0` is adjacent to `T` and
`B`, hence colored like `F`; stage `j + 1` is a triangle attached to the output of stage `j` and to
the `j`-th literal, whose output can take the color of `T` exactly when one of them does; and the
output of the last stage is adjacent to `F` and `B`, hence colored like `T`. Chaining handles
clauses of every width, including the empty clause, so the reduction is from `SAT`; it also
reduces `ThreeSAT` after rejecting clauses with more than three literals.

## Main definitions

* `Cslib.Complexity.KColoring`, `Cslib.Complexity.ThreeColoring`.
* `Cslib.Complexity.KColoring.colorOf`, `Cslib.Complexity.KColoring.verifier`.
* `Cslib.Complexity.SAT.toThreeColoring`.

## Main results

* `Cslib.Complexity.mem_KColoring_iff`: membership as a bounded natural-number coloring.
* `Cslib.Complexity.KColoring.isVerifier`, `Cslib.Complexity.KColoring.mem_NP`:
  `KColoring k ∈ NP encGraph` for every `k`.
* `Cslib.Complexity.SAT.toThreeColoring_mem_iff`: `toThreeColoring φ ∈ ThreeColoring ↔ φ ∈ SAT`.
* `Cslib.Complexity.SAT.computableTidilyInPolyTime_toThreeColoring`: the reduction is
  polynomial-time.
* `Cslib.Complexity.polyTimeReducible_SAT_ThreeColoring`,
  `Cslib.Complexity.polyTimeReducible_ThreeSAT_ThreeColoring`,
  `Cslib.Complexity.ThreeColoring_npHard`, `Cslib.Complexity.ThreeColoring_npComplete`:
  `ThreeColoring` is `NP`-complete.

## References

* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM ComputableTidilyInPolyTime

/-- The graphs whose declared vertices can be colored with `k` colors, adjacent vertices getting
different colors. -/
def KColoring (k : ℕ) : Set Graph := {G | (G.toSimpleGraph.induce {v | v ∈ G.1}).Colorable k}

/-- The graphs whose declared vertices can be colored with three colors, adjacent vertices getting
different colors. -/
abbrev ThreeColoring : Set Graph := KColoring 3

/-- Membership in `KColoring k` as a coloring by natural numbers below `k`. -/
theorem mem_KColoring_iff {k : ℕ} {G : Graph} :
    G ∈ KColoring k ↔ ∃ c : ℕ → ℕ, (∀ v ∈ G.1, c v < k) ∧
      ∀ u ∈ G.1, ∀ v ∈ G.1, G.toSimpleGraph.Adj u v → c u ≠ c v := by
  classical
  rw [KColoring, Set.mem_ofPred_eq, SimpleGraph.colorable_iff_exists_bdd_nat_coloring]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨fun v => if h : v ∈ G.1 then C ⟨v, h⟩ else 0, fun v hv => ?_,
      fun u hu v hv huv => ?_⟩
    · simpa only [hv, dite_true] using hC ⟨v, hv⟩
    · simpa only [hu, hv, dite_true] using C.valid (v := ⟨u, hu⟩) (w := ⟨v, hv⟩) huv
  · rintro ⟨c, hc, hadj⟩
    exact ⟨SimpleGraph.Coloring.mk (fun v => c v) fun {u v} huv => hadj u u.2 v v.2 huv,
      fun v => hc v v.2⟩

namespace KColoring

/-! ### The verifier -/

/-- The color of `v` described by the certificate `w`: the number of set bits among the `k` bits
of `w` from position `k * i` on, where `i` is the first occurrence of `v` in `V`. -/
def colorOf (k : ℕ) (V : List ℕ) (w : List Bool) (v : ℕ) : ℕ :=
  (List.range k).countP fun c => w.getD (k * V.idxOf v + c) false

/-- The verifier for `KColoring k`: every declared vertex gets a color below `k` from the
certificate, and no two adjacent declared vertices get the same color. -/
def verifier (k : ℕ) (x : Graph × List Bool) : Bool :=
  x.1.1.all fun u => decide (colorOf k x.1.1 x.2 u < k) &&
    x.1.1.all fun v => !(x.1.adjBool u v && decide (colorOf k x.1.1 x.2 u = colorOf k x.1.1 x.2 v))

private theorem countP_range_lt (k m : ℕ) :
    (List.range k).countP (fun c => decide (c < m)) = min m k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.range_succ, List.countP_append, ih, List.countP_singleton, decide_eq_true_eq]
    split_ifs <;> omega

private theorem length_vertices_le (G : Graph) : G.1.length ≤ (encGraph G).length := by
  calc G.1.length ≤ (encList encNat G.1).length := length_le_length_encList encNat G.1
    _ ≤ (encGraph G).length := by
        simp only [encGraph, length_encPair]
        omega

/-- `KColoring.verifier k` verifies `KColoring k` with certificates of `k` bits per symbol of the
encoded graph. -/
theorem isVerifier (k : ℕ) :
    IsVerifier encGraph (Polynomial.C k * Polynomial.X) (verifier k) (KColoring k) := by
  intro G
  simp only [mem_KColoring_iff, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    verifier, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, Graph.adjBool_eq_false_iff, decide_eq_false_iff_not]
  constructor
  · rintro ⟨c, hc, hadj⟩
    let w := (List.range (k * (encGraph G).length)).map fun j =>
      decide (j % k < c (G.1.getD (j / k) 0))
    have hcol : ∀ v ∈ G.1, colorOf k G.1 w v = c v := by
      intro v hv
      have hlt : G.1.idxOf v < G.1.length := List.idxOf_lt_length_iff.2 hv
      have hlen := length_vertices_le G
      have hk : 0 < k := Nat.zero_lt_of_lt (hc v hv)
      rw [colorOf, ← min_eq_left (hc v hv).le, ← countP_range_lt]
      refine List.countP_congr fun c' hc' => ?_
      rw [List.mem_range] at hc'
      have hidx : k * G.1.idxOf v + c' < k * (encGraph G).length := by
        calc k * G.1.idxOf v + c' < k * (G.1.idxOf v + 1) := by rw [Nat.mul_succ]; omega
          _ ≤ k * (encGraph G).length := Nat.mul_le_mul_left k (by omega)
      have hdiv : (k * G.1.idxOf v + c') / k = G.1.idxOf v := by
        rw [Nat.mul_add_div hk, Nat.div_eq_of_lt hc', Nat.add_zero]
      have hmod : (k * G.1.idxOf v + c') % k = c' := by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc']
      simp only [w, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hidx,
        Option.map_some, Option.getD_some, hdiv, hmod, List.getElem?_eq_getElem hlt,
        List.getElem_idxOf hlt]
    refine ⟨w, by simp [w], fun u hu => ⟨by rw [hcol u hu]; exact hc u hu, fun v hv => ?_⟩⟩
    rw [hcol u hu, hcol v hv]
    by_cases huv : G.toSimpleGraph.Adj u v
    · exact Or.inr (hadj u hu v hv huv)
    · exact Or.inl huv
  · rintro ⟨w, -, hw⟩
    refine ⟨colorOf k G.1 w, fun v hv => (hw v hv).1, fun u hu v hv huv => ?_⟩
    rcases (hw u hu).2 v hv with h | h
    · exact (h huv).elim
    · exact h

/-- Reading a color from a certificate is polynomial-time, with the color in unary. -/
@[fun_prop]
theorem computableTidilyInPolyTime_colorOf (k : ℕ) :
    ComputableTidilyInPolyTime (fun p : (List ℕ × List Bool) × ℕ => colorOf k p.1.1 p.1.2 p.2)
      (encPair (encPair (encList encNat) encBits) encNat) encUnary := by
  have hrange : ComputableTidilyInPolyTime (fun _ : (List ℕ × List Bool) × ℕ => List.range k)
      (encPair (encPair (encList encNat) encBits) encNat) (encList encUnary) := const _
  have hk : ComputableTidilyInPolyTime (fun _ : ((List ℕ × List Bool) × ℕ) × ℕ => k)
      (encPair (encPair (encPair (encList encNat) encBits) encNat) encUnary) encUnary := const _
  exact countPWithInput hrange (by fun_prop)

/-- The `KColoring k` verifier is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_verifier (k : ℕ) :
    ComputableTidilyInPolyTime (verifier k) (encPair encGraph encBits) encBool := by
  have hV : ComputableTidilyInPolyTime (fun x : Graph × List Bool => x.1.1)
      (encPair encGraph encBits) (encList encNat) := by
    unfold encGraph
    fun_prop
  have hcol : ComputableTidilyInPolyTime
      (fun p : (Graph × List Bool) × ℕ => colorOf k p.1.1.1 p.1.2 p.2)
      (encPair (encPair encGraph encBits) encNat) encUnary :=
    (computableTidilyInPolyTime_colorOf k).comp
      (g := fun p : (Graph × List Bool) × ℕ => ((p.1.1.1, p.1.2), p.2))
      (by unfold encGraph; fun_prop)
  have hproj : ComputableTidilyInPolyTime
      (fun p : ((Graph × List Bool) × ℕ) × ℕ => ((p.1.1.1, p.1.2), p.2))
      (encPair (encPair (encPair encGraph encBits) encNat) encNat)
      (encPair (encPair encGraph encNat) encNat) := by fun_prop
  have hproj' : ComputableTidilyInPolyTime
      (fun p : ((Graph × List Bool) × ℕ) × ℕ => (p.1.1, p.2))
      (encPair (encPair (encPair encGraph encBits) encNat) encNat)
      (encPair (encPair encGraph encBits) encNat) := by fun_prop
  exact allWithInput hV (bool_and' (unary_lt' hcol (const k))
    (allWithInput (hV.comp (fst _ _)) (bool_not.comp
      (bool_and' (Graph.computableTidilyInPolyTime_adjBool.comp hproj)
        ((hcol.comp (fst _ _)).decide_eq' (hcol.comp hproj'))))))

/-- `KColoring k` belongs to `NP`. -/
theorem mem_NP (k : ℕ) : KColoring k ∈ NP encGraph :=
  ⟨_, verifier k, computableTidilyInPolyTime_verifier k, isVerifier k⟩

end KColoring

namespace SAT

/-! ### The gadget graph -/

/-- The palette vertex of color `c`: color `0` reads true, `1` reads false and `2` is the base
color. -/
def paletteVertex (c : ℕ) : ℕ := Nat.pair 0 c

/-- The vertex of a literal of `φ`, numbered by the first occurrence of its variable in `φ`. -/
def literalVertex (φ : CNF ℕ) (l : Literal ℕ) : ℕ :=
  Nat.pair 1 (Nat.pair (φ.vars.idxOf l.1) l.2.toNat)

/-- Vertex `r` of stage `j` of the gadget of clause `i`; vertex `2` is the output of the stage. -/
def gadgetVertex (i j r : ℕ) : ℕ := Nat.pair 2 (Nat.pair i (Nat.pair j r))

/-- The edges between the two literals of the variable `x` and the base palette vertex. -/
def variableEdges (φ : CNF ℕ) (x : ℕ) : List (ℕ × ℕ) :=
  [(literalVertex φ (x, true), literalVertex φ (x, false)),
    (literalVertex φ (x, true), paletteVertex 2), (literalVertex φ (x, false), paletteVertex 2)]

/-- Stage `j + 1` of the gadget of clause `i`: a triangle attached to the output of stage `j` and
to the literal `l`. -/
def stageEdges (φ : CNF ℕ) (i j : ℕ) (l : Literal ℕ) : List (ℕ × ℕ) :=
  [(gadgetVertex i (j + 1) 0, gadgetVertex i (j + 1) 1),
    (gadgetVertex i (j + 1) 1, gadgetVertex i (j + 1) 2),
    (gadgetVertex i (j + 1) 2, gadgetVertex i (j + 1) 0),
    (gadgetVertex i (j + 1) 0, gadgetVertex i j 2),
    (gadgetVertex i (j + 1) 1, literalVertex φ l)]

/-- The gadget of the clause `c` with index `i`: the output of stage `0` is adjacent to the true
and base palette vertices, one stage follows for each literal, and the output of the last stage is
adjacent to the false and base palette vertices. -/
def clauseEdges (φ : CNF ℕ) (i : ℕ) (c : Clause ℕ) : List (ℕ × ℕ) :=
  [(gadgetVertex i 0 2, paletteVertex 0), (gadgetVertex i 0 2, paletteVertex 2),
    (gadgetVertex i c.length 2, paletteVertex 1), (gadgetVertex i c.length 2, paletteVertex 2)] ++
    c.zipIdx.flatMap fun l => stageEdges φ i l.2 l.1

/-- The edges of the gadget graph of `φ`: the palette triangle, the variable triangles and the
clause gadgets. -/
def coloringEdges (φ : CNF ℕ) : List (ℕ × ℕ) :=
  [(paletteVertex 0, paletteVertex 1), (paletteVertex 1, paletteVertex 2),
    (paletteVertex 2, paletteVertex 0)] ++
    φ.vars.flatMap (variableEdges φ) ++ φ.zipIdx.flatMap fun c => clauseEdges φ c.2 c.1

/-- The reduction from `SAT` to `ThreeColoring`: the gadget graph of `φ`, whose declared vertices
are the endpoints of its edges. -/
def toThreeColoring (φ : CNF ℕ) : Graph :=
  ((coloringEdges φ).flatMap fun e => [e.1, e.2], coloringEdges φ)

/-! ### Correctness of the reduction -/

/-- No edge of the gadget graph is a self-loop. -/
theorem ne_of_mem_coloringEdges {φ : CNF ℕ} {e : ℕ × ℕ} (he : e ∈ coloringEdges φ) :
    e.1 ≠ e.2 := by
  simp only [coloringEdges, clauseEdges, stageEdges, variableEdges, List.mem_append,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with (he | ⟨x, -, he⟩) | ⟨⟨cl, i⟩, -, he | ⟨⟨l, j⟩, -, he⟩⟩
  · rcases he with rfl | rfl | rfl <;> simp [paletteVertex]
  · rcases he with rfl | rfl | rfl <;> simp [paletteVertex, literalVertex, Nat.pair_eq_pair]
  · rcases he with rfl | rfl | rfl | rfl <;> simp [paletteVertex, gadgetVertex, Nat.pair_eq_pair]
  · rcases he with rfl | rfl | rfl | rfl | rfl <;>
      simp [gadgetVertex, literalVertex, Nat.pair_eq_pair]

private theorem mem_endpoints {E : List (ℕ × ℕ)} {e : ℕ × ℕ} (he : e ∈ E) :
    e.1 ∈ E.flatMap (fun e => [e.1, e.2]) ∧ e.2 ∈ E.flatMap (fun e => [e.1, e.2]) :=
  ⟨List.mem_flatMap.2 ⟨e, he, by simp⟩, List.mem_flatMap.2 ⟨e, he, by simp⟩⟩

private theorem fst_mem_vars {φ : CNF ℕ} {c : Clause ℕ} {l : Literal ℕ} (hc : c ∈ φ)
    (hl : l ∈ c) : l.1 ∈ φ.vars :=
  List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨c, hc, hl⟩, rfl⟩

private theorem variableEdges_subset {φ : CNF ℕ} {x : ℕ} (hx : x ∈ φ.vars) :
    variableEdges φ x ⊆ coloringEdges φ := fun e he => by
  simp only [coloringEdges, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inr ⟨x, hx, he⟩)

private theorem clauseEdges_subset {φ : CNF ℕ} {i : ℕ} (hi : i < φ.length) :
    clauseEdges φ i φ[i] ⊆ coloringEdges φ := fun e he => by
  simp only [coloringEdges, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨(φ[i], i), List.mem_zipIdx_iff_getElem?.2 (by simp [hi]), he⟩

private theorem stageEdges_subset {φ : CNF ℕ} {i j : ℕ} (hi : i < φ.length)
    (hj : j < φ[i].length) : stageEdges φ i j φ[i][j] ⊆ coloringEdges φ := fun e he => by
  refine clauseEdges_subset hi ?_
  simp only [clauseEdges, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨(φ[i][j], j), List.mem_zipIdx_iff_getElem?.2 (by simp [hj]), he⟩

/-- In a proper coloring of the gadget graph, a clause none of whose first `j` literals is
colored like the true palette vertex has the output of stage `j` colored like the false one. -/
private theorem output_eq_of_coloring {φ : CNF ℕ} {c : ℕ → ℕ}
    (hE : ∀ e ∈ coloringEdges φ, c e.1 ≠ c e.2 ∧ c e.1 < 3 ∧ c e.2 < 3) {i : ℕ}
    (hi : i < φ.length) :
    ∀ j ≤ φ[i].length, (∀ l ∈ φ[i].take j, c (literalVertex φ l) = c (paletteVertex 1)) →
      c (gadgetVertex i j 2) = c (paletteVertex 1) := by
  have hTF := hE (paletteVertex 0, paletteVertex 1) (by simp [coloringEdges])
  have hFB := hE (paletteVertex 1, paletteVertex 2) (by simp [coloringEdges])
  have hBT := hE (paletteVertex 2, paletteVertex 0) (by simp [coloringEdges])
  intro j
  induction j with
  | zero =>
    intro _ _
    have h₁ := hE _ (clauseEdges_subset hi (by simp [clauseEdges] :
      (gadgetVertex i 0 2, paletteVertex 0) ∈ clauseEdges φ i φ[i]))
    have h₂ := hE _ (clauseEdges_subset hi (by simp [clauseEdges] :
      (gadgetVertex i 0 2, paletteVertex 2) ∈ clauseEdges φ i φ[i]))
    simp only at hTF hFB hBT h₁ h₂
    omega
  | succ j ih =>
    intro hj hlit
    have hj' : j < φ[i].length := hj
    have hpre : ∀ l ∈ φ[i].take j, c (literalVertex φ l) = c (paletteVertex 1) :=
      fun l hl => hlit l (List.take_subset_take_left _ (Nat.le_succ j) hl)
    have hout := ih hj'.le hpre
    have hl := hlit φ[i][j] (by
      rw [List.take_add_one, List.getElem?_eq_getElem hj']
      exact List.mem_append_right _ (by simp))
    have hst := stageEdges_subset hi hj'
    have h₁ := hE _ (hst (by simp [stageEdges] :
      (gadgetVertex i (j + 1) 0, gadgetVertex i (j + 1) 1) ∈ _))
    have h₂ := hE _ (hst (by simp [stageEdges] :
      (gadgetVertex i (j + 1) 1, gadgetVertex i (j + 1) 2) ∈ _))
    have h₃ := hE _ (hst (by simp [stageEdges] :
      (gadgetVertex i (j + 1) 2, gadgetVertex i (j + 1) 0) ∈ _))
    have h₄ := hE _ (hst (by simp [stageEdges] :
      (gadgetVertex i (j + 1) 0, gadgetVertex i j 2) ∈ _))
    have h₅ := hE _ (hst (by simp [stageEdges] :
      (gadgetVertex i (j + 1) 1, literalVertex φ φ[i][j]) ∈ _))
    simp only at hTF hFB hBT h₁ h₂ h₃ h₄ h₅
    omega

/-- A proper 3-coloring of the gadget graph yields a satisfying assignment. -/
private theorem satisfiable_of_coloring {φ : CNF ℕ} {c : ℕ → ℕ}
    (hE : ∀ e ∈ coloringEdges φ, c e.1 ≠ c e.2 ∧ c e.1 < 3 ∧ c e.2 < 3) : φ ∈ SAT := by
  have hTF := hE (paletteVertex 0, paletteVertex 1) (by simp [coloringEdges])
  have hFB := hE (paletteVertex 1, paletteVertex 2) (by simp [coloringEdges])
  have hBT := hE (paletteVertex 2, paletteVertex 0) (by simp [coloringEdges])
  simp only at hTF hFB hBT
  let σ : ℕ → Bool := fun x => decide (c (literalVertex φ (x, true)) = c (paletteVertex 0))
  -- A literal that `σ` falsifies is colored like the false palette vertex.
  have hfalse : ∀ l : Literal ℕ, l.1 ∈ φ.vars → σ l.1 ≠ l.2 →
      c (literalVertex φ l) = c (paletteVertex 1) := by
    rintro ⟨x, b⟩ hx hσ
    have h₁ := hE _ (variableEdges_subset hx (by simp [variableEdges] :
      (literalVertex φ (x, true), literalVertex φ (x, false)) ∈ _))
    have h₂ := hE _ (variableEdges_subset hx (by simp [variableEdges] :
      (literalVertex φ (x, true), paletteVertex 2) ∈ _))
    have h₃ := hE _ (variableEdges_subset hx (by simp [variableEdges] :
      (literalVertex φ (x, false), paletteVertex 2) ∈ _))
    simp only at h₁ h₂ h₃ hσ
    cases b
    · have : c (literalVertex φ (x, true)) = c (paletteVertex 0) := by
        simpa [σ] using hσ
      omega
    · have : c (literalVertex φ (x, true)) ≠ c (paletteVertex 0) := by
        simpa [σ] using hσ
      omega
  refine ⟨σ, (CNF.eval_eq_true_iff _ _).2 fun cl hcl => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcl
  rw [Clause.eval_eq_true_iff]
  by_contra hsat
  push Not at hsat
  have hout := output_eq_of_coloring hE hi φ[i].length le_rfl fun l hl => by
    rw [List.take_length] at hl
    exact hfalse l (fst_mem_vars hcl hl) (hsat l hl)
  have h := hE _ (clauseEdges_subset hi (by simp [clauseEdges] :
    (gadgetVertex i φ[i].length 2, paletteVertex 1) ∈ clauseEdges φ i φ[i]))
  exact h.1 hout

/-- The color of a literal under `σ`: `0` when it holds and `1` otherwise. -/
private def literalColor (σ : ℕ → Bool) (l : Literal ℕ) : ℕ := if σ l.1 = l.2 then 0 else 1

/-- The color of the output of stage `j` of the gadget of the clause `c` under `σ`: `0` when one
of the first `j` literals of `c` holds and `1` otherwise. -/
private def outputColor (σ : ℕ → Bool) (c : Clause ℕ) (j : ℕ) : ℕ :=
  if (c.take j).any (Literal.eval σ) then 0 else 1

/-- The 3-coloring of the gadget graph read off an assignment `σ`, decoding vertex labels. -/
private def gadgetColoring (φ : CNF ℕ) (σ : ℕ → Bool) (n : ℕ) : ℕ :=
  match n.unpair.1 with
  | 0 => n.unpair.2 % 3
  | 1 => literalColor σ (φ.vars.getD n.unpair.2.unpair.1 0, decide (n.unpair.2.unpair.2 = 1))
  | _ =>
    let c := φ.getD n.unpair.2.unpair.1 []
    let j := n.unpair.2.unpair.2.unpair.1
    let a := outputColor σ c (j - 1)
    let b := literalColor σ (c.getD (j - 1) (0, false))
    match n.unpair.2.unpair.2.unpair.2 with
    | 0 => if a = 0 then 1 else if b = 0 then 2 else 0
    | 1 => if a ≠ 0 ∧ b = 0 then 1 else 2
    | _ => outputColor σ c j

private theorem gadgetColoring_palette (φ : CNF ℕ) (σ : ℕ → Bool) (c : ℕ) :
    gadgetColoring φ σ (paletteVertex c) = c % 3 := by
  simp [gadgetColoring, paletteVertex]

private theorem gadgetColoring_literal {φ : CNF ℕ} (σ : ℕ → Bool) {l : Literal ℕ}
    (hl : l.1 ∈ φ.vars) : gadgetColoring φ σ (literalVertex φ l) = literalColor σ l := by
  obtain ⟨x, b⟩ := l
  have hlt : φ.vars.idxOf x < φ.vars.length := List.idxOf_lt_length_iff.2 hl
  simp only [gadgetColoring, literalVertex, Nat.unpair_pair]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
    List.getElem_idxOf hlt]
  cases b <;> rfl

private theorem gadgetColoring_output (φ : CNF ℕ) (σ : ℕ → Bool) (i j : ℕ) :
    gadgetColoring φ σ (gadgetVertex i j 2) = outputColor σ (φ.getD i []) j := by
  simp [gadgetColoring, gadgetVertex]

private theorem gadgetColoring_stage₀ (φ : CNF ℕ) (σ : ℕ → Bool) (i j : ℕ) :
    gadgetColoring φ σ (gadgetVertex i (j + 1) 0) =
      if outputColor σ (φ.getD i []) j = 0 then 1
      else if literalColor σ ((φ.getD i []).getD j (0, false)) = 0 then 2 else 0 := by
  simp [gadgetColoring, gadgetVertex]

private theorem gadgetColoring_stage₁ (φ : CNF ℕ) (σ : ℕ → Bool) (i j : ℕ) :
    gadgetColoring φ σ (gadgetVertex i (j + 1) 1) =
      if outputColor σ (φ.getD i []) j ≠ 0 ∧
        literalColor σ ((φ.getD i []).getD j (0, false)) = 0 then 1 else 2 := by
  simp [gadgetColoring, gadgetVertex]

private theorem outputColor_succ {σ : ℕ → Bool} {c : Clause ℕ} {j : ℕ} (hj : j < c.length) :
    outputColor σ c (j + 1) =
      if outputColor σ c j = 0 ∨ literalColor σ c[j] = 0 then 0 else 1 := by
  have h : (c.take (j + 1)).any (Literal.eval σ) =
      ((c.take j).any (Literal.eval σ) || decide (σ c[j].1 = c[j].2)) := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, List.any_append]
    simp [Literal.eval, beq_eq_decide]
  unfold outputColor literalColor
  rw [h]
  by_cases h₁ : (c.take j).any (Literal.eval σ) = true <;>
    by_cases h₂ : σ c[j].1 = c[j].2 <;> simp [h₁, h₂]

/-- The coloring read off a satisfying assignment is proper on every edge of the gadget graph. -/
private theorem gadgetColoring_ne {φ : CNF ℕ} {σ : ℕ → Bool} (hσ : φ.eval σ = true) :
    ∀ e ∈ coloringEdges φ, gadgetColoring φ σ e.1 ≠ gadgetColoring φ σ e.2 := by
  intro e he
  simp only [coloringEdges, List.mem_append, List.mem_flatMap] at he
  rcases he with (he | ⟨x, hx, he⟩) | ⟨⟨cl, i⟩, hi, he⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> simp [gadgetColoring_palette]
  · simp only [variableEdges, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;>
      simp only [gadgetColoring_literal σ (l := (x, true)) hx,
        gadgetColoring_literal σ (l := (x, false)) hx, gadgetColoring_palette, literalColor] <;>
      cases σ x <;> simp
  · have hi' := List.mem_zipIdx_iff_getElem?.1 hi
    simp only at hi'
    obtain ⟨hilt, hcl⟩ := List.getElem?_eq_some_iff.1 hi'
    have hφi : φ.getD i [] = cl := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hilt, Option.getD_some, hcl]
    have hmem : cl ∈ φ := hcl ▸ List.getElem_mem hilt
    have hsat : (cl.take cl.length).any (Literal.eval σ) = true := by
      rw [List.take_length]
      exact (CNF.eval_eq_true_iff _ _).1 hσ cl hmem
    simp only [clauseEdges, List.mem_append, List.mem_flatMap] at he
    rcases he with he | ⟨⟨l, j⟩, hj, he⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;>
        simp only [gadgetColoring_palette, gadgetColoring_output, hφi, outputColor, hsat] <;>
        simp
    · have hj' := List.mem_zipIdx_iff_getElem?.1 hj
      simp only at hj'
      obtain ⟨hjlt, hl⟩ := List.getElem?_eq_some_iff.1 hj'
      have hlv : l.1 ∈ φ.vars := fst_mem_vars hmem (hl ▸ List.getElem_mem hjlt)
      have hsucc := outputColor_succ (σ := σ) hjlt
      rw [hl] at hsucc
      have hgetD : cl.getD j (0, false) = l := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjlt, Option.getD_some, hl]
      have ha : outputColor σ cl j = 0 ∨ outputColor σ cl j = 1 := by
        unfold outputColor; split_ifs <;> simp
      have hb : literalColor σ l = 0 ∨ literalColor σ l = 1 := by
        unfold literalColor; split_ifs <;> simp
      simp only [stageEdges, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl <;>
        simp only [gadgetColoring_stage₀, gadgetColoring_stage₁, gadgetColoring_output,
          gadgetColoring_literal σ hlv, hφi, hgetD, hsucc] <;>
        split_ifs <;> omega

/-- **Correctness of the 3-coloring reduction.** A formula is satisfiable exactly when its gadget
graph is 3-colorable. -/
theorem toThreeColoring_mem_iff (φ : CNF ℕ) : toThreeColoring φ ∈ ThreeColoring ↔ φ ∈ SAT := by
  rw [mem_KColoring_iff]
  constructor
  · rintro ⟨c, hlt, hadj⟩
    refine satisfiable_of_coloring (c := c) fun e he => ?_
    obtain ⟨h₁, h₂⟩ := mem_endpoints he
    refine ⟨hadj _ h₁ _ h₂ ?_, hlt _ h₁, hlt _ h₂⟩
    simp only [toThreeColoring, Graph.toSimpleGraph, SimpleGraph.fromRel_adj]
    exact ⟨ne_of_mem_coloringEdges he, Or.inl he⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨gadgetColoring φ σ, fun v _ => ?_, fun u _ v _ huv => ?_⟩
    · unfold gadgetColoring
      split
      · exact Nat.mod_lt _ (by norm_num)
      · unfold literalColor; split_ifs <;> simp
      · dsimp only
        split
        · split_ifs <;> simp
        · split_ifs <;> simp
        · unfold outputColor; split_ifs <;> simp
    · simp only [toThreeColoring, Graph.toSimpleGraph, SimpleGraph.fromRel_adj] at huv
      rcases huv.2 with h | h
      · exact gadgetColoring_ne hσ _ h
      · exact (gadgetColoring_ne hσ _ h).symm

/-! ### Polynomial-time reduction -/

/-- The reduction `toThreeColoring` is computable in polynomial time: vertex labels are computed in
unary from clause, position and first-occurrence indices, then converted to binary. -/
@[fun_prop]
theorem computableTidilyInPolyTime_toThreeColoring :
    ComputableTidilyInPolyTime toThreeColoring encCNF encGraph := by
  have hlit : ComputableTidilyInPolyTime (fun p : CNF ℕ × Literal ℕ => literalVertex p.1 p.2)
      (encPair encCNF (encPair encNat encBool)) encNat := by
    unfold literalVertex
    exact unary_to_binary.comp (by fun_prop)
  have hgad : ComputableTidilyInPolyTime (fun p : ℕ × ℕ × ℕ => gadgetVertex p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encUnary encUnary)) encNat := by
    unfold gadgetVertex
    exact unary_to_binary.comp (by fun_prop)
  unfold toThreeColoring coloringEdges clauseEdges stageEdges variableEdges encGraph
  fun_prop

end SAT

/-- `SAT` reduces to `ThreeColoring` in polynomial time via `SAT.toThreeColoring`. -/
theorem polyTimeReducible_SAT_ThreeColoring :
    PolyTimeReducible encCNF encGraph SAT ThreeColoring :=
  ⟨SAT.toThreeColoring, SAT.computableTidilyInPolyTime_toThreeColoring,
    fun φ => (SAT.toThreeColoring_mem_iff φ).symm⟩

/-- `ThreeSAT` reduces to `ThreeColoring` in polynomial time: a formula with a clause of more than
three literals is mapped to the gadget graph of the empty clause, which is not 3-colorable. -/
theorem polyTimeReducible_ThreeSAT_ThreeColoring :
    PolyTimeReducible encCNF encGraph ThreeSAT ThreeColoring := by
  refine ⟨fun φ => if φ.all (fun c => decide (c.length ≤ 3)) then SAT.toThreeColoring φ
    else SAT.toThreeColoring [[]], by fun_prop, fun φ => ?_⟩
  simp only [ThreeSAT, Set.mem_ofPred_eq]
  split_ifs with h
  · rw [SAT.toThreeColoring_mem_iff, mem_SAT]
    simp only [List.all_eq_true, decide_eq_true_eq] at h
    exact ⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩
  · rw [SAT.toThreeColoring_mem_iff, mem_SAT]
    simp only [List.all_eq_true, decide_eq_true_eq] at h
    refine ⟨fun h' => (h h'.1).elim, fun ⟨σ, hσ⟩ => ?_⟩
    simp at hσ

/-- `ThreeColoring` is `NP`-hard. -/
theorem ThreeColoring_npHard : NPHard encGraph ThreeColoring :=
  CookLevin.SAT_npHard.trans polyTimeReducible_SAT_ThreeColoring

/-- **`ThreeColoring` is NP-complete.** -/
theorem ThreeColoring_npComplete : NPComplete encGraph ThreeColoring :=
  ⟨KColoring.mem_NP 3, ThreeColoring_npHard⟩

end Cslib.Complexity
