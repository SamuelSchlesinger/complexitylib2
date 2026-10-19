/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Problems.Coloring
import Complexity.Computability.Complexity.Problems.VertexCover
import Complexity.Tactic.PolyTime

/-!
# NP-complete graph problem tests

Concrete, boundary, `fun_prop`, and axiom checks for `VertexCover`, `KColoring` and
`ThreeColoring`.
-/

namespace ComplexityTests.NPCompleteGraphs

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Headline complexity class results -/

example : VertexCover ∈ NP (encPair encGraph encNat) := VertexCover.mem_NP
example : NPHard (encPair encGraph encNat) VertexCover := VertexCover_npHard
example : NPComplete (encPair encGraph encNat) VertexCover := VertexCover_npComplete

example (k : ℕ) : KColoring k ∈ NP encGraph := KColoring.mem_NP k
example : NPHard encGraph ThreeColoring := ThreeColoring_npHard
example : NPComplete encGraph ThreeColoring := ThreeColoring_npComplete

example : PolyTimeReducible encCNF encGraph ThreeSAT ThreeColoring :=
  polyTimeReducible_ThreeSAT_ThreeColoring

example : PolyTimeReducible encCNF (encPair encGraph encNat) SAT VertexCover :=
  polyTimeReducible_SAT_IndependentSet.trans polyTimeReducible_IndependentSet_VertexCover

/-! ### Compositional `fun_prop` synthesis -/

example : ComputableTidilyInPolyTime IndependentSet.toVertexCover (encPair encGraph encNat)
    (encPair encGraph encNat) := by
  fun_prop

example : ComputableTidilyInPolyTime VertexCover.verifier
    (encPair (encPair encGraph encNat) encBits) encBool := by
  fun_prop

example : ComputableTidilyInPolyTime (KColoring.verifier 3) (encPair encGraph encBits) encBool := by
  fun_prop

example : ComputableTidilyInPolyTime SAT.toThreeColoring encCNF encGraph := by fun_prop

example : ComputableTidilyInPolyTime (fun φ => IndependentSet.toVertexCover (SAT.toIndependentSet φ))
    encCNF (encPair encGraph encNat) := by
  fun_prop

/-! ### `VertexCover` concrete and boundary tests -/

private def triangle : Graph := ([0, 1, 2], [(0, 1), (1, 2), (2, 0)])

-- A triangle has vertex covers with two vertices but none with one.
example : VertexCover.verifier ((triangle, 2), [true, true, false]) = true := rfl
example : VertexCover.verifier ((triangle, 2), [false, true, true]) = true := rfl
example : VertexCover.verifier ((triangle, 1), [true, false, false]) = false := rfl
example : VertexCover.verifier ((triangle, 2), [true, false, false]) = false := rfl

example : (triangle, 2) ∈ VertexCover := by
  rw [mem_VertexCover_iff]
  refine ⟨{0, 1}, by decide, fun u hu v hv huv => ?_, rfl⟩
  simp only [triangle, List.mem_cons, List.not_mem_nil, or_false] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    first | exact (huv.ne rfl).elim | simp

example : (triangle, 1) ∉ VertexCover := by
  rw [mem_VertexCover_iff]
  rintro ⟨S, -, hS, hcard⟩
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.1 hcard
  have h₀₁ := hS 0 (by simp [triangle]) 1 (by simp [triangle])
    ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  have h₁₂ := hS 1 (by simp [triangle]) 2 (by simp [triangle])
    ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  have h₂₀ := hS 2 (by simp [triangle]) 0 (by simp [triangle])
    ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  simp only [Finset.mem_singleton] at h₀₁ h₁₂ h₂₀
  omega

-- Empty graph: `k = 0` is accepted and `k = 1` is rejected.
example : VertexCover.verifier ((([], []), 0), []) = true := rfl
example : VertexCover.verifier ((([], []), 1), [true]) = false := rfl

-- Duplicate vertices count once: two copies of `0` do not make a cover with two vertices.
example : VertexCover.verifier ((([0, 0, 1], [(0, 1)]), 2), [true, true, false]) = false := rfl
example : VertexCover.verifier ((([0, 0, 1], [(0, 1)]), 1), [true, false, false]) = true := rfl

-- Edges with an undeclared endpoint and self-loops are ignored.
example : VertexCover.verifier
    ((([10, 20], [(10, 99), (99, 20), (10, 10)]), 0), [false, false]) = true := rfl

-- An oversized binary target `k = 2 ^ 100` is rejected without unary expansion.
example : VertexCover.verifier ((([0, 1], [(0, 1)]), 2 ^ 100), [true, true]) = false := by
  decide

-- The reduction complements the target within the distinct declared vertices, and maps an
-- oversized target `m > n` to the unsatisfiable target `n + 1`.
example : IndependentSet.toVertexCover (triangle, 1) = (triangle, 2) := by decide
example : IndependentSet.toVertexCover (([0, 0, 1], []), 2) = (([0, 0, 1], []), 0) := by decide
example : IndependentSet.toVertexCover (triangle, 4) = (triangle, 4) := by decide
example : IndependentSet.toVertexCover (([], []), 0) = (([], []), 0) := by decide

/-! ### `KColoring` and `ThreeColoring` concrete and boundary tests -/

-- A certificate from a coloring `c`: block `i` of `k` bits has `c` of vertex `i` set bits.
private def certificate (k : ℕ) (G : Graph) (c : ℕ → ℕ) : List Bool :=
  (List.range (k * G.1.length)).map fun j => decide (j % k < c (G.1.getD (j / k) 0))

-- Colors are counts of set bits in each vertex's block of `k` bits.
example : KColoring.colorOf 3 [5, 7] [true, false, false, true, true, false] 7 = 2 := rfl
example : KColoring.colorOf 3 [5, 7] [true, false, false, true, true, false] 5 = 1 := rfl

-- The triangle is 3-colorable but not 2-colorable.
example : KColoring.verifier 3 (triangle, certificate 3 triangle id) = true := rfl
example : KColoring.verifier 2 (triangle, [false, false, true, false, true, true]) = false := rfl

example : triangle ∈ ThreeColoring := by
  rw [mem_KColoring_iff]
  refine ⟨id, by decide, fun u _ v _ huv => huv.ne⟩

example : triangle ∉ KColoring 2 := by
  rw [mem_KColoring_iff]
  rintro ⟨c, hc, hadj⟩
  have h₀ := hc 0 (by simp [triangle])
  have h₁ := hc 1 (by simp [triangle])
  have h₂ := hc 2 (by simp [triangle])
  have h₀₁ := hadj 0 (by simp [triangle]) 1 (by simp [triangle])
    ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  have h₁₂ := hadj 1 (by simp [triangle]) 2 (by simp [triangle])
    ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  have h₂₀ := hadj 2 (by simp [triangle]) 0 (by simp [triangle])
    ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  omega

-- The complete graph on four vertices is not 3-colorable.
private def k4 : Graph := ([0, 1, 2, 3], [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)])

example : k4 ∉ ThreeColoring := by
  rw [mem_KColoring_iff]
  rintro ⟨c, hc, hadj⟩
  have h₀ := hc 0 (by simp [k4])
  have h₁ := hc 1 (by simp [k4])
  have h₂ := hc 2 (by simp [k4])
  have h₃ := hc 3 (by simp [k4])
  have h₀₁ := hadj 0 (by simp [k4]) 1 (by simp [k4]) ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  have h₀₂ := hadj 0 (by simp [k4]) 2 (by simp [k4]) ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  have h₀₃ := hadj 0 (by simp [k4]) 3 (by simp [k4]) ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  have h₁₂ := hadj 1 (by simp [k4]) 2 (by simp [k4]) ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  have h₁₃ := hadj 1 (by simp [k4]) 3 (by simp [k4]) ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  have h₂₃ := hadj 2 (by simp [k4]) 3 (by simp [k4]) ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  omega

example : KColoring.verifier 4 (k4, certificate 4 k4 id) = true := rfl

-- A block with all bits set encodes the out-of-range color `k`.
example : KColoring.verifier 3 (([0], []), [true, true, true]) = false := rfl

-- With `k = 0`, exactly the graphs without declared vertices are colorable.
example : KColoring.verifier 0 (([], [(0, 1)]), []) = true := rfl
example : KColoring.verifier 0 (([0], []), []) = false := rfl

-- Duplicate vertices share the block of their first occurrence; undeclared edges are ignored.
example : KColoring.verifier 2 (([0, 1, 0], [(0, 1), (1, 7), (7, 0)]), [false, false, true, false]) =
    true := rfl

/-! ### The 3-coloring gadget -/

-- The gadget graph of the empty formula is the palette triangle.
example : (SAT.toThreeColoring []).2 = [(0, 1), (1, 4), (4, 0)] := by decide
example : SAT.toThreeColoring [] ∈ ThreeColoring :=
  (SAT.toThreeColoring_mem_iff _).2 ⟨fun _ => true, rfl⟩

-- The stage `0` output of an empty clause is adjacent to all three palette vertices.
example : (SAT.toThreeColoring [[]]).2 =
    [(0, 1), (1, 4), (4, 0), (258, 0), (258, 4), (258, 1), (258, 4)] := by decide
example : SAT.toThreeColoring [[]] ∉ ThreeColoring := by
  rw [SAT.toThreeColoring_mem_iff]
  rintro ⟨σ, hσ⟩
  simp at hσ

-- A satisfiable formula: a coloring certificate read off a satisfying assignment.
private def unitFormula : CNF ℕ := [[(0, true)]]

private def unitColoring (v : ℕ) : ℕ :=
  if v = SAT.paletteVertex 1 ∨ v = SAT.literalVertex unitFormula (0, false) ∨
      v = SAT.gadgetVertex 0 0 2 ∨ v = SAT.gadgetVertex 0 1 1 then 1
  else if v = SAT.paletteVertex 2 ∨ v = SAT.gadgetVertex 0 1 0 then 2
  else 0

example : KColoring.verifier 3 (SAT.toThreeColoring unitFormula,
    certificate 3 (SAT.toThreeColoring unitFormula) unitColoring) = true := by decide

-- Complementary unit clauses: the gadget graph is not 3-colorable.
example : SAT.toThreeColoring [[(0, true)], [(0, false)]] ∉ ThreeColoring := by
  rw [SAT.toThreeColoring_mem_iff]
  rintro ⟨σ, hσ⟩
  cases h : σ 0 <;> simp [h] at hσ

-- A clause of width four is handled by the chain of OR gadgets.
example : SAT.toThreeColoring [[(0, false), (1, false), (2, false), (3, true)]] ∈ ThreeColoring :=
  (SAT.toThreeColoring_mem_iff _).2 ⟨fun _ => true, rfl⟩

/-! ### Axiom checks for headline theorems -/

/--
info: 'Cslib.Complexity.IndependentSet.toVertexCover_mem_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.IndependentSet.toVertexCover_mem_iff

/--
info: 'Cslib.Complexity.IndependentSet.computableTidilyInPolyTime_toVertexCover' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.IndependentSet.computableTidilyInPolyTime_toVertexCover

/--
info: 'Cslib.Complexity.VertexCover.mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.VertexCover.mem_NP

/--
info: 'Cslib.Complexity.VertexCover_npHard' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.VertexCover_npHard

/--
info: 'Cslib.Complexity.VertexCover_npComplete' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.VertexCover_npComplete

/--
info: 'Cslib.Complexity.KColoring.mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.KColoring.mem_NP

/--
info: 'Cslib.Complexity.SAT.toThreeColoring_mem_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SAT.toThreeColoring_mem_iff

/--
info: 'Cslib.Complexity.SAT.computableTidilyInPolyTime_toThreeColoring' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SAT.computableTidilyInPolyTime_toThreeColoring

/--
info: 'Cslib.Complexity.polyTimeReducible_ThreeSAT_ThreeColoring' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.polyTimeReducible_ThreeSAT_ThreeColoring

/--
info: 'Cslib.Complexity.ThreeColoring_npHard' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ThreeColoring_npHard

/--
info: 'Cslib.Complexity.ThreeColoring_npComplete' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ThreeColoring_npComplete

end ComplexityTests.NPCompleteGraphs
