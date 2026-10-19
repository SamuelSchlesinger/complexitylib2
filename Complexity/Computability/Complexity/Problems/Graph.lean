/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.IndependentSet
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Declared vertices of encoded graphs

Shared tools for the graph problems, whose graphs (`Cslib.Complexity.Graph`) are a list of
declared vertices, possibly with repetitions, and a list of edges.

* The distinct declared vertices (`Cslib.Complexity.Graph.distinctVertices`) are listed in
  polynomial time by selecting every first occurrence (`Cslib.Complexity.selectDistinct`).
* Explicit verifiers with fixed certificate lengths write numbers in unary blocks of a certificate
  (`Cslib.Complexity.unaryBlocks`): each number, at most `m`, gets its own block of `m` bits, and
  it is read back by counting the set bits of its block (`Cslib.Complexity.countP_unaryBlocks`).

## Main definitions

* `Cslib.Complexity.Graph.distinctVertices`: the declared vertices without repetitions.
* `Cslib.Complexity.unaryBlocks`: numbers written in unary blocks of a certificate.

## Main results

* `Cslib.Complexity.Graph.length_vertices_le_encGraph`: a graph has no more declared vertices than
  the length of its encoding.
* `Cslib.Complexity.countP_unaryBlocks`: counting the set bits of a block reads its number.
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableTidilyInPolyTime

namespace Graph

/-! ### Declared vertices -/

/-- A graph has no more declared vertices than the length of its encoding. -/
theorem length_vertices_le_encGraph (G : Graph) : G.1.length ≤ (encGraph G).length := by
  calc G.1.length ≤ (encList encNat G.1).length := length_le_length_encList encNat G.1
    _ ≤ (encGraph G).length := by
        simp only [encGraph, length_encPair]
        omega

/-- The declared vertices of `G` without repetitions, in the order of their first occurrences. -/
def distinctVertices (G : Graph) : List ℕ := selectDistinct G.1 (List.replicate G.1.length true)

/-- The distinct declared vertices are the declared vertices. -/
theorem mem_distinctVertices {G : Graph} {v : ℕ} : v ∈ G.distinctVertices ↔ v ∈ G.1 :=
  mem_selectDistinct_replicate

/-- The distinct declared vertices are listed without repetitions. -/
theorem nodup_distinctVertices (G : Graph) : G.distinctVertices.Nodup := nodup_selectDistinct _ _

/-- The distinct declared vertices are as many as the elements of the vertex list. -/
theorem length_distinctVertices (G : Graph) : G.distinctVertices.length = G.1.toFinset.card :=
  length_selectDistinct_replicate G.1

/-- A graph has no more distinct vertices than the length of its encoding. -/
theorem length_distinctVertices_le (G : Graph) :
    G.distinctVertices.length ≤ (encGraph G).length := by
  rw [length_distinctVertices]
  exact G.1.toFinset_card_le.trans G.length_vertices_le_encGraph

/-- Listing the distinct vertices is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_distinctVertices :
    ComputableTidilyInPolyTime distinctVertices encGraph (encList encNat) := by
  unfold distinctVertices encGraph
  fun_prop

end Graph

/-! ### Unary blocks -/

/-- The certificate of `N` bits writing the numbers `f a` in unary blocks of width `m`: bit
`m * a + c` is set when `c < f a`. -/
def unaryBlocks (m N : ℕ) (f : ℕ → ℕ) : List Bool :=
  (List.range N).map fun j => decide (j % m < f (j / m))

@[simp]
theorem length_unaryBlocks (m N : ℕ) (f : ℕ → ℕ) : (unaryBlocks m N f).length = N := by
  simp [unaryBlocks]

/-- Counting the set bits of block `a` of `unaryBlocks m N f` reads `f a`, when `f a` fits in the
block and the block fits in the certificate. -/
theorem countP_unaryBlocks {m N a : ℕ} {f : ℕ → ℕ} (hf : f a ≤ m) (hN : m * (a + 1) ≤ N) :
    ((List.range m).countP fun c => (unaryBlocks m N f).getD (m * a + c) false) = f a := by
  have hcount : ∀ k, (List.range k).countP (fun c => decide (c < f a)) = min (f a) k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [List.range_succ, List.countP_append, ih, List.countP_singleton,
        decide_eq_true_eq]
      split_ifs <;> omega
  rw [← min_eq_left hf, ← hcount]
  refine List.countP_congr fun c hc => ?_
  rw [List.mem_range] at hc
  have hm : 0 < m := by omega
  have hlt : m * a + c < N := by
    calc m * a + c < m * (a + 1) := by rw [Nat.mul_succ]; omega
      _ ≤ N := hN
  have hdiv : (m * a + c) / m = a := by rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hc, Nat.add_zero]
  have hmod : (m * a + c) % m = c := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc]
  simp only [unaryBlocks, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt,
    Option.map_some, Option.getD_some, hdiv, hmod]

end Cslib.Complexity
