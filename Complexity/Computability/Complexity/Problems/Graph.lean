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
* Problems asking for an ordering of the vertices of a list, each vertex listed once, with a
  polynomial-time property, such as Hamiltonian paths and tours, are in `NP`: the ordering is the
  witness (`Cslib.Complexity.Graph.mem_NP_of_ordering`, through
  `Cslib.Complexity.mem_NP_of_witness` [Papadimitriou, Proposition 9.1][Papadimitriou94]).
* Explicit verifiers with fixed certificate lengths write numbers in unary blocks of a certificate
  (`Cslib.Complexity.unaryBlocks`): each number, at most `m`, gets its own block of `m` bits, and
  it is read back by counting the set bits of its block (`Cslib.Complexity.countP_unaryBlocks`).

## Main definitions

* `Cslib.Complexity.Graph.distinctVertices`: the declared vertices without repetitions.
* `Cslib.Complexity.Graph.enumeratesBool`: executable test that a list lists every vertex of
  another exactly once.
* `Cslib.Complexity.unaryBlocks`: numbers written in unary blocks of a certificate.

## Main results

* `Cslib.Complexity.Graph.length_vertices_le_encGraph`: a graph has no more declared vertices than
  the length of its encoding.
* `Cslib.Complexity.Graph.mem_NP_of_ordering`: orderings with a polynomial-time property are
  `NP` witnesses.
* `Cslib.Complexity.countP_unaryBlocks`: counting the set bits of a block reads its number.

## References

* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94]
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

theorem mem_distinctVertices {G : Graph} {v : ℕ} : v ∈ G.distinctVertices ↔ v ∈ G.1 :=
  mem_selectDistinct_replicate

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

/-! ### Orderings of vertices -/

/-- Executable test that `p` lists every vertex of `V` exactly once and nothing else. -/
def enumeratesBool (V p : List ℕ) : Bool :=
  (V.all fun v => p.any fun u => decide (u = v)) &&
    (p.all fun u => V.any fun v => decide (v = u)) &&
    p.zipIdx.all fun e => decide (p.idxOf e.1 = e.2)

/-- `enumeratesBool V p` holds exactly when `p` lists the members of `V` without repetition. -/
theorem enumeratesBool_eq_true_iff {V p : List ℕ} :
    enumeratesBool V p = true ↔ p.Nodup ∧ ∀ v, v ∈ p ↔ v ∈ V := by
  have hnodup : (∀ e ∈ p.zipIdx, p.idxOf e.1 = e.2) ↔ p.Nodup := by
    constructor
    · intro h
      rw [List.nodup_iff_injective_get]
      rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simp only [List.get_eq_getElem] at hij
      have hi' : p.idxOf p[i] = i := h (p[i], i) (List.mem_zipIdx_iff_getElem?.2 (by simp))
      have hj' : p.idxOf p[j] = j := h (p[j], j) (List.mem_zipIdx_iff_getElem?.2 (by simp))
      rw [hij] at hi'
      exact Fin.ext (hi'.symm.trans hj')
    · intro hnd e he
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 he)
      rw [← heq, hnd.idxOf_getElem]
  simp only [enumeratesBool, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq, hnodup]
  constructor
  · rintro ⟨⟨hV, hp⟩, hnd⟩
    refine ⟨hnd, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · obtain ⟨u, hu, rfl⟩ := hp v hv
      exact hu
    · obtain ⟨u, hu, rfl⟩ := hV v hv
      exact hu
  · rintro ⟨hnd, hmem⟩
    exact ⟨⟨fun v hv => ⟨v, (hmem v).2 hv, rfl⟩, fun u hu => ⟨u, (hmem u).1 hu, rfl⟩⟩, hnd⟩

/-- Testing whether a list lists every vertex of another exactly once is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_enumeratesBool :
    ComputableTidilyInPolyTime (fun x : List ℕ × List ℕ => enumeratesBool x.1 x.2)
      (encPair (encList encNat) (encList encNat)) encBool := by
  unfold enumeratesBool
  fun_prop

private theorem length_encList_le_of_subperm {γ : Type} (enc : γ ↪ List Bool) {l l' : List γ}
    (h : l.Subperm l') : (encList enc l).length ≤ (encList enc l').length := by
  obtain ⟨l'', hperm, hsub⟩ := h
  rw [length_encList, length_encList, ← (hperm.map _).sum_eq]
  exact (hsub.map _).sum_le_sum fun _ _ => Nat.zero_le _

/-- **Orderings as witnesses.** If the vertex lists `V a` and the test `check` are
polynomial-time and `check` decides `P`, then having an ordering of the vertices of `V a`, each
listed once, with the property `P` is in `NP`. The ordering itself is the witness
(`Cslib.Complexity.mem_NP_of_witness`); it is no longer than `V a`. -/
theorem mem_NP_of_ordering {α : Type} {enc : α ↪ List Bool} {V : α → List ℕ}
    {check : α → List ℕ → Bool} {P : α → List ℕ → Prop}
    (hV : ComputableTidilyInPolyTime V enc (encList encNat))
    (hcheck : ComputableTidilyInPolyTime (fun q : α × List ℕ => check q.1 q.2)
      (encPair enc (encList encNat)) encBool)
    (hP : ∀ a p, check a p = true ↔ P a p) :
    {a | ∃ p, p.Nodup ∧ (∀ v, v ∈ p ↔ v ∈ V a) ∧ P a p} ∈ NP enc := by
  obtain ⟨c, d, hle⟩ := hV.polyBounded_length.exists_le
  refine mem_NP_of_witness (Decoder.list Decoder.nat) (p := Polynomial.C c * (Polynomial.X + 1) ^ d)
    (check := fun q => enumeratesBool (V q.1) q.2 && check q.1 q.2)
    (R := fun a p => p.Nodup ∧ (∀ v, v ∈ p ↔ v ∈ V a) ∧ P a p)
    ((computableTidilyInPolyTime_enumeratesBool.comp ((hV.comp (fst _ _)).prod (snd _ _))).bool_and'
      hcheck) (fun a p => ?_) fun a p hp => ⟨p, hp, ?_⟩
  · rw [Bool.and_eq_true, enumeratesBool_eq_true_iff, hP, and_assoc]
  · refine (length_encList_le_of_subperm encNat
      (List.subperm_of_subset hp.1 fun v hv => (hp.2.1 v).1 hv)).trans ?_
    simpa using hle a

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
