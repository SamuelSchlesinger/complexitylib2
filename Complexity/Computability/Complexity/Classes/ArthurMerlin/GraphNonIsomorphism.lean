/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.ArthurMerlin.SetLowerBound
public import Complexity.Computability.Complexity.Problems.GraphIsomorphism
public import Mathlib.Data.Nat.Factorial.Basic

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Factorial
import Complexity.Foundations.Data.BitString.Basic
import Mathlib.Data.List.GetD

/-!
# Graph non-isomorphism is in AM

The public-coin protocol of Goldwasser and Sipser for graph non-isomorphism
[GoldwasserSipser1986], [Arora and Barak, Section 8.2][AroraBarak09]. Let the two graphs have
`n` distinct vertices each, with adjacency matrices `A₀` and `A₁` on positions. Permutations `τ`
relabel matrices (`Cslib.Complexity.GraphNonIsomorphism.PublicCoin.relabelMatrix`), and the pairs
`(M, σ)` of a relabelling `M` of `A₀` or `A₁` and an automorphism `σ` of `M` form a set of
`2 n!` elements when the graphs are not isomorphic and `n!` when they are
(`Cslib.Complexity.GraphNonIsomorphism.PublicCoin.card_pairs_union`): by the orbit–stabilizer
count, each orbit contributes `n!` pairs
(`Cslib.Complexity.GraphNonIsomorphism.PublicCoin.card_pairs`), and the two orbits coincide or are
disjoint.

Merlin can certify membership of a pair, by naming the graph and a relabelling of it. Pairs are
written as strings of `2 L² + 1` bits, `L` the length of the encoded instance
(`Cslib.Complexity.GraphNonIsomorphism.PublicCoin.code`): the matrix `M`, the matrix of `σ`, and
`false` bits. When the graphs have different numbers of vertices, every string is accepted. The
set lower bound protocol with threshold `2 n!` (`Cslib.Complexity.mem_AM_of_card_certifiedSet`)
then gives `GraphNonIsomorphism ∈ AM` (`Cslib.Complexity.GraphNonIsomorphism.mem_AM`). The
private-coin protocol in `Complexity.Computability.Complexity.Classes.IP.GraphNonIsomorphism` is
not used.

## Main definitions

* `Cslib.Complexity.GraphNonIsomorphism.PublicCoin.relabelMatrix`: relabelling a matrix.
* `Cslib.Complexity.GraphNonIsomorphism.PublicCoin.orbit`,
  `Cslib.Complexity.GraphNonIsomorphism.PublicCoin.pairs`: relabellings, and relabellings with an
  automorphism.
* `Cslib.Complexity.GraphNonIsomorphism.PublicCoin.code`,
  `Cslib.Complexity.GraphNonIsomorphism.PublicCoin.test`: strings of pairs and their certificates.

## Main results

* `Cslib.Complexity.GraphNonIsomorphism.PublicCoin.card_pairs`: an orbit gives `n!` pairs.
* `Cslib.Complexity.GraphNonIsomorphism.PublicCoin.card_pairs_union`: `2 n!` or `n!` pairs.
* `Cslib.Complexity.GraphNonIsomorphism.PublicCoin.card_filter_check`: the certified strings
  correspond to the pairs.
* `Cslib.Complexity.GraphNonIsomorphism.mem_GraphIsomorphism_iff_mem_orbit`: isomorphism as
  relabelling of adjacency matrices.
* `Cslib.Complexity.GraphNonIsomorphism.mem_AM`: graph non-isomorphism is in `AM`.

## References

* [S. Goldwasser, M. Sipser, *Private coins versus public coins in interactive proof
  systems*][GoldwasserSipser1986]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

namespace GraphNonIsomorphism

namespace PublicCoin

/-! ### Relabelling matrices -/

variable {n : ℕ}

/-- Relabel the rows and columns of a matrix by a permutation `τ`: entry `(τ i, τ j)` of the
result is entry `(i, j)` of `M`. -/
def relabelMatrix (τ : Equiv.Perm (Fin n)) (M : Fin n → Fin n → Bool) : Fin n → Fin n → Bool :=
  fun i j => M (τ.symm i) (τ.symm j)

theorem relabelMatrix_mul (σ τ : Equiv.Perm (Fin n)) (M : Fin n → Fin n → Bool) :
    relabelMatrix (σ * τ) M = relabelMatrix σ (relabelMatrix τ M) := by
  funext i j
  simp [relabelMatrix, Equiv.Perm.mul_def]

theorem relabelMatrix_one (M : Fin n → Fin n → Bool) : relabelMatrix 1 M = M := rfl

/-- `relabelMatrix τ A = M` says that `τ` carries `A` to `M`. -/
theorem relabelMatrix_eq_iff {τ : Equiv.Perm (Fin n)} {A M : Fin n → Fin n → Bool} :
    relabelMatrix τ A = M ↔ ∀ i j, M (τ i) (τ j) = A i j := by
  constructor
  · rintro rfl i j
    simp [relabelMatrix]
  · intro h
    funext i j
    simpa [relabelMatrix] using (h (τ.symm i) (τ.symm j)).symm

/-- The relabellings of a matrix. -/
def orbit (A : Fin n → Fin n → Bool) : Finset (Fin n → Fin n → Bool) :=
  univ.image fun τ => relabelMatrix τ A

theorem mem_orbit {A M : Fin n → Fin n → Bool} : M ∈ orbit A ↔ ∃ τ, relabelMatrix τ A = M := by
  simp [orbit]

theorem mem_orbit_self (A : Fin n → Fin n → Bool) : A ∈ orbit A :=
  mem_orbit.2 ⟨1, rfl⟩

theorem mem_orbit_trans {A B M : Fin n → Fin n → Bool} (hB : B ∈ orbit A) (hM : M ∈ orbit B) :
    M ∈ orbit A := by
  obtain ⟨τ, rfl⟩ := mem_orbit.1 hB
  obtain ⟨σ, rfl⟩ := mem_orbit.1 hM
  exact mem_orbit.2 ⟨σ * τ, relabelMatrix_mul σ τ A⟩

theorem mem_orbit_symm {A B : Fin n → Fin n → Bool} (hB : B ∈ orbit A) : A ∈ orbit B := by
  obtain ⟨τ, rfl⟩ := mem_orbit.1 hB
  refine mem_orbit.2 ⟨τ⁻¹, ?_⟩
  rw [← relabelMatrix_mul, inv_mul_cancel, relabelMatrix_one]

/-- The pairs of a relabelling of `A` and an automorphism of it. -/
def pairs (A : Fin n → Fin n → Bool) :
    Finset ((Fin n → Fin n → Bool) × Equiv.Perm (Fin n)) :=
  univ.filter fun p => p.1 ∈ orbit A ∧ relabelMatrix p.2 p.1 = p.1

/-- A relabelling `M` of `A` has as many automorphisms as there are permutations carrying `A` to
`M`. -/
theorem card_filter_relabelMatrix_eq {A M : Fin n → Fin n → Bool} (hM : M ∈ orbit A) :
    #{σ : Equiv.Perm (Fin n) | relabelMatrix σ M = M} =
      #{τ : Equiv.Perm (Fin n) | relabelMatrix τ A = M} := by
  obtain ⟨τ₀, rfl⟩ := mem_orbit.1 hM
  refine card_equiv (Equiv.mulRight τ₀) fun σ => ?_
  simp only [mem_filter, mem_univ, true_and, Equiv.coe_mulRight, relabelMatrix_mul]

/-- **Orbit–stabilizer count**: the pairs of a relabelling of `A` and an automorphism of it are
`n!` many. -/
theorem card_pairs (A : Fin n → Fin n → Bool) : #(pairs A) = n.factorial := by
  have hsum : #(pairs A) = ∑ M : Fin n → Fin n → Bool,
      #{τ : Equiv.Perm (Fin n) | relabelMatrix τ A = M} := by
    rw [pairs, card_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun M _ => ?_
    by_cases hM : M ∈ orbit A
    · simp only [hM, true_and, ← card_filter_relabelMatrix_eq hM, card_filter]
    · simp only [hM, false_and, ↓reduceIte, sum_const_zero]
      symm
      rw [card_eq_zero, filter_eq_empty_iff]
      exact fun τ _ h => hM (mem_orbit.2 ⟨τ, h⟩)
  rw [hsum, ← card_eq_sum_card_fiberwise (fun _ _ => mem_univ _), card_univ,
    Fintype.card_perm, Fintype.card_fin]

/-- The pairs of the two matrices are `n!` many if one is a relabelling of the other, and `2 n!`
many otherwise. -/
theorem card_pairs_union (A₀ A₁ : Fin n → Fin n → Bool) :
    #(pairs A₀ ∪ pairs A₁) = if A₁ ∈ orbit A₀ then n.factorial else 2 * n.factorial := by
  split_ifs with h
  · have heq : pairs A₁ = pairs A₀ := by
      ext p
      simp only [pairs, mem_filter, mem_univ, true_and]
      exact and_congr_left fun _ =>
        ⟨fun hp => mem_orbit_trans h hp, fun hp => mem_orbit_trans (mem_orbit_symm h) hp⟩
    rw [heq, union_self, card_pairs]
  · rw [card_union_of_disjoint, card_pairs, card_pairs, two_mul]
    refine disjoint_left.2 fun p hp₀ hp₁ => h ?_
    simp only [pairs, mem_filter, mem_univ, true_and] at hp₀ hp₁
    exact mem_orbit_trans hp₀.1 (mem_orbit_symm hp₁.1)

/-! ### Positions -/

private theorem pos_of_fin (i : Fin n) : 0 < n := Nat.zero_lt_of_lt i.2

private theorem index_lt (i j : Fin n) : (i : ℕ) * n + j < n * n := by
  have := i.2
  have := j.2
  nlinarith

private theorem index_div (i j : Fin n) : ((i : ℕ) * n + j) / n = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (pos_of_fin i), Nat.div_eq_of_lt j.2, zero_add]

private theorem index_mod (i j : Fin n) : ((i : ℕ) * n + j) % n = j := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.2]

/-- The entry of a matrix at natural positions, `false` outside. -/
def entry (M : Fin n → Fin n → Bool) (i j : ℕ) : Bool :=
  if h : i < n ∧ j < n then M ⟨i, h.1⟩ ⟨j, h.2⟩ else false

/-- The value of a permutation at a natural position, `0` outside. -/
def value (σ : Equiv.Perm (Fin n)) (i : ℕ) : ℕ :=
  if h : i < n then σ ⟨i, h⟩ else 0

@[simp] theorem entry_fin (M : Fin n → Fin n → Bool) (i j : Fin n) :
    entry M i j = M i j := by
  simp [entry]

@[simp] theorem value_fin (σ : Equiv.Perm (Fin n)) (i : Fin n) : value σ i = σ i := by
  simp [value]

/-! ### Codes of pairs and certificates -/

/-- Bit `p` of the code of a pair `(M, σ)`: the entries of `M`, then the entries of the matrix of
`σ`, row by row, then `false`. -/
def codeBit (M : Fin n → Fin n → Bool) (σ : Equiv.Perm (Fin n)) (p : ℕ) : Bool :=
  if p < n * n then entry M (p / n) (p % n)
  else if p < 2 * (n * n) then decide (value σ ((p - n * n) / n) = (p - n * n) % n)
  else false

/-- The code of a pair `(M, σ)` of a matrix and a permutation, in `E` bits. -/
def code (E : ℕ) (M : Fin n → Fin n → Bool) (σ : Equiv.Perm (Fin n)) : BitString E :=
  fun p => codeBit M σ p

/-- Bit `q` of a certificate naming the graph `b` and a permutation `τ`. -/
def certBit (b : Bool) (τ : Equiv.Perm (Fin n)) (q : ℕ) : Bool :=
  if q = 0 then b
  else if q - 1 < n * n then decide (value τ ((q - 1) / n) = (q - 1) % n)
  else false

/-- A certificate naming the graph `b` and a permutation `τ`, in `C` bits. -/
def cert (C : ℕ) (b : Bool) (τ : Equiv.Perm (Fin n)) : BitString C :=
  fun q => certBit b τ q

private theorem getD_ofFn {E : ℕ} (x : BitString E) {p : ℕ} (hp : p < E) :
    (List.ofFn x).getD p false = x ⟨p, hp⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hp), List.getElem_ofFn]

/-- The matrix read from the first `n * n` bits of a word. -/
def decodeMatrix (n : ℕ) (u : List Bool) : Fin n → Fin n → Bool :=
  fun i j => u.getD (i * n + j) false

/-- The map read from the matrix starting after `k` bits of a word: row `i` selects its first set
bit (`Cslib.Complexity.GraphIsomorphism.image`). -/
def decodeMap (n k : ℕ) (u : List Bool) (i : Fin n) : Fin n :=
  ⟨GraphIsomorphism.image n (u.drop k) i, GraphIsomorphism.image_lt _ _ (Nat.zero_lt_of_lt i.2)⟩

theorem decodeMatrix_code {E : ℕ} (hE : n * n ≤ E) (M : Fin n → Fin n → Bool)
    (σ : Equiv.Perm (Fin n)) : decodeMatrix n (List.ofFn (code E M σ)) = M := by
  funext i j
  rw [decodeMatrix, getD_ofFn _ ((index_lt i j).trans_le hE)]
  simp only [code, codeBit, index_lt i j, ↓reduceIte, index_div, index_mod, entry_fin]

theorem decodeMap_code {E : ℕ} (hE : 2 * (n * n) ≤ E) (M : Fin n → Fin n → Bool)
    (σ : Equiv.Perm (Fin n)) : decodeMap n (n * n) (List.ofFn (code E M σ)) = σ := by
  funext i
  refine Fin.ext (GraphIsomorphism.image_eq (σ i).2 fun j hj => ?_)
  have hlt : (i : ℕ) * n + j < n * n := index_lt i ⟨j, hj⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
    getD_ofFn _ (by omega)]
  simp only [code, codeBit, show ¬(n * n + (i * n + j) < n * n) by omega,
    show n * n + (i * n + j) < 2 * (n * n) by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  rw [index_div i ⟨j, hj⟩, index_mod i ⟨j, hj⟩, value_fin]
  exact decide_eq_decide.2 eq_comm

theorem getD_ofFn_cert_zero {C : ℕ} (hC : 0 < C) (b : Bool) (τ : Equiv.Perm (Fin n)) :
    (List.ofFn (cert C b τ)).getD 0 false = b := by
  rw [getD_ofFn _ hC]
  simp [cert, certBit]

theorem decodeMap_cert {C : ℕ} (hC : n * n + 1 ≤ C) (b : Bool) (τ : Equiv.Perm (Fin n)) :
    decodeMap n 1 (List.ofFn (cert C b τ)) = τ := by
  funext i
  refine Fin.ext (GraphIsomorphism.image_eq (τ i).2 fun j hj => ?_)
  have hlt : (i : ℕ) * n + j < n * n := index_lt i ⟨j, hj⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
    getD_ofFn _ (by omega)]
  simp only [cert, certBit, show 1 + (i * n + j) ≠ 0 by omega, Nat.add_sub_cancel_left, hlt,
    ↓reduceIte]
  rw [index_div i ⟨j, hj⟩, index_mod i ⟨j, hj⟩, value_fin]
  exact decide_eq_decide.2 eq_comm

/-! ### The test -/

/-- The test of an element `u` and a certificate `v`, for matrices of size `n`, elements of `E` bits
and the adjacency `adj b i j` of graph `b`. Write `f` for the map selected by the second matrix of
`u` (`Cslib.Complexity.GraphIsomorphism.image`), `M` for the first matrix of `u`, `b` for the first
bit of `v` and `τ` for the map selected by the rest of `v`. The test accepts when the bits of `u`
after position `2 n²` are `false`, the second matrix of `u` is the matrix of `f`, `f` is an
injective automorphism of `M`, and `τ` is injective and carries the adjacency of graph `b` to
`M`. -/
def check (n E : ℕ) (adj : Bool → ℕ → ℕ → Bool) (u v : List Bool) : Bool :=
  let f := fun i => GraphIsomorphism.image n (u.drop (n * n)) i
  let τ := fun i => GraphIsomorphism.image n (v.drop 1) i
  ((List.range (E - 2 * (n * n))).all fun p => !u.getD (2 * (n * n) + p) false) &&
    (List.range n).all fun i => (List.range n).all fun j =>
      (u.getD (n * n + (i * n + j)) false == decide (f i = j)) &&
      (decide (i = j) || decide (f i ≠ f j)) &&
      (u.getD (f i * n + f j) false == u.getD (i * n + j) false) &&
      (decide (i = j) || decide (τ i ≠ τ j)) &&
      (u.getD (τ i * n + τ j) false == adj (v.getD 0 false) i j)

theorem check_eq_true_iff {n E : ℕ} {adj : Bool → ℕ → ℕ → Bool} {u v : List Bool} :
    check n E adj u v = true ↔
      (∀ p < E - 2 * (n * n), u.getD (2 * (n * n) + p) false = false) ∧
      ∀ i < n, ∀ j < n,
        u.getD (n * n + (i * n + j)) false =
          decide (GraphIsomorphism.image n (u.drop (n * n)) i = j) ∧
        (i = j ∨ GraphIsomorphism.image n (u.drop (n * n)) i ≠
          GraphIsomorphism.image n (u.drop (n * n)) j) ∧
        u.getD (GraphIsomorphism.image n (u.drop (n * n)) i * n +
          GraphIsomorphism.image n (u.drop (n * n)) j) false = u.getD (i * n + j) false ∧
        (i = j ∨ GraphIsomorphism.image n (v.drop 1) i ≠ GraphIsomorphism.image n (v.drop 1) j) ∧
        u.getD (GraphIsomorphism.image n (v.drop 1) i * n +
          GraphIsomorphism.image n (v.drop 1) j) false = adj (v.getD 0 false) i j := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_eq_eq_not,
    Bool.not_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq, ne_eq, and_assoc]

/-- The test of the protocol for graph non-isomorphism, with elements of `N(L)` bits, `L` the
length of the encoded pair of graphs: graphs with different numbers of distinct vertices pass, and
otherwise the element and the certificate must pass `check`. -/
def test (N : Polynomial ℕ) (x : (Graph × Graph) × List Bool) : Bool :=
  decide (x.1.2.distinctVertices.length ≠ x.1.1.distinctVertices.length) ||
    check x.1.1.distinctVertices.length (N.eval (encPair encGraph encGraph x.1).length)
      (fun b i j => if b then x.1.2.adjIndex i j else x.1.1.adjIndex i j)
      (x.2.take (N.eval (encPair encGraph encGraph x.1).length))
      (x.2.drop (N.eval (encPair encGraph encGraph x.1).length))

/-- The test is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_test (N : Polynomial ℕ) :
    ComputableTidilyInPolyTime (test N) (encPair (encPair encGraph encGraph) encBits) encBool := by
  unfold test check
  simp only []
  fun_prop

/-! ### Counting the certified pairs -/

/-- The permutation of an injective map of `Fin n`. -/
noncomputable def permOfInjective (f : Fin n → Fin n) (hf : Function.Injective f) :
    Equiv.Perm (Fin n) :=
  Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)

section Check

variable {E : ℕ} {adj : Bool → ℕ → ℕ → Bool} {u v : List Bool}

theorem injective_decodeMap_left (h : check n E adj u v = true) :
    Function.Injective (decodeMap n (n * n) u) := by
  intro i j hij
  rcases ((check_eq_true_iff.1 h).2 i i.2 j j.2).2.1 with h' | h'
  · exact Fin.ext h'
  · exact absurd (congrArg Fin.val hij) h'

theorem injective_decodeMap_right (h : check n E adj u v = true) :
    Function.Injective (decodeMap n 1 v) := by
  intro i j hij
  rcases ((check_eq_true_iff.1 h).2 i i.2 j j.2).2.2.2.1 with h' | h'
  · exact Fin.ext h'
  · exact absurd (congrArg Fin.val hij) h'

/-- The map selected by an accepted element is an automorphism of its matrix. -/
theorem relabelMatrix_decodeMatrix (h : check n E adj u v = true) :
    relabelMatrix (permOfInjective _ (injective_decodeMap_left h)) (decodeMatrix n u) =
      decodeMatrix n u :=
  relabelMatrix_eq_iff.2 fun i j => ((check_eq_true_iff.1 h).2 i i.2 j j.2).2.2.1

/-- The matrix of an accepted element is a relabelling of the graph named by the certificate. -/
theorem decodeMatrix_mem_orbit (h : check n E adj u v = true) :
    decodeMatrix n u ∈ orbit fun i j : Fin n => adj (v.getD 0 false) i j :=
  mem_orbit.2 ⟨permOfInjective _ (injective_decodeMap_right h),
    relabelMatrix_eq_iff.2 fun i j => ((check_eq_true_iff.1 h).2 i i.2 j j.2).2.2.2.2⟩

end Check

/-- **The certified pairs**: the elements of `E` bits with a certificate of `C` bits that passes
`check` are as many as the pairs of a relabelling of one of the two adjacency matrices and an
automorphism of it. -/
theorem card_filter_check {E C : ℕ} (hE : 2 * (n * n) + 1 ≤ E) (hC : n * n + 1 ≤ C)
    (adj : Bool → ℕ → ℕ → Bool) :
    #{x : BitString E | ∃ z : BitString C, check n E adj (List.ofFn x) (List.ofFn z) = true} =
      #(pairs (fun i j : Fin n => adj false i j) ∪ pairs fun i j : Fin n => adj true i j) := by
  refine card_bij'
    (fun x hx => (decodeMatrix n (List.ofFn x),
      permOfInjective _ (injective_decodeMap_left (mem_filter.1 hx).2.choose_spec)))
    (fun t _ => code E t.1 t.2) (fun x hx => ?_) (fun t ht => ?_) (fun x hx => ?_)
    (fun t ht => ?_)
  · -- an accepted element gives a pair
    have hz := (mem_filter.1 hx).2.choose_spec
    have horb := decodeMatrix_mem_orbit hz
    refine mem_union.2 ?_
    cases hb : (List.ofFn (mem_filter.1 hx).2.choose).getD 0 false <;> rw [hb] at horb
    · exact Or.inl (mem_filter.2 ⟨mem_univ _, horb, relabelMatrix_decodeMatrix hz⟩)
    · exact Or.inr (mem_filter.2 ⟨mem_univ _, horb, relabelMatrix_decodeMatrix hz⟩)
  · -- a pair has an accepted code
    obtain ⟨M, σ⟩ := t
    obtain ⟨b, hb⟩ : ∃ b : Bool, (M, σ) ∈ pairs fun i j : Fin n => adj b i j := by
      rcases mem_union.1 ht with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    obtain ⟨-, horb, haut⟩ := mem_filter.1 hb
    obtain ⟨τ, hτ⟩ := mem_orbit.1 horb
    refine mem_filter.2 ⟨mem_univ _, cert C b τ, check_eq_true_iff.2 ⟨fun p hp => ?_,
      fun i hi j hj => ?_⟩⟩
    · rw [getD_ofFn _ (by omega)]
      simp [code, codeBit, show ¬(2 * (n * n) + p < n * n) by omega]
    · have hf := congrArg Fin.val (congrFun (decodeMap_code (by omega : 2 * (n * n) ≤ E) M σ)
        ⟨i, hi⟩)
      have hg := congrArg Fin.val (congrFun (decodeMap_cert hC b τ) ⟨i, hi⟩)
      have hf' := congrArg Fin.val (congrFun (decodeMap_code (by omega : 2 * (n * n) ≤ E) M σ)
        ⟨j, hj⟩)
      have hg' := congrArg Fin.val (congrFun (decodeMap_cert hC b τ) ⟨j, hj⟩)
      simp only [decodeMap] at hf hg hf' hg'
      have hM := congrFun₂ (decodeMatrix_code (by omega : n * n ≤ E) M σ)
      simp only [decodeMatrix] at hM
      rw [hf, hg, hf', hg', getD_ofFn_cert_zero (by omega)]
      have hlt : i * n + j < n * n := index_lt ⟨i, hi⟩ ⟨j, hj⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [getD_ofFn _ (by omega)]
        simp only [code, codeBit, show ¬(n * n + (i * n + j) < n * n) by omega,
          show n * n + (i * n + j) < 2 * (n * n) by omega, ↓reduceIte, Nat.add_sub_cancel_left]
        rw [index_div ⟨i, hi⟩ ⟨j, hj⟩, index_mod ⟨i, hi⟩ ⟨j, hj⟩, value_fin]
      · by_cases hij : i = j
        · exact Or.inl hij
        · exact Or.inr fun h => hij (by simpa using σ.injective (Fin.ext h))
      · rw [hM, hM ⟨i, hi⟩ ⟨j, hj⟩]
        exact (relabelMatrix_eq_iff.1 haut ⟨i, hi⟩ ⟨j, hj⟩)
      · by_cases hij : i = j
        · exact Or.inl hij
        · exact Or.inr fun h => hij (by simpa using τ.injective (Fin.ext h))
      · rw [hM]
        exact relabelMatrix_eq_iff.1 hτ ⟨i, hi⟩ ⟨j, hj⟩
  · -- decoding an accepted element and coding it again gives it back
    have hz := (mem_filter.1 hx).2.choose_spec
    obtain ⟨hrest, hrows⟩ := check_eq_true_iff.1 hz
    funext p
    change codeBit _ _ p.1 = x p
    by_cases h₁ : p.1 < n * n
    · have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at h₁
      have hdiv : p.1 / n < n := Nat.div_lt_of_lt_mul h₁
      have hmod : p.1 % n < n := Nat.mod_lt _ hn
      simp only [codeBit, h₁, ↓reduceIte, entry, hdiv, hmod, and_self, ↓reduceDIte, decodeMatrix]
      rw [Nat.div_add_mod', getD_ofFn _ p.2]
    · by_cases h₂ : p.1 < 2 * (n * n)
      · have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at h₂
        have hq : p.1 - n * n < n * n := by omega
        have hdiv : (p.1 - n * n) / n < n := Nat.div_lt_of_lt_mul hq
        have hmod : (p.1 - n * n) % n < n := Nat.mod_lt _ hn
        simp only [codeBit, h₁, h₂, ↓reduceIte, value, hdiv, ↓reduceDIte, permOfInjective,
          Equiv.ofBijective_apply, decodeMap]
        rw [← (hrows _ hdiv _ hmod).1, Nat.div_add_mod', Nat.add_sub_cancel' (by omega),
          getD_ofFn _ p.2]
      · simp only [codeBit, h₁, h₂, ↓reduceIte]
        have := hrest (p.1 - 2 * (n * n)) (by omega)
        rw [Nat.add_sub_cancel' (by omega), getD_ofFn _ p.2] at this
        exact this.symm
  · -- coding a pair and decoding it gives it back
    refine Prod.ext (decodeMatrix_code (by omega) _ _) (Equiv.ext fun i => ?_)
    simp only [permOfInjective, Equiv.ofBijective_apply]
    exact congrFun (decodeMap_code (by omega) _ _) i

end PublicCoin

open PublicCoin

/-- Isomorphic graphs have equally many distinct vertices. -/
theorem length_distinctVertices_eq_of_mem_GraphIsomorphism {G₀ G₁ : Graph}
    (h : (G₀, G₁) ∈ GraphIsomorphism) :
    G₁.distinctVertices.length = G₀.distinctVertices.length := by
  obtain ⟨σ, -⟩ := mem_GraphIsomorphism_iff.1 h
  simpa using (Fintype.card_congr σ).symm

/-- Graphs with equally many distinct vertices are isomorphic exactly when the adjacency matrix of
the second, on positions, is a relabelling of that of the first. -/
theorem mem_GraphIsomorphism_iff_mem_orbit {G₀ G₁ : Graph}
    (h : G₁.distinctVertices.length = G₀.distinctVertices.length) :
    (G₀, G₁) ∈ GraphIsomorphism ↔
      (fun i j : Fin G₀.distinctVertices.length => G₁.adjIndex i j) ∈
        orbit fun i j : Fin G₀.distinctVertices.length => G₀.adjIndex i j := by
  rw [mem_GraphIsomorphism_iff, mem_orbit]
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ.trans (finCongr h), relabelMatrix_eq_iff.2 fun i j => hσ i j⟩
  · rintro ⟨τ, hτ⟩
    exact ⟨τ.trans (finCongr h.symm), fun i j => relabelMatrix_eq_iff.1 hτ i j⟩

/-- **Graph non-isomorphism is in `AM`** [Goldwasser and Sipser][GoldwasserSipser1986],
[Arora and Barak, Section 8.2][AroraBarak09]: the set lower bound protocol applied to the pairs
of a relabelling of one of the graphs and an automorphism of it, which are `2 n!` many for
non-isomorphic graphs with `n` distinct vertices each and `n!` many for isomorphic graphs. -/
theorem mem_AM : GraphNonIsomorphism ∈ AM (encPair encGraph encGraph) := by
  set N : Polynomial ℕ := 2 * Polynomial.X ^ 2 + 1 with hN
  set c : Polynomial ℕ := Polynomial.X ^ 2 + 1 with hc
  have hK : ComputableTidilyInPolyTime
      (fun a : Graph × Graph => 2 * a.1.distinctVertices.length.factorial)
      (encPair encGraph encGraph) encNat :=
    (ComputableTidilyInPolyTime.const 2).binary_mul'
      (ComputableTidilyInPolyTime.binary_factorial.comp
        ((ComputableTidilyInPolyTime.length_list encNat).comp
          (Graph.computableTidilyInPolyTime_distinctVertices.comp
            (ComputableTidilyInPolyTime.fst encGraph encGraph))))
  -- the lengths
  have hlen (G₀ G₁ : Graph) :
      G₀.distinctVertices.length * G₀.distinctVertices.length ≤
        (encPair encGraph encGraph (G₀, G₁)).length ^ 2 := by
    have := G₀.length_distinctVertices_le
    have : G₀.distinctVertices.length ≤ (encPair encGraph encGraph (G₀, G₁)).length := by
      simp only [length_encPair]
      omega
    nlinarith
  have hE (L : ℕ) : N.eval L = 2 * L ^ 2 + 1 := by simp [hN]
  have hC (L : ℕ) : c.eval L = L ^ 2 + 1 := by simp [hc]
  -- with equally many vertices, the certified set has `n!` or `2 n!` elements
  have hpairs (G₀ G₁ : Graph) (h : G₁.distinctVertices.length = G₀.distinctVertices.length) :
      #(certifiedSet (encPair encGraph encGraph) N c (test N) (G₀, G₁)) =
        #((pairs fun i j : Fin G₀.distinctVertices.length => G₀.adjIndex i j) ∪
          pairs fun i j : Fin G₀.distinctVertices.length => G₁.adjIndex i j) := by
    have hset : certifiedSet (encPair encGraph encGraph) N c (test N) (G₀, G₁) =
        univ.filter fun x : BitString (N.eval (encPair encGraph encGraph (G₀, G₁)).length) =>
          ∃ z : BitString (c.eval (encPair encGraph encGraph (G₀, G₁)).length),
            check G₀.distinctVertices.length (N.eval (encPair encGraph encGraph (G₀, G₁)).length)
              (fun b i j => if b then G₁.adjIndex i j else G₀.adjIndex i j)
              (List.ofFn x) (List.ofFn z) = true := by
      refine filter_congr fun x _ => exists_congr fun z => ?_
      simp only [test, h, ne_eq, not_true_eq_false, decide_false, Bool.false_or,
        List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn]
    have hlen' := hlen G₀ G₁
    rw [hset, card_filter_check (by rw [hE]; omega) (by rw [hC]; omega)]
    rfl
  refine mem_AM_of_card_certifiedSet (N := N) (c := c) (R := test N)
    (computableTidilyInPolyTime_test N) hK (fun a => by positivity) (fun a ha => ?_)
    fun a ha => ?_
  · obtain ⟨G₀, G₁⟩ := a
    dsimp only
    by_cases h : G₁.distinctVertices.length = G₀.distinctVertices.length
    · rw [hpairs G₀ G₁ h, card_pairs_union,
        ite_eq_right fun hmem => ha ((mem_GraphIsomorphism_iff_mem_orbit h).2 hmem)]
    · -- with different numbers of vertices, every string is certified
      have hset : certifiedSet (encPair encGraph encGraph) N c (test N) (G₀, G₁) = univ := by
        refine filter_true_of_mem fun x _ => ⟨fun _ => false, ?_⟩
        simp only [test, h, ne_eq, not_false_eq_true, decide_true, Bool.true_or]
      have hlen' := hlen G₀ G₁
      rw [hset, card_univ, BitString.card, hE]
      have hfac : G₀.distinctVertices.length.factorial ≤
          2 ^ (2 * (encPair encGraph encGraph (G₀, G₁)).length ^ 2) :=
        calc G₀.distinctVertices.length.factorial
            ≤ G₀.distinctVertices.length ^ G₀.distinctVertices.length := Nat.factorial_le_pow _
          _ ≤ (2 ^ G₀.distinctVertices.length) ^ G₀.distinctVertices.length :=
            Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
          _ = 2 ^ (G₀.distinctVertices.length * G₀.distinctVertices.length) := by rw [← pow_mul]
          _ ≤ 2 ^ (2 * (encPair encGraph encGraph (G₀, G₁)).length ^ 2) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ]
      omega
  · obtain ⟨G₀, G₁⟩ := a
    have hiso : (G₀, G₁) ∈ GraphIsomorphism := not_not.1 ha
    have h := length_distinctVertices_eq_of_mem_GraphIsomorphism hiso
    rw [hpairs G₀ G₁ h, card_pairs_union,
      ite_eq_left ((mem_GraphIsomorphism_iff_mem_orbit h).1 hiso)]

end GraphNonIsomorphism

end Cslib.Complexity
