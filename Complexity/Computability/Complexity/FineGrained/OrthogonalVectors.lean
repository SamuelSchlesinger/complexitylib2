/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.Exponents
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-!
# The strong exponential time hypothesis implies the orthogonal vectors hypothesis

The split-and-list reduction of Williams [Williams2005] (`Cslib.Complexity.toOV`) splits the `n`
distinct variables of a formula with `m` clauses into halves of `⌊n / 2⌋` and `⌈n / 2⌉` variables.
To each assignment of a half it assigns the vector of length `m` whose coordinate `j` is `true`
when no literal of clause `j` on a variable of the half is satisfied
(`Cslib.Complexity.OV.clauseVector`). Two such vectors, one for each half, are orthogonal exactly
when every clause is satisfied by one of the two partial assignments, that is when together they
satisfy the formula. So the formula is satisfiable exactly when the instance `toOV φ`, of
`2 ^ ⌊n / 2⌋` and `2 ^ ⌈n / 2⌉` vectors of dimension `m`, is in `OV`
(`Cslib.Complexity.toOV_mem_OV_iff`).

The reduction writes its `2 ^ ⌈n / 2⌉ m`-bit output in time `2 ^ ⌈n / 2⌉` times a polynomial in
the length of the encoded formula (`Cslib.Complexity.computableTidilyInO_toOV`): the vectors are
streamed to the output one at a time (`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.iterate_unary_stream_sum`)
rather than accumulated, which would cost time quadratic in the number of vectors. Then a decider
for `OV` within time `N ^ (2 - ε)` times a polynomial in the dimension, on `N` vectors, decides
`SAT` within time `2 ^ ((1 - ε / 2) n)` times a polynomial, for `0 < ε ≤ 1`
(`Cslib.Complexity.DecidableInExpTime.SAT_of_OV`), and the strong exponential time hypothesis
implies the orthogonal vectors hypothesis (`Cslib.Complexity.OVH_of_SETH`).

The hypothesis is stated with a polynomial factor in the dimension. The form for dimension
`c log N`, which Williams also derives with the sparsification lemma, is not proved here.

## Main definitions

* `Cslib.Complexity.OV.clauseVector`, `Cslib.Complexity.OV.halfVectors`: the vectors of the
  assignments of a half of the variables.
* `Cslib.Complexity.toOV`: the split-and-list reduction.

## Main results

* `Cslib.Complexity.toOV_mem_OV_iff`: `toOV φ ∈ OV ↔ φ ∈ SAT`.
* `Cslib.Complexity.computableTidilyInO_toOV`: the reduction runs within time `2 ^ ⌈n / 2⌉` times a
  polynomial.
* `Cslib.Complexity.DecidableInExpTime.SAT_of_OV`: a fast `OV` decider gives a fast `SAT` decider.
* `Cslib.Complexity.OVH_of_SETH`: `SETH → OVH`.

## References

* [R. Williams, *A new algorithm for optimal 2-constraint satisfaction and its
  implications*][Williams2005]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Orthogonality -/

/-- Vectors indexed by the same list are orthogonal when no index is `true` in both. -/
theorem OV.orthogonal_map_map {γ : Type*} {l : List γ} {f g : γ → Bool} :
    OV.Orthogonal (l.map f) (l.map g) ↔ ∀ x ∈ l, f x = false ∨ g x = false := by
  constructor
  · intro h x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    simpa [List.getD_eq_getElem?_getD, hj] using h j
  · intro h j
    rcases lt_or_ge j l.length with hj | hj
    · simpa [List.getD_eq_getElem?_getD, hj] using h _ (List.getElem_mem hj)
    · left
      simp [List.getD_eq_getElem?_getD, hj]

/-! ### The split-and-list reduction -/

namespace OV

/-- Whether the assignment numbered by `i` on the variables `vs` satisfies a literal of the clause
`c` on a variable of `vs`. -/
def satisfiesOn (vs : List ℕ) (i : ℕ) (c : Clause ℕ) : Bool :=
  c.any fun l => decide (l.1 ∈ vs) && bitsAssignment vs i l.1 == l.2

/-- The vector of the assignment numbered by `i` on the variables `vs`: coordinate `j` is `true`
when the assignment satisfies no literal of clause `j` of `φ` on a variable of `vs`. -/
def clauseVector (φ : CNF ℕ) (vs : List ℕ) (i : ℕ) : List Bool :=
  φ.map fun c => !satisfiesOn vs i c

/-- The vectors of the `2 ^ |vs|` assignments numbered on the variables `vs`. -/
def halfVectors (φ : CNF ℕ) (vs : List ℕ) : List (List Bool) :=
  (List.range (2 ^ vs.length)).map (clauseVector φ vs)

/-- The first `⌊n / 2⌋` of the `n` distinct variables. -/
def firstVars (φ : CNF ℕ) : List ℕ :=
  (ThreeSAT.distinctVars φ).take ((ThreeSAT.distinctVars φ).length / 2)

/-- The last `⌈n / 2⌉` of the `n` distinct variables. -/
def secondVars (φ : CNF ℕ) : List ℕ :=
  (ThreeSAT.distinctVars φ).drop ((ThreeSAT.distinctVars φ).length / 2)

end OV

/-- **The split-and-list reduction** [Williams2005]: the vectors of the assignments of the first
`⌊n / 2⌋` and of the last `⌈n / 2⌉` of the `n` distinct variables of a formula. -/
def toOV (φ : CNF ℕ) : List (List Bool) × List (List Bool) :=
  (OV.halfVectors φ (OV.firstVars φ), OV.halfVectors φ (OV.secondVars φ))

namespace OV

theorem satisfiesOn_eq_true_iff {vs : List ℕ} {i : ℕ} {c : Clause ℕ} :
    satisfiesOn vs i c = true ↔ ∃ l ∈ c, l.1 ∈ vs ∧ bitsAssignment vs i l.1 = l.2 := by
  simp [satisfiesOn]

theorem length_firstVars (φ : CNF ℕ) : (firstVars φ).length = φ.numVars / 2 := by
  simp [firstVars, ThreeSAT.length_distinctVars]
  omega

theorem length_secondVars (φ : CNF ℕ) :
    (secondVars φ).length = φ.numVars - φ.numVars / 2 := by
  simp [secondVars, ThreeSAT.length_distinctVars]

theorem length_halfVectors (φ : CNF ℕ) (vs : List ℕ) : (halfVectors φ vs).length = 2 ^ vs.length := by
  simp [halfVectors]

theorem length_of_mem_halfVectors {φ : CNF ℕ} {vs : List ℕ} {v : List Bool}
    (hv : v ∈ halfVectors φ vs) : v.length = φ.length := by
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
  simp [clauseVector]

/-- **Orthogonal vectors are satisfying assignments.** For disjoint lists of variables `vs₁` and
`vs₂` covering the variables of `φ`, the vectors of the assignments numbered by `i₁` on `vs₁` and
by `i₂` on `vs₂` are orthogonal exactly when the two assignments together satisfy `φ`. -/
theorem orthogonal_clauseVector_iff {φ : CNF ℕ} {vs₁ vs₂ : List ℕ} (hdisj : vs₁.Disjoint vs₂)
    (hcover : ∀ v ∈ φ.vars, v ∈ vs₁ ∨ v ∈ vs₂) (i₁ i₂ : ℕ) :
    Orthogonal (clauseVector φ vs₁ i₁) (clauseVector φ vs₂ i₂) ↔
      φ.eval (fun v => if v ∈ vs₁ then bitsAssignment vs₁ i₁ v else bitsAssignment vs₂ i₂ v) =
        true := by
  rw [clauseVector, clauseVector, orthogonal_map_map, CNF.eval_eq_true_iff]
  refine forall₂_congr fun c hc => ?_
  simp only [Bool.not_eq_false', satisfiesOn_eq_true_iff, Clause.eval_eq_true_iff]
  constructor
  · rintro (⟨l, hl, hv, he⟩ | ⟨l, hl, hv, he⟩)
    · exact ⟨l, hl, by rw [ite_eq_left hv, he]⟩
    · exact ⟨l, hl, by rw [ite_eq_right fun h => hdisj h hv, he]⟩
  · rintro ⟨l, hl, he⟩
    have hvars : l.1 ∈ φ.vars := List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨c, hc, hl⟩, rfl⟩
    by_cases hv : l.1 ∈ vs₁
    · exact Or.inl ⟨l, hl, hv, by rwa [ite_eq_left hv] at he⟩
    · exact Or.inr ⟨l, hl, (hcover _ hvars).resolve_left hv, by rwa [ite_eq_right hv] at he⟩

end OV

/-- **The split-and-list reduction is correct** [Williams2005]: `toOV φ ∈ OV ↔ φ ∈ SAT`. -/
theorem toOV_mem_OV_iff (φ : CNF ℕ) : toOV φ ∈ OV ↔ φ ∈ SAT := by
  set vs := ThreeSAT.distinctVars φ
  set h := vs.length / 2
  have hdisj : (vs.take h).Disjoint (vs.drop h) :=
    List.disjoint_of_nodup_append (by rw [List.take_append_drop]; exact ThreeSAT.nodup_distinctVars)
  have hcover : ∀ v ∈ φ.vars, v ∈ vs.take h ∨ v ∈ vs.drop h := fun v hv => by
    rw [← List.mem_append, List.take_append_drop]
    exact ThreeSAT.mem_distinctVars.mpr hv
  simp only [toOV, OV, OV.halfVectors, Set.mem_ofPred_eq, List.mem_map, List.mem_range,
    exists_exists_and_eq_and]
  rw [mem_SAT]
  constructor
  · rintro ⟨i₁, -, i₂, -, ho⟩
    exact ⟨_, (OV.orthogonal_clauseVector_iff hdisj hcover i₁ i₂).mp ho⟩
  · rintro ⟨σ, hσ⟩
    obtain ⟨i₁, hi₁, h₁⟩ := exists_lt_two_pow_bitsAssignment_eq (vs := vs.take h) σ
    obtain ⟨i₂, hi₂, h₂⟩ := exists_lt_two_pow_bitsAssignment_eq (vs := vs.drop h) σ
    refine ⟨i₁, hi₁, i₂, hi₂, (OV.orthogonal_clauseVector_iff hdisj hcover i₁ i₂).mpr ?_⟩
    refine (CNF.eval_congr fun v hv => ?_).trans hσ
    split_ifs with hv₁
    · exact h₁ v hv₁
    · exact h₂ v ((hcover v hv).resolve_left hv₁)

end Cslib.Complexity
