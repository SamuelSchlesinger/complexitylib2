/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Complexity.Logics.Propositional.ClauseSet.Sparsification.Asymptotics

/-!
# The sparsification lemma

The sparsification lemma of Impagliazzo, Paturi and Zane [ImpagliazzoPaturiZane2001]: for every
width `k` and every `ε > 0` there is a constant `c` such that every formula in conjunctive normal
form of width `k` over `N` variables is the disjunction of at most `2 ^ (ε N)` formulas of width
`k` in which every variable occurs in at most `c` clauses, each accepting only inputs the original
accepts.

The proof follows Calabro, Impagliazzo and Paturi [CalabroImpagliazzoPaturi2006]. While some set
`H` of `h ≥ 1` literals is contained in at least `θ (c - h)` clauses of size `c > h`, branch on
whether `H` is satisfied: either add the clause `H`, or add every *petal* `C \ H`; choose `c`
smallest and then `h` largest, and remove clauses that strictly contain others. The clauses a step
introduces are new along its branch, and fewer than `2 θ (c - h)` new clauses of size `c`
containing a fixed clause of size `h` are present at once. With thresholds
`θ j = α (2 k α) ^ (2 j - 1)`, a branch has length at most `N k (2 k α) ^ (2 k)` and at most
`(k - 1) N / α` petal steps, so the number of leaves is a binomial tail, below `2 ^ (ε N)` once
`α` is large. The leaves have no heavy hearts, so every literal occurs in at most `∑_{c < k} θ c`
of their clauses.

## Main results

* `Cslib.Logic.PL.ClauseSet.sparsification`: the lemma for clause sets.
* `Cslib.Logic.PL.CNF.sparsification`: the lemma for formulas in conjunctive normal form.

## References

* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
* [C. Calabro, R. Impagliazzo, R. Paturi, *A duality between clause width and clause density for
  SAT*][CalabroImpagliazzoPaturi2006]
-/

@[expose] public section

namespace Cslib.Logic.PL

/-- **The sparsification lemma** [Impagliazzo, Paturi and Zane][ImpagliazzoPaturiZane2001], **for
clause sets.** For every width `k` and every `ε > 0` there is a constant `c` such that every clause
set `φ` over `N` variables whose clauses have at most `k` literals has a family `Ψ` of at most
`2 ^ (ε N)` clause sets whose clauses have at most `k` literals, in each of which every variable
occurs in at most `c` clauses, each having only solutions of `φ`, and whose solutions together
cover those of `φ`. -/
theorem ClauseSet.sparsification (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ, ∀ (N : ℕ) (φ : ClauseSet (Fin N)), (∀ C ∈ φ, C.card ≤ k) →
      ∃ Ψ : Finset (ClauseSet (Fin N)), (Ψ.card : ℝ) ≤ 2 ^ (ε * N) ∧
        (∀ ψ ∈ Ψ, (∀ C ∈ ψ, C.card ≤ k) ∧ (∀ v, ψ.occurrences v ≤ c) ∧
          ψ.solutions ⊆ φ.solutions) ∧
        φ.solutions ⊆ Ψ.biUnion ClauseSet.solutions :=
  ClauseSet.Sparsify.exists_sparsification k hε

/-- **The sparsification lemma** [Impagliazzo, Paturi and Zane][ImpagliazzoPaturiZane2001]. For
every width `k` and every `ε > 0` there is a constant `c` such that every formula `φ` in
conjunctive normal form over `N` variables whose clauses have at most `k` literals is the
disjunction of at most `2 ^ (ε N)` such formulas, in each of which every variable occurs in at most
`c` clauses: each of them accepts only inputs that `φ` accepts, and every input that `φ` accepts is
accepted by one of them. -/
theorem CNF.sparsification (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ, ∀ (N : ℕ) (φ : CNF (Fin N)), (∀ cl ∈ φ, cl.length ≤ k) →
      ∃ Fs : List (CNF (Fin N)), (Fs.length : ℝ) ≤ 2 ^ (ε * N) ∧
        (∀ F ∈ Fs, (∀ cl ∈ F, cl.length ≤ k) ∧ (∀ v, F.occurrences v ≤ c) ∧
          ∀ x, F.eval x = true → φ.eval x = true) ∧
        ∀ x, φ.eval x = true → ∃ F ∈ Fs, F.eval x = true := by
  obtain ⟨c, hc⟩ := ClauseSet.sparsification k hε
  refine ⟨c, fun N φ hφ => ?_⟩
  obtain ⟨Ψ, hcard, hleaves, hcover⟩ := hc N φ.toClauseSet fun C hC => by
    obtain ⟨cl, hcl, hle⟩ := CNF.exists_card_le_of_mem_toClauseSet hC
    exact hle.trans (hφ cl hcl)
  refine ⟨Ψ.toList.map ClauseSet.toCNF, by simpa using hcard, fun F hF => ?_, fun x hx => ?_⟩
  · obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hF
    obtain ⟨hwidth, hocc, hsol⟩ := hleaves ψ (Finset.mem_toList.mp hψ)
    refine ⟨fun cl hcl => ClauseSet.length_le_of_mem_toCNF hwidth hcl,
      fun v => (ClauseSet.occurrences_toCNF ψ v).trans_le (hocc v), fun x hx => ?_⟩
    rw [← CNF.sat_toClauseSet_iff, ← ClauseSet.mem_solutions]
    exact hsol (ClauseSet.mem_solutions.mpr ((ClauseSet.eval_toCNF_eq_true_iff ψ x).mp hx))
  · obtain ⟨ψ, hψ, hψx⟩ := Finset.mem_biUnion.mp
      (hcover (ClauseSet.mem_solutions.mpr ((CNF.sat_toClauseSet_iff φ x).mpr hx)))
    refine ⟨ψ.toCNF, List.mem_map.mpr ⟨ψ, Finset.mem_toList.mpr hψ, rfl⟩, ?_⟩
    exact (ClauseSet.eval_toCNF_eq_true_iff ψ x).mpr (ClauseSet.mem_solutions.mp hψx)

end Cslib.Logic.PL
