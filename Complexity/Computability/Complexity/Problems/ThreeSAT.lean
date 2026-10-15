/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Logics.Propositional.CNF.ThreeCNF
public import Mathlib.Data.Nat.Pairing

/-!
# 3SAT

`ThreeSAT` is the set of satisfiable formulas in conjunctive normal form whose clauses have at most
three literals [Arora and Barak, Section 2.3.1][AroraBarak09]. `toThreeSAT` maps a formula to an
equisatisfiable one of width three, by splitting its clauses (`Cslib.Logic.PL.CNF.to3CNF`) and
numbering the variables injectively.

## Main definitions

* `Cslib.Complexity.ThreeSAT`.
* `Cslib.Complexity.toThreeSAT`.

## Main results

* `Cslib.Complexity.mem_ThreeSAT_toThreeSAT_iff`: `φ ∈ SAT ↔ toThreeSAT φ ∈ ThreeSAT`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL

/-- The satisfiable formulas whose clauses have at most three literals. -/
def ThreeSAT : Set (CNF ℕ) := {φ | (∀ c ∈ φ, c.length ≤ 3) ∧ φ.Satisfiable}

/-- An injective numbering of the variables of a split formula: original variables at even
numbers, auxiliary variables at odd numbers through `Nat.pair`. -/
def splitVarToNat : ℕ ⊕ (ℕ × ℕ) → ℕ :=
  Sum.elim (2 * ·) fun p => 2 * Nat.pair p.1 p.2 + 1

theorem splitVarToNat_injective : Function.Injective splitVarToNat := by
  rintro (a | ⟨a₁, a₂⟩) (b | ⟨b₁, b₂⟩) h <;> simp only [splitVarToNat, Sum.elim_inl,
    Sum.elim_inr] at h
  · rw [show a = b by omega]
  · omega
  · omega
  · have : Nat.pair a₁ a₂ = Nat.pair b₁ b₂ := by omega
    rw [Nat.pair_eq_pair] at this
    rw [this.1, this.2]

/-- The reduction from `SAT` to `ThreeSAT`: split the clauses, then number the variables. -/
def toThreeSAT (φ : CNF ℕ) : CNF ℕ := φ.to3CNF.relabel splitVarToNat

theorem mem_ThreeSAT_toThreeSAT_iff (φ : CNF ℕ) : toThreeSAT φ ∈ ThreeSAT ↔ φ ∈ SAT := by
  refine ⟨fun h => ?_, fun h => ⟨fun c hc => ?_, ?_⟩⟩
  · exact (CNF.satisfiable_to3CNF φ).1 ((CNF.satisfiable_relabel splitVarToNat_injective _).1 h.2)
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    simpa using CNF.length_le_three_of_mem_to3CNF hd
  · exact (CNF.satisfiable_relabel splitVarToNat_injective _).2 ((CNF.satisfiable_to3CNF φ).2 h)

end Cslib.Complexity
