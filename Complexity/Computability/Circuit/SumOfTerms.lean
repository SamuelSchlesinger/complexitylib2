/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Simulation
public import Mathlib.LinearAlgebra.Dimension.LinearMap
import Complexity.Foundations.LinearAlgebra.Rank
import Complexity.Computability.Circuit.Program
import Complexity.Computability.Circuit.Simulation

/-!
# Circuits adding dictionary terms

Nullary gates produce members of a prescribed dictionary; binary addition and wiring are free.
The dictionary can include scalar coefficients. A linear feature whose dictionary values have
bounded rank gives a lower bound on the total dictionary cost. Each shared gate is charged once.
Supplied inputs are permitted when their features vanish.

## Main definitions

* `Cslib.Circuits.SumOfTerms.signature`: additions and nullary dictionary terms.
* `Cslib.Circuits.SumOfTerms.interpretation`: interpret the dictionary in an additive carrier.
* `Cslib.Circuits.SumOfTerms.dictionaryCost`, `Cslib.Circuits.SumOfTerms.termCost`: term weights.
* `Cslib.Circuits.SumOfTerms.addCost`, `Cslib.Circuits.SumOfTerms.weightedCost`: addition counts
  and separate uniform weights for additions and terms.

## Main results

* `Cslib.Circuits.SumOfTerms.rank_trace_le`: every wire's feature rank is bounded by program cost.
* `Cslib.Circuits.SumOfTerms.cost_weightedCost`: separate the two gate counts.

## References

* Adapted from `Basis/SumOfTerms.lean` and `LowerBound/Fusion/SumOfTerms/Rank.lean` in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

@[expose] public section

namespace Cslib.Circuits.SumOfTerms

universe u

/-- Free binary addition and a nullary gate for each dictionary term. -/
inductive Op (T : Type u)
  | add
  | term (value : T)
  deriving DecidableEq

/-- Addition reads two wires; dictionary terms read none. -/
abbrev Op.arity {T : Type*} : Op T → ℕ
  | .add => 2
  | .term _ => 0

/-- The signature for sums of dictionary terms. -/
abbrev signature (T : Type u) : Signature where
  Op := Op T
  Arity := Op.arity

/-- Interpret dictionary terms by their values and addition by carrier addition. -/
def interpretation {T V : Type*} [Add V] (value : T → V) : Interpretation (signature T) V
  | .add, args => args 0 + args 1
  | .term t, _ => value t

@[simp] theorem interpretation_add {T V : Type*} [Add V] (value : T → V)
    (args : Fin 2 → V) : interpretation value .add args = args 0 + args 1 := rfl

@[simp] theorem interpretation_term {T V : Type*} [Add V] (value : T → V) (t : T)
    (args : Fin 0 → V) : interpretation value (.term t) args = value t := rfl

/-- Charge each dictionary term its weight; addition is free. -/
def dictionaryCost {T : Type*} (weight : T → ℕ) : Op T → ℕ
  | .add => 0
  | .term t => weight t

@[simp] theorem dictionaryCost_add {T : Type*} (weight : T → ℕ) :
    dictionaryCost weight .add = 0 := rfl

@[simp] theorem dictionaryCost_term {T : Type*} (weight : T → ℕ) (t : T) :
    dictionaryCost weight (.term t) = weight t := rfl

/-- Count dictionary gates, with free addition. -/
abbrev termCost {T : Type*} : Op T → ℕ := dictionaryCost fun _ => 1

/-- Count additions; dictionary gates are free. -/
def addCost {T : Type*} : Op T → ℕ
  | .add => 1
  | .term _ => 0

/-- Assign one weight to additions and another to dictionary gates. -/
def weightedCost {T : Type*} (addition term : ℕ) : Op T → ℕ
  | .add => addition
  | .term _ => term

/-- Uniform weights separate into the addition and dictionary gate counts. -/
theorem cost_weightedCost {T : Type*} {n g : ℕ} (p : Program (signature T) n g)
    (addition term : ℕ) :
    p.cost (weightedCost addition term) = addition * p.cost addCost + term * p.cost termCost := by
  simp only [Program.cost_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases (p.lines i).op <;> simp [weightedCost, addCost]

variable {T K V A B : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B] {n g : ℕ}

/-- A rank budget for each dictionary term bounds every wire's feature rank. The span argument
counts shared gates once, even when additions reuse them. -/
theorem rank_trace_le (p : Program (signature T) n g) (value : T → V)
    (feature : V →ₗ[K] A →ₗ[K] B) (weight : T → ℕ)
    (hterm : ∀ t, (feature (value t)).rank ≤ weight t)
    (input : Fin n → V) (hinput : ∀ i, feature (input i) = 0) (w : Wire n g) :
    (feature (p.trace (interpretation value) input w)).rank ≤ p.cost (dictionaryCost weight) := by
  let contribution : Op T → A →ₗ[K] B
    | .add => 0
    | .term t => feature (value t)
  let family := fun k => contribution (p.lines k).op
  let S := Submodule.span K (Set.range family)
  have step (op : Op T) (args : Fin op.arity → V)
      (hargs : ∀ a, feature (args a) ∈ S) (hnew : contribution op ∈ S) :
      feature (interpretation value op args) ∈ S := by
    cases op with
    | add => simpa [interpretation] using S.add_mem (hargs 0) (hargs 1)
    | term t => exact hnew
  have hmem : ∀ w, feature (p.trace (interpretation value) input w) ∈ S := by
    refine p.wire_induction (fun i => ?_) (fun k ih => ?_)
    · simp [hinput]
    · rw [p.trace_gate]
      exact step _ _ ih (Submodule.subset_span ⟨k, rfl⟩)
  have h := LinearMap.rank_le_sum_of_mem_span _ family
    (fun k => dictionaryCost weight (p.lines k).op) (hmem w) (fun k => ?_)
  · simpa only [← Nat.cast_sum, ← p.cost_eq_sum] using h
  · cases hop : (p.lines k).op with
    | add => simp [family, contribution, hop, dictionaryCost]
    | term t => simpa [family, contribution, hop, dictionaryCost] using hterm t

end Cslib.Circuits.SumOfTerms
