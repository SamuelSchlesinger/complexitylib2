/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives

/-!
# Polynomial-time truth-table reductions

A nonadaptive reduction uses a uniformly computed indexed batch of queries, a unary query count,
and a polynomial-time Boolean combiner. The combiner receives the original input and all answers.
The query generator is total even outside the used range; unused outputs do not affect semantics.

## Main definitions

* `truthTableAnswers`: the semantic answer word for an indexed family.
* `PolyTimeTruthTableReducible`: polynomial-time nonadaptive reduction of encoded languages.

## References

* [H. Spakowski, M. Thakur, R. Tripathi, *Quantum and classical complexity
  classes*][SpakowskiThakurTripathi2005], Theorem 5.6(a).
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

open Classical in
/-- The semantic answers to a fixed indexed batch, in increasing index order. This definition
does not assert that membership in the indexed language is computable. -/
noncomputable def truthTableAnswers {α : Type} (A : Set (α × ℕ)) (r : α → ℕ) (a : α) : List Bool :=
  List.ofFn fun i : Fin (r a) => decide ((a, i.1) ∈ A)

variable {α : Type}

/-- A polynomial-time truth-table reduction generates all queries without access to their
answers, then applies a polynomial-time Boolean combiner to the input and answer word.
The count is computed in unary; query lengths and counts may vary at fixed input length. -/
def PolyTimeTruthTableReducible {β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (L : Set α) (B : Set β) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → β) (d : α × List Bool → Bool),
    ComputableTidilyInPolyTime r encA encUnary ∧
    ComputableTidilyInPolyTime q (encPair encA encUnary) encB ∧
    ComputableTidilyInPolyTime d (encPair encA encBits) encBool ∧
    ∀ a, a ∈ L ↔ d (a, truthTableAnswers (q ⁻¹' B) r a) = true

end Cslib.Complexity
