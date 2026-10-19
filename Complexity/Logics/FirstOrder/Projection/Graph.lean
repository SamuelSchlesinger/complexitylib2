/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Projection
public import Mathlib.ModelTheory.Graph

/-!
# Graph projections

The loop-free directed complement is a quantifier-free projection: equality of the endpoints
selects false on the diagonal; otherwise the output is the negation of one input edge. The
numeric interpretation is the identity, so this construction preserves any chosen relational numeric
structure. It works for every universe, including the empty one, and needs neither order nor BIT.
For simple graphs this is the usual graph complement.

## Main definitions

* `Projection.offDiagonalComplement`: complement off the diagonal, with identity numeric data.

## Main results

* `Projection.realize_offDiagonalComplement`: the output edge predicate is inequality and
  nonadjacency.
* `Projection.isQF_offDiagonalComplement`: all numeric tests and definitions are quantifier-free.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

namespace Cslib.Logic.FO.Projection

open FirstOrder Language Structure

/-- Complement a binary edge relation off the diagonal. Equality is a numeric test and the
negative edge literal supplies the only input bit inspected by each output bit. -/
def offDiagonalComplement (N : Language) : Projection N N Language.graph Language.graph Unit where
  numeric := .id N
  rel
    | .adj =>
      .branch ((Term.var (0, ())).equal (.var (1, ()))) (.leaf (.const false))
        (.leaf (.rel .adj (fun i => (i, ())) true))

/-- The loop-free directed complement is quantifier-free. -/
theorem isQF_offDiagonalComplement (N : Language) : (offDiagonalComplement N).IsQF := by
  refine ⟨Interpretation.isQF_id N, ?_⟩
  rintro _ ⟨⟩
  exact ⟨(BoundedFormula.IsAtomic.equal _ _).isQF, trivial, trivial⟩

/-- The output contains precisely the unequal, nonadjacent pairs. No symmetry or irreflexivity
assumption is imposed on the input relation. -/
theorem realize_offDiagonalComplement (N : Language) {M : Type*}
    [N.Structure M] [Language.graph.Structure M] (x : Fin 2 × Unit → M) :
    ((offDiagonalComplement N).rel .adj).toFormula.Realize x ↔
      x (0, ()) ≠ x (1, ()) ∧ ¬ RelMap Language.adj (fun i => x (i, ())) := by
  classical
  rw [ProjectionFormula.realize_toFormula]
  by_cases h : x (0, ()) = x (1, ()) <;>
    simp [offDiagonalComplement, ProjectionFormula.select, InputLiteral.Realize, h,
      Function.comp_def]

end Cslib.Logic.FO.Projection
