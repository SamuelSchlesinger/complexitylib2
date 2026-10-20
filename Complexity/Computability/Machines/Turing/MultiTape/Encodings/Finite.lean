/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Encodings of fixed finite types

A finite type is encoded by unary ranks in one fixed enumeration. The enumeration and its size
are independent of the runtime input; this does not give a uniform algorithm for growing types.

## Main definitions

* `Turing.MultiTapeTM.encFinite`: unary ranks for a fixed finite type.

## Main results

* `Turing.MultiTapeTM.length_encFinite_lt`: the cardinality bounds every encoded rank.

## References

Adapts `Computability/Probabilistic/Finite.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the existing unary encoding.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- Encode a fixed finite type by unary ranks in an enumeration chosen once. -/
noncomputable def encFinite (α : Type) [Finite α] : α ↪ List Bool :=
  let _ := Fintype.ofFinite α
  ⟨fun a => encUnary (Fintype.equivFin α a).val, fun _ _ h =>
    (Fintype.equivFin α).injective (Fin.ext (encUnary.injective h))⟩

/-- Every encoded finite tag has length less than the fixed domain's cardinality. -/
theorem length_encFinite_lt {α : Type} [Finite α] (a : α) :
    (encFinite α a).length < Nat.card α := by
  let _ := Fintype.ofFinite α
  simp [encFinite, Nat.card_eq_fintype_card]

end Turing.MultiTapeTM
