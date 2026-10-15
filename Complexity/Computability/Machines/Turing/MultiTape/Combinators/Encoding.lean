/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: subset of crei/tidy-universal `Combinators/Encoding.lean`;
-- definitions only, delete when it lands

public import Complexity.Init
public import Mathlib.Logic.Embedding.Basic

/-!
# The encoding of Booleans

A verbatim subset of Christian Reitwiessner's `Combinators/Encoding.lean` (branch
`crei/tidy-universal`): the encoding of `Bool`, without the closure properties of linear time.

## Main definitions

* `Turing.MultiTapeTM.encBool`: the encoding `b ↦ [b]` of `Bool`.
-/

namespace Turing.MultiTapeTM

/-- The encoding `b ↦ [b]` of `Bool`. -/
@[expose] public def encBool : Bool ↪ List Bool :=
  ⟨fun b => [b], fun _ _ h => List.head_eq_of_cons_eq h⟩

@[simp]
public lemma encBool_apply (b : Bool) : encBool b = [b] := rfl

end Turing.MultiTapeTM
