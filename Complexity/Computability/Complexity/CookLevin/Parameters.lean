/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.CookLevin.Reduction
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Computing the Cook–Levin parameters

The reduction in `CookLevin/Reduction.lean` builds a tableau from a framed input prefix, a
certificate length and a time bound. This module certifies their joint computation, with the two
bounds in unary so that enumerating times and tape positions has polynomial cost. The certificate
polynomial and the constants in the verifier's time bound are fixed parameters.

The clause and variable-numbering certificates in `CookLevin/Clauses.lean` and
`CookLevin/Encoding.lean` compose with this result in `CookLevin/PolyTime.lean`.

## Main results

* `Cslib.Complexity.CookLevin.computableTidilyInPolyTime_parameters`:
  computing the exact prefix and bounds used by the reduction.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 2.3.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin

open Turing.MultiTapeTM

/-- The input prefix, certificate length and verifier time bound used by the Cook–Levin
reduction are jointly computable in polynomial time, with the bounds in unary. -/
@[fun_prop]
theorem computableTidilyInPolyTime_parameters {α : Type} (p : Polynomial ℕ) (c d : ℕ)
    (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (parameters p c d enc)
      enc (encPair encBits (encPair encUnary encUnary)) := by
  have hframe : ComputableTidilyInPolyTime (fun a => frame (enc a)) enc encBits :=
    .of_linear (.of_frame fun _ => rfl)
  have hlength := ComputableTidilyInPolyTime.encoding_length enc
  unfold parameters
  fun_prop

end Cslib.Complexity.CookLevin
