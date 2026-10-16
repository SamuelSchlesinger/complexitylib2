/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.CookLevin.Encoding

import Complexity.Computability.Complexity.CookLevin.Clauses
import Complexity.Computability.Complexity.CookLevin.Parameters
import Complexity.Tactic.PolyTime

/-!
# Polynomial time for the complete Cook–Levin reduction

The existing tableau is constructed from a bit-string prefix and unary certificate/time bounds.
All clause families and intermediate lists are charged by the tidy machine calculus. Composing
with the exact parameter computation and binary variable relabelling certifies `reduce` itself.
The verifier, tape count, finite state type and polynomial bounds are fixed; one resulting machine
and polynomial work for every encoded instance.

## Main results

* `Cslib.Complexity.CookLevin.computableTidilyInPolyTime_tableau`: the entire original tableau.
* `Cslib.Complexity.CookLevin.computableTidilyInPolyTime_reduce`: the complete SAT reduction.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 2.3.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin

open Turing Turing.MultiTapeTM

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]

/-- Construct the whole tableau from its prefix and unary certificate/time bounds. -/
@[fun_prop]
theorem computableTidilyInPolyTime_tableau (tm : MultiTapeTM k Bool State) :
    ComputableTidilyInPolyTime (fun q : List Bool × ℕ × ℕ => tableau tm q.1 q.2.1 q.2.2)
      (encPair encBits (encPair encUnary encUnary))
      (encList (encList (encPair encVar encBool))) := by
  unfold tableau
  polytime

/-- The existing Cook–Levin reduction is polynomial-time for every fixed verifier and bounds. -/
@[fun_prop]
theorem computableTidilyInPolyTime_reduce (tm : MultiTapeTM k Bool State) (p : Polynomial ℕ)
    (c d : ℕ) {α : Type} (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (reduce tm p c d enc) enc encCNF :=
  computableTidilyInPolyTime_relabel.comp
    ((computableTidilyInPolyTime_tableau tm).comp (computableTidilyInPolyTime_parameters p c d enc))

end Cslib.Complexity.CookLevin
