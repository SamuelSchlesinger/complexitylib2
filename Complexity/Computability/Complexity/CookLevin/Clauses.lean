/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.CookLevin.Encoding

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Window
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Logics.Propositional.CNF.PolyTime

/-!
# Polynomial-time construction of tableau clauses

The initial, accepting, situation and exactly-one clauses of the existing Cook–Levin tableau are
polynomial-time functions of their input word and unary time/window bounds. Variables use
`encVar`, so the certificates compose with `computableTidilyInPolyTime_relabel` to produce
binary SAT instances.

The machine, its tape count and its finite state type are fixed. Traversals of tapes and
situations therefore use fixed lists; the tape-cell window is enumerated from the input bound.
The remaining clause families must still be certified to obtain the full reduction-time theorem.

## Main results

* `Cslib.Complexity.CookLevin.computableTidilyInPolyTime_initClauses`.
* `Cslib.Complexity.CookLevin.computableTidilyInPolyTime_acceptClauses`.
* `Cslib.Complexity.CookLevin.computableTidilyInPolyTime_sitClauses`.
* `Cslib.Complexity.CookLevin.computableTidilyInPolyTime_oneHotClauses`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin

open Turing Turing.MultiTapeTM ComputableTidilyInPolyTime Cslib.Logic.PL

variable {k : ℕ} {State : Type} [Fintype State]

/-- Enumerate the feature groups in polynomial time in the unary input and window bounds. -/
@[fun_prop]
theorem computableTidilyInPolyTime_groups :
    ComputableTidilyInPolyTime
      (fun p : ℕ × ℕ => Feature.groups (k := k) (State := State) p.1 p.2)
      (encPair encUnary encUnary) (encList (encList encFeature)) := by
  unfold Feature.groups
  simp only [SProd.sprod, List.product, List.map_flatMap, List.map_map, Function.comp_def]
  fun_prop

/-- Build all exactly-one clauses for one tableau row, including the input-dependent windows. -/
@[fun_prop]
theorem computableTidilyInPolyTime_oneHotClauses [DecidableEq State] :
    ComputableTidilyInPolyTime
      (fun p : ((List Bool × ℕ) × ℕ) × ℕ =>
        oneHotClauses (k := k) (State := State) p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair encBits encUnary) encUnary) encUnary)
      (encList (encList (encPair encVar encBool))) := by
  fun_prop [oneHotClauses]

/-- Build the existing initial-configuration clauses from a unary window bound. -/
@[fun_prop]
theorem computableTidilyInPolyTime_initClauses (tm : MultiTapeTM k Bool State) :
    ComputableTidilyInPolyTime (initClauses tm) encUnary
      (encList (encList (encPair encVar encBool))) := by
  fun_prop [initClauses]

/-- Build the two accepting-configuration clauses from a unary time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_acceptClauses :
    ComputableTidilyInPolyTime (acceptClauses (k := k) (State := State)) encUnary
      (encList (encList (encPair encVar encBool))) := by
  fun_prop [acceptClauses]

/-- Build the situation clauses at a unary time, with the finite machine data fixed. -/
@[fun_prop]
theorem computableTidilyInPolyTime_sitClauses :
    ComputableTidilyInPolyTime (sitClauses (k := k) (State := State)) encUnary
      (encList (encList (encPair encVar encBool))) := by
  fun_prop [sitClauses]

end Cslib.Complexity.CookLevin
