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

The initial, accepting and situation clauses of the existing Cook–Levin tableau are
polynomial-time functions of their unary time or window bound. Variables use `encVar`, so the
certificates compose with `computableTidilyInPolyTime_relabel` to produce binary SAT instances.

The machine, its tape count and its finite state type are fixed. Traversals of tapes and
situations therefore use fixed lists; the tape-cell window is enumerated from the input bound.
The remaining clause families must still be certified to obtain the full reduction-time theorem.

## Main results

* `Cslib.Complexity.CookLevin.computableTidilyInPolyTime_initClauses`.
* `Cslib.Complexity.CookLevin.computableTidilyInPolyTime_acceptClauses`.
* `Cslib.Complexity.CookLevin.computableTidilyInPolyTime_sitClauses`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin

open Turing Turing.MultiTapeTM ComputableTidilyInPolyTime Cslib.Logic.PL

variable {k : ℕ} {State : Type} [Fintype State]

/-- Build the existing initial-configuration clauses from a unary window bound. -/
@[fun_prop]
theorem computableTidilyInPolyTime_initClauses (tm : MultiTapeTM k Bool State) :
    ComputableTidilyInPolyTime (initClauses tm) encUnary
      (encList (encList (encPair encVar encBool))) := by
  have hrow (i : Fin k) : ComputableTidilyInPolyTime
      (fun T => [(Var.holds 0 (.head i 0), true)] ::
        (windowList T).map fun z => [(Var.holds 0 (.cell i z none), true)])
      encUnary (encList (encList (encPair (encVar (State := State)) encBool))) := by
    have hcell : ComputableTidilyInPolyTime
        (fun z => [(Var.holds 0 (.cell i z none), true)])
        encInt (encList (encPair (encVar (State := State)) encBool)) := by fun_prop
    have hcells := (map hcell).comp computableTidilyInPolyTime_windowList
    fun_prop
  have hrows := flatMapConst (List.finRange k) (fun i _ => hrow i)
  unfold initClauses
  fun_prop

/-- Build the two accepting-configuration clauses from a unary time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_acceptClauses :
    ComputableTidilyInPolyTime (acceptClauses (k := k) (State := State)) encUnary
      (encList (encList (encPair encVar encBool))) := by
  unfold acceptClauses
  fun_prop

/-- Build the situation clauses at a unary time, with the finite machine data fixed. -/
@[fun_prop]
theorem computableTidilyInPolyTime_sitClauses :
    ComputableTidilyInPolyTime (sitClauses (k := k) (State := State)) encUnary
      (encList (encList (encPair encVar encBool))) := by
  unfold sitClauses
  apply mapConst
  intro y _
  have hreads : ComputableTidilyInPolyTime
      (fun t => (List.finRange k).map fun i => Var.holds t (.read i (y.2.2 i)))
      encUnary (encList (encVar (State := State))) := by
    apply mapConst
    intro i _
    fun_prop
  fun_prop

end Cslib.Complexity.CookLevin
