/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.CookLevin.Clauses
import Complexity.Computability.Complexity.CookLevin.Parameters
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Window

/-!
# Cook–Levin construction tests

The constructor certificates must compose through the reduction's actual parameters and emit
the binary encoding of SAT. A concrete zero-work-tape machine checks that the machine parameters
are inhabited; certificate variables remain available even for an empty control-state type.
-/

namespace ComplexityTests.CookLevinPolyTime

open Turing.MultiTapeTM Cslib.Complexity Cslib.Complexity.CookLevin

example {k : ℕ} {State : Type} [Fintype State] (tm : Turing.MultiTapeTM k Bool State) :
    ComputableTidilyInPolyTime
      (fun T => (initClauses tm T ++ sitClauses T ++ acceptClauses T).relabel Var.index)
      encUnary encCNF := by
  fun_prop

-- Fixed tape/symbol traversals combine with input-dependent windows and nested lists.
example {k : ℕ} {State : Type} [Fintype State] :
    ComputableTidilyInPolyTime
      (fun p : ℕ × ℕ => Feature.groups (k := k) (State := State) p.1 p.2)
      (encPair encUnary encUnary) (encList (encList encFeature)) := by
  unfold Feature.groups
  simp only [SProd.sprod, List.product, List.map_flatMap, List.map_map, Function.comp_def]
  fun_prop

-- The input encoding, polynomial and machine are fixed parameters of the reduction.
example {k : ℕ} {State α : Type} [Fintype State]
    (tm : Turing.MultiTapeTM k Bool State) (enc : α ↪ List Bool)
    (p : Polynomial ℕ) (c d : ℕ) :
    ComputableTidilyInPolyTime
      (fun a => (initClauses tm (parameters p c d enc a).2.2).relabel Var.index)
      enc encCNF := by
  fun_prop

private def finish : Turing.MultiTapeTM 0 Bool Unit :=
  ofTr () fun _ _ _ => ⟨0, Fin.elim0, some true, none⟩

example : ComputableTidilyInPolyTime
    (fun T => (initClauses finish T).relabel Var.index) encUnary encCNF := by
  fun_prop

example : ComputableTidilyInPolyTime
    (fun j => (Var.cert (k := 0) (State := Empty) j).index) encUnary encNat := by
  fun_prop

end ComplexityTests.CookLevinPolyTime
