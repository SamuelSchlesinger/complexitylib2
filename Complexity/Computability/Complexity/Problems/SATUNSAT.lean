/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.DP
public import Complexity.Computability.Complexity.CookLevin.Completeness

/-!
# DP-completeness of SAT–UNSAT

## Main definitions

* `Cslib.Complexity.SATUNSAT`: pairs of CNF formulas whose first component is satisfiable and
  second component is unsatisfiable.

## Main results

* `Cslib.Complexity.SATUNSAT_dpComplete`: completeness under polynomial-time many-one reductions.

## References

* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Cslib.Logic.PL

/-- Pairs of a satisfiable CNF formula and an unsatisfiable CNF formula. -/
def SATUNSAT : Set (CNF ℕ × CNF ℕ) := SAT ×ˢ UNSAT

/-- SAT–UNSAT is DP-complete with the product of the library's CNF encodings. -/
theorem SATUNSAT_dpComplete : DPComplete (encPair encCNF encCNF) SATUNSAT :=
  CookLevin.SAT_npComplete.prod_coNPComplete CookLevin.UNSAT_coNPComplete

end Cslib.Complexity
