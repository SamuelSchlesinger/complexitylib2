/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.Compact
public import Complexity.Logics.Propositional.CNF.ExactlyOne
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Polynomial-time CNF construction

The clause and formula constructors used by reductions to satisfiability are polynomial-time
for any fixed encoding of their variables. Literals use `encPair`, and clauses and formulas use
`encList`. Specializing the variable encoding to binary naturals gives the encoding of `SAT`.

These results certify the existing constructors, including the ordered-pair implementation of
exactly-one constraints. They apply to empty lists and lists with repeated variables. Relabelling
requires a polynomial-time renaming function, but does not require injectivity; injectivity is
needed separately when transferring satisfiability.

## Main results

* `Cslib.Logic.PL.Clause.computableTidilyInPolyTime_impLits`,
  `.computableTidilyInPolyTime_imp`: implication clauses.
* `Cslib.Logic.PL.Clause.computableTidilyInPolyTime_relabel`,
  `Cslib.Logic.PL.CNF.computableTidilyInPolyTime_relabel`: renaming variables.
* `Cslib.Logic.PL.CNF.computableTidilyInPolyTime_exactlyOne`: exactly-one constraints.
* `Cslib.Logic.PL.CNF.computableTidilyInPolyTime_vars`: listing variable occurrences.
* `Cslib.Logic.PL.CNF.isPolyTime_compact`: compact unary indices for arbitrary variable names.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 2.3][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Turing.MultiTapeTM ComputableTidilyInPolyTime

variable {V W : Type} {encV : V ↪ List Bool} {encW : W ↪ List Bool}

/-- Negating a literal changes only its polarity. -/
@[fun_prop]
theorem Literal.computableTidilyInPolyTime_negate (enc : V ↪ List Bool) :
    ComputableTidilyInPolyTime Std.Sat.Literal.negate
      (encPair enc encBool) (encPair enc encBool) := by
  unfold Std.Sat.Literal.negate
  fun_prop

/-- Construct an implication from literals, with a positive conclusion. -/
@[fun_prop]
theorem Clause.computableTidilyInPolyTime_impLits (enc : V ↪ List Bool) :
    ComputableTidilyInPolyTime (fun p : List (Literal V) × V => Clause.impLits p.1 p.2)
      (encPair (encList (encPair enc encBool)) enc) (encList (encPair enc encBool)) := by
  unfold Clause.impLits
  fun_prop

/-- Construct an implication from positive hypotheses and a positive conclusion. -/
@[fun_prop]
theorem Clause.computableTidilyInPolyTime_imp (enc : V ↪ List Bool) :
    ComputableTidilyInPolyTime (fun p : List V × V => Clause.imp p.1 p.2)
      (encPair (encList enc) enc) (encList (encPair enc encBool)) := by
  unfold Clause.imp
  fun_prop

/-- Relabelling a clause is polynomial-time whenever the renaming function is. -/
@[fun_prop]
theorem Clause.computableTidilyInPolyTime_relabel {f : V → W}
    (hf : ComputableTidilyInPolyTime f encV encW) :
    ComputableTidilyInPolyTime (Clause.relabel f)
      (encList (encPair encV encBool)) (encList (encPair encW encBool)) :=
  map ((hf.comp (fst encV encBool)).prod (snd encV encBool))

/-- Relabelling a formula is polynomial-time whenever the renaming function is. -/
@[fun_prop]
theorem CNF.computableTidilyInPolyTime_relabel {f : V → W}
    (hf : ComputableTidilyInPolyTime f encV encW) :
    ComputableTidilyInPolyTime (CNF.relabel f)
      (encList (encList (encPair encV encBool)))
      (encList (encList (encPair encW encBool))) :=
  map (Clause.computableTidilyInPolyTime_relabel hf)

/-- List the variables of a formula in order, including repetitions. -/
@[fun_prop]
theorem CNF.computableTidilyInPolyTime_vars (enc : V ↪ List Bool) :
    ComputableTidilyInPolyTime (CNF.vars (V := V))
      (encList (encList (encPair enc encBool))) (encList enc) :=
  (map (fst enc encBool)).comp (flatten (encPair enc encBool))

/-- Construct the clause requiring at least one listed variable to hold. -/
@[fun_prop]
theorem CNF.computableTidilyInPolyTime_atLeastOne (enc : V ↪ List Bool) :
    ComputableTidilyInPolyTime (CNF.atLeastOne (V := V))
      (encList enc) (encList (encList (encPair enc encBool))) := by
  unfold CNF.atLeastOne
  fun_prop

/-- Construct the clauses forbidding two distinct listed variables from both holding.
The list may contain repeated variables. -/
@[fun_prop]
theorem CNF.computableTidilyInPolyTime_atMostOne [DecidableEq V] (enc : V ↪ List Bool) :
    ComputableTidilyInPolyTime (CNF.atMostOne (V := V))
      (encList enc) (encList (encList (encPair enc encBool))) := by
  fun_prop [CNF.atMostOne]

/-- Construct exactly-one constraints in polynomial time, including for empty or repeated lists. -/
@[fun_prop]
theorem CNF.computableTidilyInPolyTime_exactlyOne [DecidableEq V] (enc : V ↪ List Bool) :
    ComputableTidilyInPolyTime (CNF.exactlyOne (V := V))
      (encList enc) (encList (encList (encPair enc encBool))) := by
  unfold CNF.exactlyOne
  fun_prop

/-- The entire input-dependent renaming is polynomial-time for any original variable encoding.
Its output indices use unary encoding and are bounded by the input's number of occurrences. -/
@[fun_prop]
theorem CNF.isPolyTime_compact [DecidableEq V] (enc : V ↪ List Bool) :
    ComputableTidilyInPolyTime (CNF.compact (V := V))
      (encList (encList (encPair enc encBool)))
      (encList (encList (encPair encUnary encBool))) := by
  unfold CNF.compact CNF.relabel Clause.relabel Prod.map
  fun_prop

end Cslib.Logic.PL
