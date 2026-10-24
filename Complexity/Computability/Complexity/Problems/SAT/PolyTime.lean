/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Logics.Propositional.CNF.PolyTime

/-!
# SAT belongs to NP

The existing verifier is polynomial-time on the framed binary encoding of CNF formulas and raw
certificate bits. It looks up each variable's first occurrence, so arbitrary binary variable
labels do not inflate certificates. Repeated variables read the same certificate position.

Together with `Cslib.Complexity.SAT.isVerifier`, this proves membership in `NP`
[Arora and Barak, Section 2.3][AroraBarak09]. Combined with the tableau reduction in
`CookLevin/PolyTime.lean`, this gives `Cslib.Complexity.CookLevin.SAT_npComplete` in
`CookLevin/Completeness.lean`.

## Main definitions

* `Cslib.Complexity.cnfDecoder`: the total decoder of formulas, along `encCNF`.

## Main results

* `Cslib.Complexity.SAT.computableTidilyInPolyTime_verifier`: the verifier is polynomial-time.
* `Cslib.Complexity.SAT.computableTidilyInPolyTime_clause_length`,
  `Cslib.Complexity.SAT.computableTidilyInPolyTime_length`,
  `Cslib.Complexity.SAT.computableTidilyInPolyTime_vars_length`: literal, clause and
  variable-occurrence counts for natural-number variables, in unary (`fun_prop` versions of the
  generic `Cslib.Logic.PL.CNF` lemmas).
* `Cslib.Complexity.SAT.mem_NP`: satisfiability belongs to NP.
* `Cslib.Complexity.UNSAT_mem_coNP`: unsatisfiability belongs to coNP.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Formulas in conjunctive normal form are decoded along their encoding `encCNF`. -/
def cnfDecoder : Decoder encCNF := .list (.list (.pair .nat .bool))

namespace SAT

open ComputableTidilyInPolyTime

/-- Listing the variables in order of occurrence is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_vars :
    ComputableTidilyInPolyTime (CNF.vars (V := ℕ)) encCNF (encList encNat) :=
  (CNF.computableInPolyTime_vars encNat).tidy

/-- The number of literals of a polynomial-time clause, in unary, is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_clause_length {α : Type} {input : α ↪ List Bool}
    {c : α → Clause ℕ}
    (hc : ComputableTidilyInPolyTime c input (encList (encPair encNat encBool))) :
    ComputableTidilyInPolyTime (fun a => (c a).length) input encUnary :=
  (Clause.computableInPolyTime_length (.of_tidy hc)).tidy

/-- The number of clauses of a polynomial-time formula, in unary, is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_length {α : Type} {input : α ↪ List Bool} {φ : α → CNF ℕ}
    (hφ : ComputableTidilyInPolyTime φ input encCNF) :
    ComputableTidilyInPolyTime (fun a => (φ a).length) input encUnary :=
  (CNF.computableInPolyTime_length (encV := encNat) (.of_tidy hφ)).tidy

/-- The number of variable occurrences of a polynomial-time formula, in unary, is
polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_vars_length {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} (hφ : ComputableTidilyInPolyTime φ input encCNF) :
    ComputableTidilyInPolyTime (fun a => (φ a).vars.length) input encUnary :=
  (CNF.computableInPolyTime_vars_length (encV := encNat) (.of_tidy hφ)).tidy

/-- Reading the certificate at the first occurrence of a variable is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_assignment :
    ComputableTidilyInPolyTime (fun p : (CNF ℕ × List Bool) × ℕ => assignment p.1.1 p.1.2 p.2)
      (encPair (encPair encCNF encBits) encNat) encBool := by
  fun_prop [assignment]

/-- Evaluating a literal with the certificate assignment is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_literal :
    ComputableTidilyInPolyTime
      (fun p : (CNF ℕ × List Bool) × Literal ℕ => Literal.eval (assignment p.1.1 p.1.2) p.2)
      (encPair (encPair encCNF encBits) (encPair encNat encBool)) encBool := by
  fun_prop [Literal.eval, assignment]

/-- Evaluating a clause with the certificate assignment is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_clause :
    ComputableTidilyInPolyTime
      (fun p : (CNF ℕ × List Bool) × Clause ℕ => Clause.eval (assignment p.1.1 p.1.2) p.2)
      (encPair (encPair encCNF encBits) (encList (encPair encNat encBool))) encBool := by
  fun_prop [Clause.eval, Literal.eval, assignment]

/-- The SAT verifier is polynomial-time, including on certificates of arbitrary length. -/
@[fun_prop]
theorem computableTidilyInPolyTime_verifier :
    ComputableTidilyInPolyTime verifier (encPair encCNF encBits) encBool := by
  fun_prop [verifier, CNF.eval]

/-- Satisfiability is in NP, with certificates of length equal to the encoded formula length. -/
theorem mem_NP : SAT ∈ NP encCNF :=
  ⟨Polynomial.X, verifier, .of_tidy computableTidilyInPolyTime_verifier, isVerifier⟩

end SAT

/-- Unsatisfiability is in coNP. -/
theorem UNSAT_mem_coNP : UNSAT ∈ coNP encCNF := by
  simpa only [mem_coNP, ← compl_SAT, compl_compl] using SAT.mem_NP

end Cslib.Complexity
