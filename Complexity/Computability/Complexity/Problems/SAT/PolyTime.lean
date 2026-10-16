/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# SAT belongs to NP

The existing verifier is polynomial-time on the framed binary encoding of CNF formulas and raw
certificate bits. It looks up each variable's first occurrence, so arbitrary binary variable
labels do not inflate certificates. Repeated variables read the same certificate position.

Together with `Cslib.Complexity.SAT.isVerifier`, this proves membership in `NP`
[Arora and Barak, Section 2.3][AroraBarak09]. NP-hardness still requires the polynomial-time bound
for the Cook–Levin reduction.

## Main results

* `Cslib.Complexity.SAT.computableTidilyInPolyTime_verifier`: the verifier is polynomial-time.
* `Cslib.Complexity.SAT.mem_NP`: satisfiability belongs to NP.
* `Cslib.Complexity.UNSAT_mem_coNP`: unsatisfiability belongs to coNP.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

namespace SAT

open ComputableTidilyInPolyTime

/-- Listing the variables in order of occurrence is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_vars :
    ComputableTidilyInPolyTime (CNF.vars (V := ℕ)) encCNF (encList encNat) :=
  (map (fst encNat encBool)).comp (flatten (encPair encNat encBool))

/-- Reading the certificate at the first occurrence of a variable is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_assignment :
    ComputableTidilyInPolyTime (fun p : (CNF ℕ × List Bool) × ℕ => assignment p.1.1 p.1.2 p.2)
      (encPair (encPair encCNF encBits) encNat) encBool := by
  have hx := fst (encPair encCNF encBits) encNat
  have hφ := (fst encCNF encBits).comp hx
  have hw := (snd encCNF encBits).comp hx
  exact (listGetD (encA := encBool) (encL := encBits) false).comp
    (hw.prod ((idxOf encNat).comp
      ((computableTidilyInPolyTime_vars.comp hφ).prod (snd (encPair encCNF encBits) encNat))))

/-- Evaluating a literal with the certificate assignment is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_literal :
    ComputableTidilyInPolyTime
      (fun p : (CNF ℕ × List Bool) × Literal ℕ => Literal.eval (assignment p.1.1 p.1.2) p.2)
      (encPair (encPair encCNF encBits) (encPair encNat encBool)) encBool := by
  have hx := fst (encPair encCNF encBits) (encPair encNat encBool)
  have hl := snd (encPair encCNF encBits) (encPair encNat encBool)
  have hv := (fst encNat encBool).comp hl
  have hb := (snd encNat encBool).comp hl
  exact (of_finite (encA := encPair encBool encBool) (encB := encBool)
    (fun p : Bool × Bool => p.1 == p.2)).comp
      ((computableTidilyInPolyTime_assignment.comp (hx.prod hv)).prod hb)

/-- Evaluating a clause with the certificate assignment is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_clause :
    ComputableTidilyInPolyTime
      (fun p : (CNF ℕ × List Bool) × Clause ℕ => Clause.eval (assignment p.1.1 p.1.2) p.2)
      (encPair (encPair encCNF encBits) (encList (encPair encNat encBool))) encBool := by
  exact anyWith computableTidilyInPolyTime_literal
    (fst (encPair encCNF encBits) (encList (encPair encNat encBool)))
    (snd (encPair encCNF encBits) (encList (encPair encNat encBool)))

/-- The SAT verifier is polynomial-time, including on certificates of arbitrary length. -/
@[fun_prop]
theorem computableTidilyInPolyTime_verifier :
    ComputableTidilyInPolyTime verifier (encPair encCNF encBits) encBool := by
  exact allWith computableTidilyInPolyTime_clause id' (fst encCNF encBits)

/-- Satisfiability is in NP, with certificates of length equal to the encoded formula length. -/
theorem mem_NP : SAT ∈ NP encCNF :=
  ⟨Polynomial.X, verifier, computableTidilyInPolyTime_verifier, isVerifier⟩

end SAT

/-- Unsatisfiability is in coNP. -/
theorem UNSAT_mem_coNP : UNSAT ∈ coNP encCNF := by
  simpa only [mem_coNP, ← compl_SAT, compl_compl] using SAT.mem_NP

end Cslib.Complexity
