/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (staging: assembles Cook–Levin from the two polynomial-time facts that
-- need crei's calculus; replaced by the unconditional theorems once that lands)

public import Complexity.Computability.Complexity.CookLevin.Reduction
public import Complexity.Computability.Complexity.Reduction

/-!
# Assembling the Cook–Levin theorem

The correctness parts of the Cook–Levin theorem are proved: the verifier for `SAT` is correct
(`Cslib.Complexity.SAT.isVerifier`) and so is the reduction (`reduce_mem_SAT_iff`). What remains
are two polynomial-time facts, which need the closure properties of polynomial-time computability
(composition, folds, arithmetic on binary numbers): that the verifier and the reduction are
computable in polynomial time. This file assembles the theorem from exactly those two facts, so
that the logical structure is checked now and the remaining work is explicit. Its dual, that
`UNSAT` is `coNP`-complete, follows from the same two facts.

## Main results

* `Cslib.Complexity.CookLevin.SAT_mem_NP_of_polyTime`: `SAT ∈ NP` from a polynomial-time verifier.
* `Cslib.Complexity.CookLevin.SAT_npHard_of_polyTime`: `SAT` is `NP`-hard from polynomial-time
  reductions.
* `Cslib.Complexity.CookLevin.SAT_npComplete_of_polyTime`: both together.
* `Cslib.Complexity.CookLevin.UNSAT_coNPComplete_of_polyTime`: `UNSAT` is `coNP`-complete, from
  the same two facts.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin

open Turing Turing.MultiTapeTM Cslib.Logic.PL

/-- `SAT ∈ NP`, given that its verifier is computable in polynomial time. -/
theorem SAT_mem_NP_of_polyTime
    (hV : ComputableTidilyInPolyTime SAT.verifier (encPair encCNF encBits) encBool) :
    SAT ∈ NP encCNF :=
  ⟨Polynomial.X, SAT.verifier, hV, SAT.isVerifier⟩

/-- `SAT` is `NP`-hard, given that the Cook–Levin reductions are computable in polynomial time. -/
theorem SAT_npHard_of_polyTime
    (hred : ∀ {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
      (tm : MultiTapeTM k Bool State) (p : Polynomial ℕ) (c d : ℕ) {α : Type}
      (enc : α ↪ List Bool), ComputableTidilyInPolyTime (reduce tm p c d enc) enc encCNF) :
    NPHard encCNF SAT := by
  rintro α enc A ⟨p, V, ⟨t, s, ⟨c, d, ht⟩, -, k, State, hfin, tm, htm⟩, hV⟩
  have := Fintype.ofFinite State
  classical
  refine ⟨reduce tm p c d enc, hred tm p c d enc, fun a =>
    (reduce_mem_SAT_iff_of_computesTidily (s := s) hV ?_ a).symm⟩
  exact htm.mono (fun x => ht x) (fun _ => le_rfl)

/-- **Cook–Levin**, assembled: `SAT` is `NP`-complete, given that its verifier and the reductions
are computable in polynomial time. -/
theorem SAT_npComplete_of_polyTime
    (hV : ComputableTidilyInPolyTime SAT.verifier (encPair encCNF encBits) encBool)
    (hred : ∀ {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
      (tm : MultiTapeTM k Bool State) (p : Polynomial ℕ) (c d : ℕ) {α : Type}
      (enc : α ↪ List Bool), ComputableTidilyInPolyTime (reduce tm p c d enc) enc encCNF) :
    NPComplete encCNF SAT :=
  ⟨SAT_mem_NP_of_polyTime hV, SAT_npHard_of_polyTime hred⟩

/-- `UNSAT` is `coNP`-complete, given that the verifier for `SAT` and the Cook–Levin reductions are
computable in polynomial time: the dual of the Cook–Levin theorem. -/
theorem UNSAT_coNPComplete_of_polyTime
    (hV : ComputableTidilyInPolyTime SAT.verifier (encPair encCNF encBits) encBool)
    (hred : ∀ {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
      (tm : MultiTapeTM k Bool State) (p : Polynomial ℕ) (c d : ℕ) {α : Type}
      (enc : α ↪ List Bool), ComputableTidilyInPolyTime (reduce tm p c d enc) enc encCNF) :
    coNPComplete encCNF UNSAT :=
  compl_SAT ▸ (SAT_npComplete_of_polyTime hV hred).compl

end Cslib.Complexity.CookLevin
