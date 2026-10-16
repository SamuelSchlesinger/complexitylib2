/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (staging: assembles Cook–Levin from the remaining polynomial-time bound
-- on the reduction; replaced by unconditional theorems once that bound is proved)

public import Complexity.Computability.Complexity.CookLevin.Reduction
public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Complexity.Problems.SAT.PolyTime

/-!
# Assembling the Cook–Levin theorem

`SAT ∈ NP` is proved in `Problems/SAT/PolyTime.lean`, and the Cook–Levin reduction is correct
(`reduce_mem_SAT_iff`). What remains is its polynomial-time bound. This file assembles the theorem
from exactly that bound, so the remaining work is explicit. Its dual, that `UNSAT` is
`coNP`-complete, follows from the same bound.

## Main results

* `Cslib.Complexity.CookLevin.SAT_npHard_of_polyTime`: `SAT` is `NP`-hard from polynomial-time
  reductions.
* `Cslib.Complexity.CookLevin.SAT_npComplete_of_polyTime`: `SAT` is `NP`-complete from that bound.
* `Cslib.Complexity.CookLevin.UNSAT_coNPComplete_of_polyTime`: `UNSAT` is `coNP`-complete, from
  the same bound.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin

open Turing Turing.MultiTapeTM Cslib.Logic.PL

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

/-- **Cook–Levin**, assembled: `SAT` is `NP`-complete, given that the reductions are computable
in polynomial time. -/
theorem SAT_npComplete_of_polyTime
    (hred : ∀ {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
      (tm : MultiTapeTM k Bool State) (p : Polynomial ℕ) (c d : ℕ) {α : Type}
      (enc : α ↪ List Bool), ComputableTidilyInPolyTime (reduce tm p c d enc) enc encCNF) :
    NPComplete encCNF SAT :=
  ⟨SAT.mem_NP, SAT_npHard_of_polyTime hred⟩

/-- `UNSAT` is `coNP`-complete, given that the Cook–Levin reductions are computable in polynomial
time: the dual of the Cook–Levin theorem. -/
theorem UNSAT_coNPComplete_of_polyTime
    (hred : ∀ {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
      (tm : MultiTapeTM k Bool State) (p : Polynomial ℕ) (c d : ℕ) {α : Type}
      (enc : α ↪ List Bool), ComputableTidilyInPolyTime (reduce tm p c d enc) enc encCNF) :
    coNPComplete encCNF UNSAT :=
  compl_SAT ▸ (SAT_npComplete_of_polyTime hred).compl

end Cslib.Complexity.CookLevin
