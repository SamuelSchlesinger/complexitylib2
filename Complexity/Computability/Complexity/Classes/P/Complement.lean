/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Complexity.Problems.ThreeSAT
import Complexity.Computability.Complexity.Classes.Ladner
import Complexity.Computability.Complexity.CookLevin.Completeness

/-!
# Complements of problems in P

A problem is in `P` exactly when its complement is: negate the answer of the decider
(`Cslib.Complexity.compl_mem_P`). With `P ⊆ NP` (`Cslib.Complexity.P_subset_NP`) this gives
`P ⊆ coNP`.

Since `SAT` is `NP`-complete (`Cslib.Complexity.CookLevin.SAT_npComplete`), `SAT ∈ P` holds exactly
when `P = NP` for every encoding of instances (`Cslib.Complexity.SAT_mem_P_iff`). Closure under
complement gives the same for `UNSAT`, and the reductions between `SAT` and `ThreeSAT` give it for
`ThreeSAT` [Arora and Barak, Chapter 2][AroraBarak09].

## Main results

* `Cslib.Complexity.compl_mem_P`: `P` is closed under complement.
* `Cslib.Complexity.P_subset_coNP`.
* `Cslib.Complexity.SAT_mem_P_iff`: `SAT ∈ P` exactly when `P = NP` for every encoding.
* `Cslib.Complexity.UNSAT_mem_P_iff_SAT_mem_P`, `Cslib.Complexity.ThreeSAT_mem_P_iff_SAT_mem_P`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- **`P` is closed under complement**: negate the answer of the decider. -/
theorem compl_mem_P {A : Set α} (hA : A ∈ P enc) : Aᶜ ∈ P enc :=
  let ⟨f, hf, h⟩ := hA
  ⟨fun a => !f a, ComputableTidilyInPolyTime.bool_not.comp hf, fun a => by simp [h a]⟩

/-- `P` equals its preimage under complement. -/
theorem P_eq_preimage_compl_P (enc : α ↪ List Bool) : P enc = compl ⁻¹' P enc :=
  Set.ext fun _ => ⟨compl_mem_P, fun h => by simpa using compl_mem_P h⟩

/-- **`P ⊆ coNP`.** -/
theorem P_subset_coNP : P enc ⊆ coNP enc := fun _ hA => P_subset_NP (compl_mem_P hA)

/-- **`SAT ∈ P` exactly when `P = NP`**, for every encoding of instances: `SAT` is
`NP`-complete. -/
theorem SAT_mem_P_iff : SAT ∈ P encCNF ↔ ∀ {β : Type} (e : β ↪ List Bool), P e = NP e :=
  ⟨fun h _ e => Ladner.P_eq_NP_of_SAT_mem_P h e, fun h => h encCNF ▸ CookLevin.SAT_npComplete.1⟩

/-- `UNSAT ∈ P` exactly when `SAT ∈ P`: `UNSAT` is the complement of `SAT`. -/
theorem UNSAT_mem_P_iff_SAT_mem_P : UNSAT ∈ P encCNF ↔ SAT ∈ P encCNF := by
  rw [← compl_SAT]
  exact ⟨fun h => by simpa using compl_mem_P h, compl_mem_P⟩

/-- `ThreeSAT ∈ P` exactly when `SAT ∈ P`: each reduces to the other. -/
theorem ThreeSAT_mem_P_iff_SAT_mem_P : ThreeSAT ∈ P encCNF ↔ SAT ∈ P encCNF :=
  ⟨polyTimeReducible_SAT_ThreeSAT.mem_P,
    (CookLevin.SAT_npHard encCNF ThreeSAT ThreeSAT.mem_NP).mem_P⟩

end Cslib.Complexity
