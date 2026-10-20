/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Fagin.Converse
public import Complexity.Logics.SecondOrder.Grounding
import Mathlib.Tactic.FinCases

/-!
# SAT is NP-complete under first-order reductions

The descriptive-complexity form of the Cook–Levin theorem [Immerman, Chapter 7][Immerman1999]:
the class `CNF.sat` of satisfiable CNF structures has its query language in `NP`
(`Cslib.Logic.FO.CNF.queryLanguage_sat_mem_NP`), and every isomorphism-closed class of finite
structures whose query language is in `NP` and which contains the empty structure is first-order
reducible to it (`Cslib.Logic.FO.CNF.reduces_sat_of_mem_NP`). Conversely, a class first-order
reducible to SAT is in `NP`, so these are exactly the classes reducible to SAT
(`Cslib.Logic.FO.CNF.reduces_sat_iff_mem_NP`).

The proof combines Fagin's theorem
(`Cslib.Logic.ESO.definable_iff_isoClosed_and_queryLanguage_mem_NP`) with the grounding of
existential second-order sentences (`Cslib.Logic.ESO.Definable.reduces_sat`).
The hypothesis on the empty structure is that of the grounding: the classical statement concerns
nonempty structures, and the empty structure is satisfiable.

## Main definitions

* `Cslib.Logic.FO.CNF.vocabulary`: the vocabulary of CNF structures, `pos` before `neg`.

## Main results

* `Cslib.Logic.FO.CNF.queryLanguage_sat_mem_NP`, `Cslib.Logic.FO.CNF.queryLanguage_threeSat_mem_NP`:
  SAT and 3SAT are in `NP`.
* `Cslib.Logic.FO.CNF.reduces_sat_of_mem_NP`: **SAT is NP-hard under first-order reductions**.
* `Cslib.Logic.FO.CNF.reduces_sat_iff_mem_NP`: the classes containing the empty structure that are
  first-order reducible to SAT are exactly the isomorphism-closed classes in `NP`.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
-/

@[expose] public section

universe u v

namespace Cslib.Logic.FO.CNF

open FirstOrder Language Structure CategoryTheory Cslib.Complexity

/-- The vocabulary of CNF structures: the table of `pos`, then that of `neg`. -/
def vocabulary : Vocabulary CNF.language where
  count := 2
  symbol :=
    { toFun := fun i => if i = 0 then ⟨2, pos⟩ else ⟨2, neg⟩
      invFun := fun | ⟨_, .pos⟩ => 0 | ⟨_, .neg⟩ => 1
      left_inv := fun i => by fin_cases i <;> rfl
      right_inv := fun | ⟨_, .pos⟩ => rfl | ⟨_, .neg⟩ => rfl }

/-- **SAT is in NP**: the encodings of the satisfiable CNF structures form a problem in `NP`. -/
theorem queryLanguage_sat_mem_NP : vocabulary.queryLanguage sat ∈ NP encStructure :=
  definable_sat.queryLanguage_mem_NP vocabulary

/-- **3SAT is in NP.** -/
theorem queryLanguage_threeSat_mem_NP : vocabulary.queryLanguage threeSat ∈ NP encStructure :=
  definable_threeSat.queryLanguage_mem_NP vocabulary

variable {L : Language.{u, v}} [L.IsRelational] (v : Vocabulary L)

/-- **SAT is NP-hard under first-order reductions** (the Cook–Levin theorem for first-order
reductions [Immerman, Chapter 7][Immerman1999]): every isomorphism-closed class of finite
structures whose query language is in `NP` and which contains the empty structure is first-order
reducible to SAT. -/
theorem reduces_sat_of_mem_NP {K : Set (Bundled.{0} L.Structure)} (hK : IsoClosed K)
    (hNP : v.queryLanguage K ∈ NP encStructure)
    (hempty : ∀ M : Bundled.{0} L.Structure, IsEmpty M → M ∈ K) : Reduces K sat :=
  (ESO.Definable.of_queryLanguage_mem_NP v hK hNP).reduces_sat hempty

/-- **The classes first-order reducible to SAT are the NP classes**: a class containing the empty
structure is first-order reducible to SAT exactly when it is closed under isomorphism and its
query language is in `NP`. -/
theorem reduces_sat_iff_mem_NP {K : Set (Bundled.{0} L.Structure)}
    (hempty : ∀ M : Bundled.{0} L.Structure, IsEmpty M → M ∈ K) :
    Reduces K sat ↔ IsoClosed K ∧ v.queryLanguage K ∈ NP encStructure :=
  (ESO.definable_iff_reduces_sat hempty).symm.trans
    (ESO.definable_iff_isoClosed_and_queryLanguage_mem_NP v)

end Cslib.Logic.FO.CNF
