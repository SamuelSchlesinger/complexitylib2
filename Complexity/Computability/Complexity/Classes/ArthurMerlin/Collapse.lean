/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.ArthurMerlin.PH
public import Complexity.Computability.Complexity.Classes.PH.Collapse
public import Complexity.Computability.Complexity.Problems.GraphIsomorphism

import Complexity.Computability.Complexity.Classes.ArthurMerlin.GraphNonIsomorphism
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# coNP ⊆ AM collapses the polynomial hierarchy

The theorem of Boppana, Håstad and Zachos [BoppanaHastadZachos1987],
[Arora and Barak, Section 8.2][AroraBarak09]: if `coNP ⊆ AM`, for problems with any encoding of
their instances, then `Σ₂ = Π₂ = AM` and the polynomial hierarchy collapses to its second level,
`PH = Σ₂`. Consequently, if graph isomorphism is `NP`-complete then `PH = Σ₂`, since graph
non-isomorphism is in `AM` (`Cslib.Complexity.GraphNonIsomorphism.mem_AM`).

The proof:

* **`AM` is closed under existential quantification** over polynomially long words
  (`Cslib.Complexity.mem_AM_of_exists`, the collapse `MAM = AM` of [Babai][Babai1985], in
  `Complexity.Computability.Complexity.Classes.ArthurMerlin.Amplification`).
* A problem in `Σ₂` is the projection of a problem in `Π₁ = coNP` on pairs `(a, w₁)`, so
  `coNP ⊆ AM` gives `Σ₂ ⊆ AM` (`Cslib.Complexity.SigmaP_two_subset_AM_of_coNP_subset_AM`), and with
  `AM ⊆ Π₂` (`Cslib.Complexity.AM_subset_PiP_two`), `Σ₂ ⊆ Π₂`, hence `Π₂ ⊆ Σ₂` by complements and
  `PH = Σ₂` (`Cslib.Complexity.PH_eq_SigmaP_of_PiP_subset_SigmaP`).

## Main results

* `Cslib.Complexity.SigmaP_two_subset_AM_of_coNP_subset_AM`: `coNP ⊆ AM` gives `Σ₂ ⊆ AM`.
* `Cslib.Complexity.PH_eq_SigmaP_two_of_coNP_subset_AM`: **Boppana–Håstad–Zachos**.
* `Cslib.Complexity.SigmaP_two_eq_AM_of_coNP_subset_AM`,
  `Cslib.Complexity.PiP_two_eq_SigmaP_two_of_coNP_subset_AM`: `Σ₂ = Π₂ = AM`.
* `Cslib.Complexity.PH_eq_SigmaP_two_of_NPComplete_GraphIsomorphism`: if graph isomorphism is
  `NP`-complete, then `PH = Σ₂`.

## References

* [R. B. Boppana, J. Håstad, S. Zachos, *Does co-NP have short interactive
  proofs?*][BoppanaHastadZachos1987]
* [L. Babai, *Trading group theory for randomness*][Babai1985]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-! ### The collapse -/

/-- **`coNP ⊆ AM` gives `Σ₂ ⊆ AM`**: a problem in `Σ₂` is the projection of the `Π₁` problem of
pairs `(a, w₁)` that the universal quantifier accepts, which is in `coNP`, hence in `AM`. -/
theorem SigmaP_two_subset_AM_of_coNP_subset_AM
    (h : coNP (encPair enc encBits) ⊆ AM (encPair enc encBits)) : SigmaP 2 enc ⊆ AM enc := by
  rintro A ⟨ps, V, hlen, hV, hA⟩
  obtain ⟨p₁, ps, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  have hlen' : ps.length = 1 := by simpa using hlen
  -- the pairs `(a, w₁)` that the universal quantifier accepts
  let B : Set (α × List Bool) := {y | Alternation false
    (ps.map fun r => r.eval (enc y.1).length) fun w => V (y.1, y.2 ++ w) = true}
  have hle (y : α × List Bool) : (enc y.1).length ≤ (encPair enc encBits y).length := by
    simp only [length_encPair]
    omega
  have hB : B ∈ PiP 1 (encPair enc encBits) := by
    refine ⟨ps, fun z => V (z.1.1, z.1.2 ++ truncateBlocks ps (enc z.1.1).length
      (encPair enc encBits z.1).length z.2), hlen', ?_, fun y => ?_⟩
    · have hfst := (ComputableTidilyInPolyTime.fst (encPair enc encBits) encBits)
      exact hV.comp (((ComputableTidilyInPolyTime.fst _ _).comp hfst).prod
        (ComputableTidilyInPolyTime.bitsAppend ((ComputableTidilyInPolyTime.snd _ _).comp hfst)
          (computableTidilyInPolyTime_truncateBlocks ps
            ((ComputableTidilyInPolyTime.encoding_length enc).comp
              ((ComputableTidilyInPolyTime.fst _ _).comp hfst))
            ((ComputableTidilyInPolyTime.encoding_length _).comp hfst) (.snd _ _))))
    · exact (alternation_truncateBlocks (hle y)
        (P := fun w => V (y.1, y.2 ++ w) = true)).symm
  rw [PiP_one_eq_coNP] at hB
  have hA' : A = {a | ∃ w : List Bool, w.length = p₁.eval (enc a).length ∧ (a, w) ∈ B} := by
    ext a
    rw [hA a]
    simp only [List.map_cons, alternation_true_cons]
    rfl
  rw [hA']
  exact mem_AM_of_exists (h hB) p₁

/-- If `coNP ⊆ AM` for every encoding, then `Π₂ ⊆ Σ₂`: the complement of a `Π₂` problem is in
`Σ₂ ⊆ AM ⊆ Π₂`. -/
theorem PiP_two_subset_SigmaP_two_of_coNP_subset_AM
    (h : ∀ {β : Type} (encB : β ↪ List Bool), coNP encB ⊆ AM encB) {β : Type}
    (encB : β ↪ List Bool) : PiP 2 encB ⊆ SigmaP 2 encB := fun A hA => by
  have hc := AM_subset_PiP_two
    (SigmaP_two_subset_AM_of_coNP_subset_AM (h _) (compl_mem_SigmaP_of_mem_PiP hA))
  simpa using compl_mem_SigmaP_of_mem_PiP hc

/-- **The Boppana–Håstad–Zachos theorem** [BoppanaHastadZachos1987],
[Arora and Barak, Section 8.2][AroraBarak09]: if `coNP ⊆ AM` for problems with any encoding of
their instances, then the polynomial hierarchy collapses to `Σ₂`. -/
theorem PH_eq_SigmaP_two_of_coNP_subset_AM
    (h : ∀ {β : Type} (encB : β ↪ List Bool), coNP encB ⊆ AM encB) : PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_of_PiP_subset_SigmaP (by norm_num) fun encB =>
    PiP_two_subset_SigmaP_two_of_coNP_subset_AM h encB

/-- If `coNP ⊆ AM` for every encoding, then `Σ₂ = AM`. -/
theorem SigmaP_two_eq_AM_of_coNP_subset_AM
    (h : ∀ {β : Type} (encB : β ↪ List Bool), coNP encB ⊆ AM encB) : SigmaP 2 enc = AM enc :=
  (SigmaP_two_subset_AM_of_coNP_subset_AM (h _)).antisymm
    (AM_subset_PiP_two.trans (PiP_two_subset_SigmaP_two_of_coNP_subset_AM h enc))

/-- If `coNP ⊆ AM` for every encoding, then `Π₂ = Σ₂`. -/
theorem PiP_two_eq_SigmaP_two_of_coNP_subset_AM
    (h : ∀ {β : Type} (encB : β ↪ List Bool), coNP encB ⊆ AM encB) : PiP 2 enc = SigmaP 2 enc :=
  (PiP_two_subset_SigmaP_two_of_coNP_subset_AM h enc).antisymm
    ((SigmaP_two_subset_AM_of_coNP_subset_AM (h _)).trans AM_subset_PiP_two)

/-- **If graph isomorphism is `NP`-complete, then `PH = Σ₂`** [BoppanaHastadZachos1987],
[Arora and Barak, Section 8.2][AroraBarak09]: graph non-isomorphism is then `coNP`-hard, and it
is in `AM`, which is closed under reductions, so `coNP ⊆ AM`. -/
theorem PH_eq_SigmaP_two_of_NPComplete_GraphIsomorphism
    (hGI : NPComplete (encPair encGraph encGraph) GraphIsomorphism) : PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_two_of_coNP_subset_AM fun encB A hA =>
    (NPHard.compl hGI.2 encB A hA).mem_AM GraphNonIsomorphism.mem_AM

end Cslib.Complexity
