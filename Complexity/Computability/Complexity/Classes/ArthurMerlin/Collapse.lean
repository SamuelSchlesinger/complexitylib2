/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.ArthurMerlin.GraphNonIsomorphism
public import Complexity.Computability.Complexity.Classes.ArthurMerlin.PH
public import Complexity.Computability.Complexity.Classes.PH.Collapse

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Data.BitString.Basic

/-!
# coNP ⊆ AM collapses the polynomial hierarchy

The theorem of Boppana, Håstad and Zachos [BoppanaHastadZachos1987],
[Arora and Barak, Section 8.2][AroraBarak09]: if `coNP ⊆ AM`, for problems with any encoding of
their instances, then `Σ₂ = Π₂ = AM` and the polynomial hierarchy collapses to its second level,
`PH = Σ₂`. Consequently, if graph isomorphism is `NP`-complete then `PH = Σ₂`, since graph
non-isomorphism is in `AM` (`Cslib.Complexity.GraphNonIsomorphism.mem_AM`).

The proof:

* **`AM` is closed under existential quantification** over polynomially long words
  (`Cslib.Complexity.mem_AM_of_exists`, the collapse `MAM = AM` of [Babai][Babai1985]): reduce the
  error of the Arthur–Merlin verifier for the pairs `(a, w)` below `2 ^ (-|w| - 2)` and let Merlin
  send `w` with his reply; by the union bound over the words `w`, Arthur's coins rarely admit an
  accepted answer for any `w` when no `w` works.
* A problem in `Σ₂` is the projection of a problem in `Π₁ = coNP` on pairs `(a, w₁)`, so
  `coNP ⊆ AM` gives `Σ₂ ⊆ AM` (`Cslib.Complexity.SigmaP_two_subset_AM_of_coNP_subset_AM`), and with
  `AM ⊆ Π₂` (`Cslib.Complexity.AM_subset_PiP_two`), `Σ₂ ⊆ Π₂`, hence `Π₂ ⊆ Σ₂` by complements and
  `PH = Σ₂` (`Cslib.Complexity.PH_eq_SigmaP_of_PiP_subset_SigmaP`).

## Main results

* `Cslib.Complexity.mem_AM_of_exists`: `AM` is closed under polynomially bounded existential
  quantification.
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

/-! ### Existential quantification -/

/-- A bit string of `k + j` bits is its first `k` bits followed by its last `j` bits. -/
private theorem ofFn_eq_append {k j : ℕ} (y : BitString (k + j)) :
    List.ofFn y = List.ofFn ((Fin.appendEquiv k j).symm y).1 ++
      List.ofFn ((Fin.appendEquiv k j).symm y).2 := by
  rw [← List.ofFn_fin_append]
  congr 1
  exact ((Fin.appendEquiv k j).apply_symm_apply y).symm

/-- **`AM` is closed under existential quantification** [Babai][Babai1985]: if the pairs `(a, w)`
form a problem in `AM`, with respect to the encoding of pairs, then so do the instances `a` for
which some word `w` of length `p(n)`, `n` the length of the encoded instance, makes `(a, w)` a
member. -/
theorem mem_AM_of_exists {B : Set (α × List Bool)} (hB : B ∈ AM (encPair enc encBits))
    (p : Polynomial ℕ) :
    {a | ∃ w : List Bool, w.length = p.eval (enc a).length ∧ (a, w) ∈ B} ∈ AM enc := by
  obtain ⟨pB, qB, VB, hVB, hB'⟩ := mem_AM_iff_forall_errorExponent.mp hB (Polynomial.X + 2)
  -- the length of the encoded pair of an instance and a word of length `p(n)`
  set L : Polynomial ℕ := 2 * Polynomial.X + 1 + p with hLdef
  have hL (a : α) (w : List Bool) (hw : w.length = p.eval (enc a).length) :
      (encPair enc encBits (a, w)).length = L.eval (enc a).length := by
    simp only [length_encPair, encBits_apply, hw, hLdef, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  have hn : ComputableTidilyInPolyTime (fun a => (encPair enc encBits a).length)
      (encPair enc encBits) encUnary := ComputableTidilyInPolyTime.encoding_length _
  have hP : ComputableTidilyInPolyTime (fun x : α × List Bool => (pB.comp L).eval (enc x.1).length)
      (encPair enc encBits) encUnary :=
    ((ComputableTidilyInPolyTime.unary_eval _).comp
      (ComputableTidilyInPolyTime.encoding_length enc)).comp (.fst _ _)
  have hp : ComputableTidilyInPolyTime (fun x : α × List Bool => p.eval (enc x.1).length)
      (encPair enc encBits) encUnary :=
    ((ComputableTidilyInPolyTime.unary_eval _).comp
      (ComputableTidilyInPolyTime.encoding_length enc)).comp (.fst _ _)
  refine ⟨pB.comp L, p + qB.comp L, fun x => VB ((x.1,
      (x.2.drop ((pB.comp L).eval (enc x.1).length)).take (p.eval (enc x.1).length)),
      x.2.take ((pB.comp L).eval (enc x.1).length) ++
        x.2.drop ((pB.comp L).eval (enc x.1).length + p.eval (enc x.1).length)), ?_,
    fun a => ?_⟩
  · exact hVB.comp (((ComputableTidilyInPolyTime.fst _ _).prod
      (ComputableTidilyInPolyTime.bitsTakeWithInput
        (ComputableTidilyInPolyTime.bitsDropWithInput (.snd _ _) hP) hp)).prod
      (ComputableTidilyInPolyTime.bitsAppend
        (ComputableTidilyInPolyTime.bitsTakeWithInput (.snd _ _) hP)
        (ComputableTidilyInPolyTime.bitsDropWithInput (.snd _ _)
          (ComputableTidilyInPolyTime.unary_add.comp (hP.prod hp)))))
  rw [Polynomial.eval_add]
  -- the verifier reads the word and runs the verifier of the pairs
  have hsplit (r : BitString ((pB.comp L).eval (enc a).length))
      (y : BitString (p.eval (enc a).length + (qB.comp L).eval (enc a).length)) :
      VB ((a, ((List.ofFn r ++ List.ofFn y).drop ((pB.comp L).eval (enc a).length)).take
          (p.eval (enc a).length)), (List.ofFn r ++ List.ofFn y).take
            ((pB.comp L).eval (enc a).length) ++ (List.ofFn r ++ List.ofFn y).drop
              ((pB.comp L).eval (enc a).length + p.eval (enc a).length)) =
        VB ((a, List.ofFn ((Fin.appendEquiv _ _).symm y).1),
          List.ofFn r ++ List.ofFn ((Fin.appendEquiv _ _).symm y).2) := by
    rw [List.drop_left' List.length_ofFn, List.take_left' List.length_ofFn, ofFn_eq_append y,
      List.take_left' List.length_ofFn, ← List.append_assoc,
      List.drop_left' (by simp)]
  simp only [hsplit]
  -- the error bounds of the pairs, at the length of the encoded instance
  have herr (w : BitString (p.eval (enc a).length)) :
      ((a, List.ofFn w) ∈ B → 2 ^ (L.eval (enc a).length + 2) *
        #{r : BitString (pB.eval (L.eval (enc a).length)) |
          ∀ y : BitString (qB.eval (L.eval (enc a).length)),
            VB ((a, List.ofFn w), List.ofFn r ++ List.ofFn y) = false} ≤
          2 ^ pB.eval (L.eval (enc a).length)) ∧
      ((a, List.ofFn w) ∉ B → 2 ^ (L.eval (enc a).length + 2) *
        #{r : BitString (pB.eval (L.eval (enc a).length)) |
          ∃ y : BitString (qB.eval (L.eval (enc a).length)),
            VB ((a, List.ofFn w), List.ofFn r ++ List.ofFn y) = true} ≤
          2 ^ pB.eval (L.eval (enc a).length)) := by
    have h := hB' (a, List.ofFn w)
    rw [hL a _ List.length_ofFn,
      show (Polynomial.X + 2 : Polynomial ℕ).eval (L.eval (enc a).length) =
        L.eval (enc a).length + 2 by simp] at h
    exact h
  rw [Polynomial.eval_comp, Polynomial.eval_comp]
  have hLp : p.eval (enc a).length ≤ L.eval (enc a).length := by
    simp [hLdef]
  constructor
  · -- a good word leaves a quarter of the random strings without an accepted answer
    rintro ⟨w, hw, hmem⟩
    refine BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le _ ?_
    have hw' : List.ofFn (BitString.ofList _ w) = w := BitString.ofFn_ofList hw
    have hbad := (herr (BitString.ofList _ w)).1 (by rwa [hw'])
    have h4 : 4 ≤ 2 ^ (L.eval (enc a).length + 2) := by
      rw [pow_add]
      exact Nat.le_mul_of_pos_left _ (by positivity)
    refine (Nat.mul_le_mul_left 4 (card_le_card fun r hr => ?_)).trans
      ((Nat.mul_le_mul_right _ h4).trans hbad)
    rw [mem_filter] at hr ⊢
    refine ⟨mem_univ _, fun y => ?_⟩
    have := not_exists.1 hr.2 (Fin.append (BitString.ofList _ w) y)
    simpa [Fin.appendEquiv] using this
  · -- by the union bound over the words, a quarter of the random strings have an accepted answer
    intro ha
    refine BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le _ ?_
    have hunion : #{r : BitString (pB.eval (L.eval (enc a).length)) |
        ¬∀ y : BitString (p.eval (enc a).length + qB.eval (L.eval (enc a).length)),
          VB ((a, List.ofFn ((Fin.appendEquiv _ _).symm y).1),
            List.ofFn r ++ List.ofFn ((Fin.appendEquiv _ _).symm y).2) = false} ≤
        ∑ w : BitString (p.eval (enc a).length),
          #{r : BitString (pB.eval (L.eval (enc a).length)) |
            ∃ y : BitString (qB.eval (L.eval (enc a).length)),
              VB ((a, List.ofFn w), List.ofFn r ++ List.ofFn y) = true} := by
      refine (card_le_card fun r hr => ?_).trans card_biUnion_le
      obtain ⟨y, hy⟩ := not_forall.1 (mem_filter.1 hr).2
      exact mem_biUnion.2 ⟨_, mem_univ _, mem_filter.2 ⟨mem_univ _, _, by simpa using hy⟩⟩
    have hpos : 0 < 2 ^ p.eval (enc a).length := by positivity
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc 2 ^ p.eval (enc a).length * (4 * #{r : BitString (pB.eval (L.eval (enc a).length)) |
          ¬∀ y : BitString (p.eval (enc a).length + qB.eval (L.eval (enc a).length)),
            VB ((a, List.ofFn ((Fin.appendEquiv _ _).symm y).1),
              List.ofFn r ++ List.ofFn ((Fin.appendEquiv _ _).symm y).2) = false})
        ≤ 2 ^ (L.eval (enc a).length + 2) * ∑ w : BitString (p.eval (enc a).length),
          #{r : BitString (pB.eval (L.eval (enc a).length)) |
            ∃ y : BitString (qB.eval (L.eval (enc a).length)),
              VB ((a, List.ofFn w), List.ofFn r ++ List.ofFn y) = true} := by
          have h4 : 2 ^ p.eval (enc a).length * 4 ≤ 2 ^ (L.eval (enc a).length + 2) := by
            rw [pow_add]
            exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hLp)
          rw [← mul_assoc]
          exact Nat.mul_le_mul h4 hunion
      _ = ∑ w : BitString (p.eval (enc a).length), 2 ^ (L.eval (enc a).length + 2) *
          #{r : BitString (pB.eval (L.eval (enc a).length)) |
            ∃ y : BitString (qB.eval (L.eval (enc a).length)),
              VB ((a, List.ofFn w), List.ofFn r ++ List.ofFn y) = true} := mul_sum _ _ _
      _ ≤ ∑ _w : BitString (p.eval (enc a).length), 2 ^ pB.eval (L.eval (enc a).length) :=
          sum_le_sum fun w _ => (herr w).2 fun hw => ha ⟨_, List.length_ofFn, hw⟩
      _ = 2 ^ p.eval (enc a).length * 2 ^ pB.eval (L.eval (enc a).length) := by
          rw [sum_const, card_univ, smul_eq_mul, BitString.card]

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
