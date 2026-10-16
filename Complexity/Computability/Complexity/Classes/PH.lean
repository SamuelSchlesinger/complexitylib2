/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.Complexity.Classes.P

/-!
# The polynomial hierarchy

The levels `Σₖ` and `Πₖ` of the polynomial hierarchy are defined like `NP`
(`Cslib.Complexity.NP`), through polynomial-time verifiers, now with `k` alternating quantifiers
over certificates [Arora and Barak, Definition 5.4][AroraBarak09], [Wrathall][Wrathall1976]:
`A ∈ SigmaP k enc` when there are polynomials `p₁, …, pₖ` and a function
`V : α × List Bool → Bool`, computable in polynomial time on inputs
`encPair enc encBits (a, w) = frame (enc a) ++ w`, such that
`a ∈ A ↔ ∃ w₁, ∀ w₂, ∃ w₃, …, V (a, w₁ ++ w₂ ++ ⋯ ++ wₖ) = true`, where `wᵢ` ranges over the
strings of length `pᵢ (enc a).length`. `PiP k enc` is the same with a universal quantifier
first, and `PH enc` is the union of the levels `SigmaP k enc` [Stockmeyer][Stockmeyer1976].

Two choices make the inclusions between levels hold with the same verifier, and hence without any
facts about polynomial time:

* The certificates are concatenated into one string, as in `NP`, so that `SigmaP 1 enc = NP enc`
  (`SigmaP_one`).
* Each block of certificates has its own length `pᵢ`, where Arora and Barak use one polynomial
  for all blocks. A block of length `0` is a vacuous quantifier, so adding one at either end of
  the quantifier prefix shows `SigmaP k ∪ PiP k ⊆ SigmaP (k + 1) ∩ PiP (k + 1)`. The two
  definitions give the same classes, since padding every block to the largest length only needs
  a verifier that skips the padding.

That `Πₖ` consists of the complements of the problems in `Σₖ` is the quantifier duality
`¬∃ w, φ ↔ ∀ w, ¬φ` (`not_alternation`) together with one fact about polynomial time: negating the
output of a polynomial-time function keeps it polynomial-time. That fact needs the composition of
polynomial-time functions, which is not yet in cslib, so it is a hypothesis of the theorems that
use it, as are the two facts that relate `SigmaP 0` to `P`.

## Main definitions

* `Cslib.Complexity.Alternation`: alternating quantifiers over binary strings of given lengths.
* `Cslib.Complexity.IsAlternatingVerifier`: the verifier condition.
* `Cslib.Complexity.SigmaP`, `Cslib.Complexity.PiP`, `Cslib.Complexity.PH`.

## Main results

* `Cslib.Complexity.not_alternation`: the duality of alternating quantifiers.
* `Cslib.Complexity.PiP_eq_preimage_compl_SigmaP`: `Πₖ = coΣₖ`, given that negation preserves
  polynomial time.
* `Cslib.Complexity.SigmaP_one`: `Σ₁ = NP`; `Cslib.Complexity.PiP_one_eq_coNP`: `Π₁ = coNP`,
  given that negation preserves polynomial time.
* `Cslib.Complexity.SigmaP_subset_SigmaP_succ`, `Cslib.Complexity.SigmaP_subset_PiP_succ`,
  `Cslib.Complexity.PiP_subset_SigmaP_succ`, `Cslib.Complexity.PiP_subset_PiP_succ`: the
  inclusions between consecutive levels.
* `Cslib.Complexity.PH_eq_iUnion_PiP`, `Cslib.Complexity.NP_subset_PH`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [L. Stockmeyer, *The polynomial-time hierarchy*][Stockmeyer1976]
* [C. Wrathall, *Complete sets and the polynomial-time hierarchy*][Wrathall1976]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-! ### Alternating quantifiers -/

/-- Alternating quantifiers over binary strings: `Alternation q [n₁, …, nₖ] P` says
`Q₁ w₁, Q₂ w₂, …, Qₖ wₖ, P (w₁ ++ w₂ ++ ⋯ ++ wₖ)`, where `wᵢ` ranges over the strings of length
`nᵢ` and the quantifiers `Qᵢ` alternate, starting with `∃` if `q` is `true` and with `∀` if `q` is
`false`. -/
def Alternation : Bool → List ℕ → (List Bool → Prop) → Prop
  | _, [], P => P []
  | true, n :: ns, P => ∃ w : List Bool, w.length = n ∧ Alternation false ns fun v => P (w ++ v)
  | false, n :: ns, P => ∀ w : List Bool, w.length = n → Alternation true ns fun v => P (w ++ v)

section Alternation

variable {q : Bool} {n : ℕ} {ns : List ℕ} {P Q : List Bool → Prop}

@[simp] theorem alternation_nil : Alternation q [] P ↔ P [] := by
  cases q <;> rfl

theorem alternation_true_cons :
    Alternation true (n :: ns) P ↔ ∃ w : List Bool, w.length = n ∧
      Alternation false ns fun v => P (w ++ v) :=
  Iff.rfl

theorem alternation_false_cons :
    Alternation false (n :: ns) P ↔ ∀ w : List Bool, w.length = n →
      Alternation true ns fun v => P (w ++ v) :=
  Iff.rfl

theorem Alternation.mono (h : ∀ w, P w → Q w) : Alternation q ns P → Alternation q ns Q := by
  induction ns generalizing q P Q with
  | nil => simpa only [alternation_nil] using h []
  | cons n ns ih =>
    cases q
    · exact fun hP w hw => ih (fun v => h (w ++ v)) (hP w hw)
    · exact fun ⟨w, hw, hP⟩ => ⟨w, hw, ih (fun v => h (w ++ v)) hP⟩

theorem alternation_congr (h : ∀ w, P w ↔ Q w) : Alternation q ns P ↔ Alternation q ns Q :=
  ⟨.mono fun w => (h w).1, .mono fun w => (h w).2⟩

/-- **Quantifier duality.** Negating alternating quantifiers swaps every quantifier and negates
the predicate. -/
theorem not_alternation : ¬Alternation q ns P ↔ Alternation (!q) ns fun w => ¬P w := by
  induction ns generalizing q P with
  | nil => simp only [alternation_nil]
  | cons n ns ih =>
    cases q
    · simp only [alternation_false_cons, Bool.not_false, alternation_true_cons, not_forall, ih,
        Bool.not_true, exists_prop]
    · simp only [alternation_true_cons, Bool.not_true, alternation_false_cons, not_exists, not_and,
        ih, Bool.not_false]

/-- A quantifier over strings of length `0` at the end of the prefix is vacuous. -/
theorem alternation_append_zero : Alternation q (ns ++ [0]) P ↔ Alternation q ns P := by
  induction ns generalizing q P with
  | nil =>
    cases q <;> simp [alternation_true_cons, alternation_false_cons, List.length_eq_zero_iff]
  | cons n ns ih =>
    cases q
    · simp only [List.cons_append, alternation_false_cons, ih]
    · simp only [List.cons_append, alternation_true_cons, ih]

/-- A quantifier over strings of length `0` at the start of the prefix is vacuous. -/
theorem alternation_zero_cons : Alternation q (0 :: ns) P ↔ Alternation (!q) ns P := by
  cases q <;> simp [alternation_true_cons, alternation_false_cons, List.length_eq_zero_iff]

theorem alternation_singleton_true :
    Alternation true [n] P ↔ ∃ w : List Bool, w.length = n ∧ P w := by
  simp [alternation_true_cons]

end Alternation

/-! ### Alternating verifiers -/

variable {α : Type}

/-- `V` verifies `A` through alternating quantifiers over certificates whose lengths are the
polynomials `ps`, evaluated at the length of the encoded instance, starting with `∃` if `q` is
`true` and with `∀` if `q` is `false`: `a ∈ A` iff `Q₁ w₁, Q₂ w₂, …, V (a, w₁ ++ w₂ ++ ⋯)`. -/
def IsAlternatingVerifier (enc : α ↪ List Bool) (q : Bool) (ps : List (Polynomial ℕ))
    (V : α × List Bool → Bool) (A : Set α) : Prop :=
  ∀ a, a ∈ A ↔ Alternation q (ps.map fun p => p.eval (enc a).length) fun w => V (a, w) = true

variable {enc : α ↪ List Bool} {q : Bool} {ps : List (Polynomial ℕ)} {V : α × List Bool → Bool}
  {A : Set α}

namespace IsAlternatingVerifier

/-- Negating the verifier verifies the complement with every quantifier swapped. -/
theorem compl (h : IsAlternatingVerifier enc q ps V A) :
    IsAlternatingVerifier enc (!q) ps (fun x => !V x) Aᶜ := fun a => by
  rw [Set.mem_compl_iff, h a, not_alternation]
  exact alternation_congr fun w => by simp

/-- A block of certificates of length `0` can be added at the end. -/
theorem append_zero (h : IsAlternatingVerifier enc q ps V A) :
    IsAlternatingVerifier enc q (ps ++ [0]) V A := fun a => by
  rw [h a, List.map_append, List.map_singleton, Polynomial.eval_zero, alternation_append_zero]

/-- A block of certificates of length `0` can be added at the start, as a quantifier of the other
kind. -/
theorem zero_cons (h : IsAlternatingVerifier enc q ps V A) :
    IsAlternatingVerifier enc (!q) (0 :: ps) V A := fun a => by
  rw [h a, List.map_cons, Polynomial.eval_zero, alternation_zero_cons, Bool.not_not]

end IsAlternatingVerifier

/-- With one existential block, an alternating verifier is a verifier in the sense of `NP`. -/
theorem isAlternatingVerifier_true_singleton {p : Polynomial ℕ} :
    IsAlternatingVerifier enc true [p] V A ↔ IsVerifier enc p V A := by
  simp only [IsAlternatingVerifier, IsVerifier, List.map_cons, List.map_nil,
    alternation_singleton_true]

/-! ### The levels of the hierarchy -/

/-- The level `Σₖ` of the polynomial hierarchy, with respect to the encoding `enc` of instances:
the problems verified in polynomial time through `k` alternating blocks of polynomially long
certificates, the first existential. -/
def SigmaP (k : ℕ) (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (ps : List (Polynomial ℕ)) (V : α × List Bool → Bool), ps.length = k ∧
    ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧
      IsAlternatingVerifier enc true ps V A}

/-- The level `Πₖ` of the polynomial hierarchy, with respect to the encoding `enc` of instances:
the problems verified in polynomial time through `k` alternating blocks of polynomially long
certificates, the first universal. -/
def PiP (k : ℕ) (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (ps : List (Polynomial ℕ)) (V : α × List Bool → Bool), ps.length = k ∧
    ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧
      IsAlternatingVerifier enc false ps V A}

/-- The polynomial hierarchy: the union of the levels `Σₖ`. -/
def PH (enc : α ↪ List Bool) : Set (Set α) := ⋃ k, SigmaP k enc

variable {k : ℕ}

theorem mem_SigmaP : A ∈ SigmaP k enc ↔
    ∃ (ps : List (Polynomial ℕ)) (V : α × List Bool → Bool), ps.length = k ∧
      ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧
        IsAlternatingVerifier enc true ps V A :=
  Iff.rfl

theorem mem_PiP : A ∈ PiP k enc ↔
    ∃ (ps : List (Polynomial ℕ)) (V : α × List Bool → Bool), ps.length = k ∧
      ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧
        IsAlternatingVerifier enc false ps V A :=
  Iff.rfl

theorem mem_PH : A ∈ PH enc ↔ ∃ k, A ∈ SigmaP k enc := Set.mem_iUnion

/-! ### The first levels -/

/-- Without quantifiers, it does not matter which quantifier would have come first. -/
theorem SigmaP_zero_eq_PiP_zero : SigmaP 0 enc = PiP 0 enc := by
  ext A
  constructor <;>
  · rintro ⟨ps, V, hk, hV, h⟩
    obtain rfl := List.length_eq_zero_iff.1 hk
    exact ⟨[], V, rfl, hV, fun a => by simpa using h a⟩

/-- **`Σ₁ = NP`.** -/
theorem SigmaP_one : SigmaP 1 enc = NP enc := by
  ext A
  constructor
  · rintro ⟨ps, V, hk, hV, h⟩
    obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hk
    exact ⟨p, V, hV, isAlternatingVerifier_true_singleton.1 h⟩
  · rintro ⟨p, V, hV, h⟩
    exact ⟨[p], V, rfl, hV, isAlternatingVerifier_true_singleton.2 h⟩

/-- `P ⊆ Σ₀`, given that a polynomial-time function of the instance stays polynomial-time when it
is given a certificate to ignore. -/
theorem P_subset_SigmaP_zero
    (hfst : ∀ f : α → Bool, ComputableTidilyInPolyTime f enc encBool →
      ComputableTidilyInPolyTime (fun x : α × List Bool => f x.1) (encPair enc encBits) encBool) :
    P enc ⊆ SigmaP 0 enc := fun _ ⟨f, hf, h⟩ =>
  ⟨[], fun x => f x.1, rfl, hfst f hf, fun a => by simpa using h a⟩

/-- `Σ₀ ⊆ P`, given that a polynomial-time function of an instance and a certificate stays
polynomial-time when the certificate is fixed to be empty. -/
theorem SigmaP_zero_subset_P
    (hnil : ∀ V : α × List Bool → Bool, ComputableTidilyInPolyTime V (encPair enc encBits) encBool →
      ComputableTidilyInPolyTime (fun a => V (a, [])) enc encBool) :
    SigmaP 0 enc ⊆ P enc := by
  rintro _ ⟨ps, V, hk, hV, h⟩
  obtain rfl := List.length_eq_zero_iff.1 hk
  exact ⟨fun a => V (a, []), hnil V hV, fun a => by simpa using h a⟩

/-! ### Inclusions between levels -/

theorem SigmaP_subset_SigmaP_succ (k : ℕ) : SigmaP k enc ⊆ SigmaP (k + 1) enc :=
  fun _ ⟨ps, V, hk, hV, h⟩ => ⟨ps ++ [0], V, by simp [hk], hV, h.append_zero⟩

theorem PiP_subset_PiP_succ (k : ℕ) : PiP k enc ⊆ PiP (k + 1) enc :=
  fun _ ⟨ps, V, hk, hV, h⟩ => ⟨ps ++ [0], V, by simp [hk], hV, h.append_zero⟩

theorem SigmaP_subset_PiP_succ (k : ℕ) : SigmaP k enc ⊆ PiP (k + 1) enc :=
  fun _ ⟨ps, V, hk, hV, h⟩ => ⟨0 :: ps, V, by simp [hk], hV, h.zero_cons⟩

theorem PiP_subset_SigmaP_succ (k : ℕ) : PiP k enc ⊆ SigmaP (k + 1) enc :=
  fun _ ⟨ps, V, hk, hV, h⟩ => ⟨0 :: ps, V, by simp [hk], hV, h.zero_cons⟩

theorem SigmaP_mono : Monotone fun k => SigmaP k enc :=
  monotone_nat_of_le_succ SigmaP_subset_SigmaP_succ

theorem PiP_mono : Monotone fun k => PiP k enc :=
  monotone_nat_of_le_succ PiP_subset_PiP_succ

theorem SigmaP_subset_PH (k : ℕ) : SigmaP k enc ⊆ PH enc :=
  Set.subset_iUnion (fun k => SigmaP k enc) k

theorem PiP_subset_PH (k : ℕ) : PiP k enc ⊆ PH enc :=
  (PiP_subset_SigmaP_succ k).trans (SigmaP_subset_PH _)

/-- The polynomial hierarchy is also the union of the levels `Πₖ`. -/
theorem PH_eq_iUnion_PiP : PH enc = ⋃ k, PiP k enc :=
  (Set.iUnion_subset fun k =>
    (SigmaP_subset_PiP_succ k).trans (Set.subset_iUnion (fun k => PiP k enc) (k + 1))).antisymm
    (Set.iUnion_subset PiP_subset_PH)

theorem NP_subset_PH : NP enc ⊆ PH enc := SigmaP_one (enc := enc) ▸ SigmaP_subset_PH 1

/-- `P ⊆ PH`, given that a polynomial-time function of the instance stays polynomial-time when it is
given a certificate to ignore. -/
theorem P_subset_PH
    (hfst : ∀ f : α → Bool, ComputableTidilyInPolyTime f enc encBool →
      ComputableTidilyInPolyTime (fun x : α × List Bool => f x.1) (encPair enc encBits) encBool) :
    P enc ⊆ PH enc :=
  (P_subset_SigmaP_zero hfst).trans (SigmaP_subset_PH 0)

/-! ### Quantifier duality -/

section Duality

/- The theorems in this section assume that negating its output keeps a polynomial-time function
polynomial-time (`hnot`), which follows from the composition of polynomial-time functions once that
is in cslib. -/

variable
  (hnot : ∀ V : α × List Bool → Bool, ComputableTidilyInPolyTime V (encPair enc encBits) encBool →
    ComputableTidilyInPolyTime (fun x => !V x) (encPair enc encBits) encBool)
include hnot

theorem compl_mem_PiP_of_mem_SigmaP (hA : A ∈ SigmaP k enc) : Aᶜ ∈ PiP k enc :=
  let ⟨ps, V, hk, hV, h⟩ := hA
  ⟨ps, fun x => !V x, hk, hnot V hV, h.compl⟩

theorem compl_mem_SigmaP_of_mem_PiP (hA : A ∈ PiP k enc) : Aᶜ ∈ SigmaP k enc :=
  let ⟨ps, V, hk, hV, h⟩ := hA
  ⟨ps, fun x => !V x, hk, hnot V hV, h.compl⟩

/-- **`Πₖ = coΣₖ`**, given that negation preserves polynomial time. -/
theorem PiP_eq_preimage_compl_SigmaP : PiP k enc = compl ⁻¹' SigmaP k enc := by
  ext A
  refine ⟨compl_mem_SigmaP_of_mem_PiP hnot, fun hA => ?_⟩
  simpa using compl_mem_PiP_of_mem_SigmaP hnot hA

/-- **`Σₖ = coΠₖ`**, given that negation preserves polynomial time. -/
theorem SigmaP_eq_preimage_compl_PiP : SigmaP k enc = compl ⁻¹' PiP k enc := by
  ext A
  refine ⟨compl_mem_PiP_of_mem_SigmaP hnot, fun hA => ?_⟩
  simpa using compl_mem_SigmaP_of_mem_PiP hnot hA

/-- **`Π₁ = coNP`**, given that negation preserves polynomial time. -/
theorem PiP_one_eq_coNP : PiP 1 enc = coNP enc := by
  rw [PiP_eq_preimage_compl_SigmaP hnot, SigmaP_one, coNP_eq_preimage_compl_NP]

theorem coNP_subset_PH : coNP enc ⊆ PH enc :=
  PiP_one_eq_coNP hnot ▸ PiP_subset_PH 1

end Duality

end Cslib.Complexity
