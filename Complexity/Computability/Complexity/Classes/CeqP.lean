/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP.Closure
public import Complexity.Computability.Complexity.Classes.PP.Characterization

/-!
# Exact counting: C=P

`CeqP` consists of zero sets of `GapP` functions, the gap characterization of `C=P`
[Fenner, Fortnow and Kurtz][FennerFortnowKurtz1994]. These are verifier-based counts; no counting
machine characterization is assumed.

## Main definitions

* `Cslib.Complexity.CeqP`: the exact counting class `C=P`.

## Main results

* `Cslib.Complexity.mem_CeqP_iff_exists_SharpP`: equality of two `#P` functions.
* `Cslib.Complexity.inter_mem_CeqP`, `Cslib.Complexity.union_mem_CeqP`.
* `Cslib.Complexity.coNP_subset_CeqP`, `Cslib.Complexity.CeqP_subset_PP`.
* `Cslib.Complexity.PolyTimeReducible.mem_CeqP`.

## References

* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994]
-/

@[expose] public section

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool} {A B : Set α}

/-- `C=P`, the zero sets of integer-valued `GapP` functions. -/
def CeqP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ g ∈ GapP enc, ∀ a, a ∈ A ↔ g a = 0}

/-- A language is in `C=P` iff membership is equality of two accepting counts. -/
theorem mem_CeqP_iff_exists_SharpP : A ∈ CeqP enc ↔
    ∃ f ∈ SharpP enc, ∃ g ∈ SharpP enc, ∀ a, a ∈ A ↔ f a = g a := by
  constructor
  · rintro ⟨h, ⟨f, hf, g, hg, hh⟩, hA⟩
    exact ⟨f, hf, g, hg, fun a => by simpa [hh a, sub_eq_zero] using hA a⟩
  · rintro ⟨f, hf, g, hg, hA⟩
    exact ⟨_, GapP.natCast_sub_natCast_mem hf hg, fun a => by simpa [sub_eq_zero] using hA a⟩

/-- A coNP language is the zero set of the accepting count for its complement. -/
theorem coNP_subset_CeqP : coNP enc ⊆ CeqP enc := by
  intro A hA
  obtain ⟨f, hf, hA⟩ := mem_NP_iff_exists_SharpP.mp hA
  refine ⟨fun a => (f a : ℤ), SharpP.natCast_mem_GapP hf, fun a => ?_⟩
  simpa only [Set.mem_compl_iff, not_not, not_lt, Nat.le_zero, Int.natCast_eq_zero] using
    not_congr (hA a)

/-- A product vanishes exactly when one of its factors vanishes. -/
theorem union_mem_CeqP (hA : A ∈ CeqP enc) (hB : B ∈ CeqP enc) : A ∪ B ∈ CeqP enc := by
  obtain ⟨f, hf, hA⟩ := hA
  obtain ⟨g, hg, hB⟩ := hB
  exact ⟨f * g, GapP.mul_mem hf hg, fun a => by simp [hA a, hB a]⟩

/-- A sum of two integer squares vanishes exactly when both vanish. -/
theorem inter_mem_CeqP (hA : A ∈ CeqP enc) (hB : B ∈ CeqP enc) : A ∩ B ∈ CeqP enc := by
  obtain ⟨f, hf, hA⟩ := hA
  obtain ⟨g, hg, hB⟩ := hB
  refine ⟨f * f + g * g, GapP.add_mem (GapP.mul_mem hf hf) (GapP.mul_mem hg hg), fun a => ?_⟩
  simp only [Set.mem_inter_iff, hA a, hB a, Pi.add_apply, Pi.mul_apply]
  constructor
  · rintro ⟨h₁, h₂⟩
    simp [h₁, h₂]
  · intro h
    have h₁ := sq_nonneg (f a)
    have h₂ := sq_nonneg (g a)
    constructor <;> nlinarith

/-- `C=P ⊆ PP`: for integer `g`, the gap `1 - g²` is positive precisely at its zeros. -/
theorem CeqP_subset_PP : CeqP enc ⊆ PP enc := by
  rintro A ⟨g, hg, hA⟩
  refine mem_PP_iff_exists_GapP.mpr
    ⟨1 - g * g, GapP.sub_mem' GapP.one_mem (GapP.mul_mem hg hg), fun a => ?_⟩
  simp only [hA a, Pi.sub_apply, Pi.one_apply, Pi.mul_apply]
  constructor
  · intro h
    simp [h]
  · intro h
    have := sq_nonneg (g a)
    nlinarith [sq_nonneg (g a - 1), sq_nonneg (g a + 1)]

/-- `C=P` is closed under polynomial-time many-one reductions. -/
theorem PolyTimeReducible.mem_CeqP {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ CeqP encB) : A ∈ CeqP enc := by
  obtain ⟨g, hg, hAB⟩ := h
  obtain ⟨f, hf, hB⟩ := hB
  exact ⟨f ∘ g, GapP.comp_mem hf hg, fun a => (hAB a).trans (hB (g a))⟩

end Cslib.Complexity
