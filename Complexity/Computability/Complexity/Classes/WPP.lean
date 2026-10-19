/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SPP
public import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Wide and length-dependent counting gaps

WPP allows a GapP function to take either zero or a nonzero polynomial-time computable integer
target; LWPP restricts that target to depend on input length. We follow
[Hemaspaandra et al., Definitions 2.4–2.5][HemaspaandraEtAl2018], crediting the original
[Fenner–Fortnow–Kurtz][FennerFortnowKurtz1994] definitions. Targets use binary integers
`encIntBin`; the length argument of LWPP uses unary `encUnary`, so an exponentially large
numeric target is permitted. These are verifier-based counting classes, without a proved
nondeterministic-machine characterization. The basic containments and Boolean closures below
are algebraic consequences; oracle lowness and robustness are not claimed.

## Main definitions

* `WPP`: an input-dependent nonzero FP target.
* `LWPP`: a nonzero FP target depending only on encoded input length.

## Main results

* `SPP_subset_LWPP`, `LWPP_subset_WPP`, `WPP_subset_CeqP`, `WPP_subset_coCeqP`.
* `compl_mem_WPP`, `inter_mem_WPP`, `union_mem_WPP`: Boolean closure.
* `compl_mem_LWPP`, `inter_mem_LWPP`, `union_mem_LWPP`: length-dependent Boolean closure.
* `PolyTimeReducible.mem_WPP`: polynomial-time reduction closure.

## References

* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994]
* [E. Hemaspaandra et al., *The Robustness of LWPP and WPP, with an Application to Graph
  Reconstruction*][HemaspaandraEtAl2018]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β : Type} {enc : α ↪ List Bool} {A B : Set α}

/-- Wide gaps: zero on nonmembers and a nonzero binary FP target on members. -/
def WPP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ g ∈ GapP enc, ∃ f : α → ℤ, ComputableTidilyInPolyTime f enc encIntBin ∧
    (∀ a, f a ≠ 0) ∧ (∀ a, g a = 0 ∨ g a = f a) ∧ ∀ a, a ∈ A ↔ g a = f a}

/-- Wide gaps with a target computed in polynomial time from unary input length. -/
def LWPP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ g ∈ GapP enc, ∃ f : ℕ → ℤ, ComputableTidilyInPolyTime f encUnary encIntBin ∧
    (∀ n, f n ≠ 0) ∧ (∀ a, g a = 0 ∨ g a = f (enc a).length) ∧
    ∀ a, a ∈ A ↔ g a = f (enc a).length}

/-- The constant target one witnesses the SPP containment. -/
theorem SPP_subset_LWPP : SPP enc ⊆ LWPP enc := by
  rintro A ⟨g, hg, hr, hA⟩
  exact ⟨g, hg, fun _ => 1, .const _, fun _ => one_ne_zero, hr, hA⟩

/-- Computing the encoded input length turns an LWPP target into a WPP target. -/
theorem LWPP_subset_WPP : LWPP enc ⊆ WPP enc := by
  rintro A ⟨g, hg, f, hf, hn, hr, hA⟩
  exact ⟨g, hg, fun a => f (enc a).length,
    hf.comp (.encoding_length enc), fun a => hn _, hr, hA⟩

/-- Subtraction of the target gives a zero test for WPP membership. -/
theorem WPP_subset_CeqP : WPP enc ⊆ CeqP enc := by
  rintro A ⟨g, hg, f, hf, -, -, hA⟩
  exact ⟨g - f, GapP.sub_mem' hg (GapP.of_polyTime hf), fun a => by
    simpa [sub_eq_zero] using hA a⟩

/-- A WPP gap is nonzero exactly on members. -/
theorem WPP_subset_coCeqP : WPP enc ⊆ coCeqP enc := by
  rintro A ⟨g, hg, f, -, hn, hr, hA⟩
  refine mem_coCeqP_iff_exists_GapP.mpr ⟨g, hg, fun a => ?_⟩
  rw [hA a]
  rcases hr a with h | h <;> simp [h, hn a, (hn a).symm]

/-- Complement exchanges the zero and target values. -/
theorem compl_mem_WPP (hA : A ∈ WPP enc) : Aᶜ ∈ WPP enc := by
  obtain ⟨g, hg, f, hf, hn, hr, hA⟩ := hA
  refine ⟨f - g, GapP.sub_mem' (GapP.of_polyTime hf) hg, f, hf, hn,
    fun a => ?_, fun a => ?_⟩
  · rcases hr a with h | h <;> simp [h]
  · rcases hr a with h | h <;> simp [hA a, h, (hn a).symm]

/-- Products preserve the zero-or-target condition and the target is still nonzero. -/
theorem inter_mem_WPP (hA : A ∈ WPP enc) (hB : B ∈ WPP enc) : A ∩ B ∈ WPP enc := by
  obtain ⟨g, hg, f, hf, hn, hr, hA⟩ := hA
  obtain ⟨g', hg', f', hf', hn', hr', hB⟩ := hB
  refine ⟨g * g', GapP.mul_mem hg hg', f * f', hf.intBin_mul' hf',
    fun a => mul_ne_zero (hn a) (hn' a), fun a => ?_, fun a => ?_⟩
  · rcases hr a with h | h <;> rcases hr' a with h' | h' <;> simp [h, h']
  · rcases hr a with h | h <;> rcases hr' a with h' | h' <;>
      simp [hA a, hB a, h, h', hn a, hn' a, (hn a).symm, (hn' a).symm]

/-- Union follows by De Morgan's law. -/
theorem union_mem_WPP (hA : A ∈ WPP enc) (hB : B ∈ WPP enc) : A ∪ B ∈ WPP enc := by
  simpa [Set.compl_inter] using
    compl_mem_WPP (inter_mem_WPP (compl_mem_WPP hA) (compl_mem_WPP hB))

/-- Polynomial-time precomposition preserves the target and the exact gap. -/
theorem PolyTimeReducible.mem_WPP {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ WPP encB) : A ∈ WPP enc := by
  obtain ⟨r, hr, hAB⟩ := h
  obtain ⟨g, hg, f, hf, hn, hgr, hB⟩ := hB
  exact ⟨g ∘ r, GapP.comp_mem hg hr, f ∘ r, hf.comp hr, fun a => hn _,
    fun a => hgr _, fun a => (hAB a).trans (hB _)⟩

/-- The complementary gap uses the same length-dependent target. -/
theorem compl_mem_LWPP (hA : A ∈ LWPP enc) : Aᶜ ∈ LWPP enc := by
  obtain ⟨g, hg, f, hf, hn, hr, hA⟩ := hA
  have htarget := GapP.of_polyTime (hf.comp (.encoding_length enc))
  refine ⟨(fun a => f (enc a).length) - g, GapP.sub_mem' htarget hg,
    f, hf, hn, fun a => ?_, fun a => ?_⟩
  · rcases hr a with h | h <;> simp [h]
  · rcases hr a with h | h <;> simp [hA a, h, (hn _).symm]

/-- Multiplying length-dependent targets preserves length dependence. -/
theorem inter_mem_LWPP (hA : A ∈ LWPP enc) (hB : B ∈ LWPP enc) : A ∩ B ∈ LWPP enc := by
  obtain ⟨g, hg, f, hf, hn, hr, hA⟩ := hA
  obtain ⟨g', hg', f', hf', hn', hr', hB⟩ := hB
  refine ⟨g * g', GapP.mul_mem hg hg', f * f', hf.intBin_mul' hf',
    fun n => mul_ne_zero (hn n) (hn' n), fun a => ?_, fun a => ?_⟩
  · rcases hr a with h | h <;> rcases hr' a with h' | h' <;> simp [h, h']
  · rcases hr a with h | h <;> rcases hr' a with h' | h' <;>
      simp [hA a, hB a, h, h', hn _, hn' _, (hn _).symm, (hn' _).symm]

/-- Union preserves length-dependent targets. -/
theorem union_mem_LWPP (hA : A ∈ LWPP enc) (hB : B ∈ LWPP enc) : A ∪ B ∈ LWPP enc := by
  simpa [Set.compl_inter] using
    compl_mem_LWPP (inter_mem_LWPP (compl_mem_LWPP hA) (compl_mem_LWPP hB))

end Cslib.Complexity
