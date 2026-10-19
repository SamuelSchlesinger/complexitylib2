/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP
public import Complexity.Computability.Complexity.Classes.BPP
public import Complexity.Computability.Complexity.Classes.PP
public import Complexity.Computability.Complexity.Reduction
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Complexity.Classes.BPP.Amplification
import Complexity.Computability.Complexity.Classes.PP.Characterization
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Small bounded-error polynomial time

SBP was introduced by [Böhler, Glaßer and Meister][BoehlerGlasserMeister2006]. We use
[Watson, Definition 2][Watson2012]: a #P count is at least a binary FP threshold on
members and strictly less than half the threshold on nonmembers. The threshold may
be zero; `mem_SBP_iff_exists_pos_threshold` shows that requiring positivity is equivalent.
These are verifier counts, without a proved nondeterministic counting-machine equivalence.
The containments and union closure below are elementary counting-algebra consequences;
the stronger MA and AM containments are not proved here.

## Main definitions

* `SBP`: small bounded-error polynomial time with an input-dependent FP threshold.

## Main results

* `NP_subset_SBP`, `BPP_subset_SBP`, `SBP_subset_PP`.
* `union_mem_SBP`, `PolyTimeReducible.mem_SBP`: union and many-one reduction closure.

## References

* [E. Böhler, C. Glaßer, D. Meister, *Error-bounded probabilistic computations between
  MA and AM*][BoehlerGlasserMeister2006]
* [T. Watson, *The Complexity of Estimating Min-Entropy*][Watson2012]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β : Type} {enc : α ↪ List Bool} {A B : Set α}

/-- A #P count at least an FP threshold on members and strictly below half on nonmembers.
The threshold is encoded in binary and may be exponentially large. -/
def SBP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ SharpP enc, ∃ k : α → ℕ, ComputableTidilyInPolyTime k enc encNat ∧
    ∀ a, (a ∈ A → k a ≤ f a) ∧ (a ∉ A → 2 * f a < k a)}

/-- Replacing `(f, k)` by `(2f + 1, 2k + 1)` makes the threshold positive. -/
theorem mem_SBP_iff_exists_pos_threshold : A ∈ SBP enc ↔
    ∃ f ∈ SharpP enc, ∃ k : α → ℕ, ComputableTidilyInPolyTime k enc encNat ∧
      (∀ a, 0 < k a) ∧ ∀ a, (a ∈ A → k a ≤ f a) ∧ (a ∉ A → 2 * f a < k a) := by
  constructor
  · rintro ⟨f, hf, k, hk, hA⟩
    refine ⟨f + f + 1, SharpP.add_mem (SharpP.add_mem hf hf) SharpP.one_mem,
      fun a => k a + k a + 1, (hk.binary_add' hk).binary_add' (.const 1),
      fun a => by positivity, fun a => ?_⟩
    simp only [Pi.add_apply, Pi.one_apply]
    constructor
    · intro ha
      have := (hA a).1 ha
      lia
    · intro ha
      have := (hA a).2 ha
      lia
  · rintro ⟨f, hf, k, hk, -, hA⟩
    exact ⟨f, hf, k, hk, hA⟩

/-- Threshold one recognizes precisely the positive #P counts. -/
theorem NP_subset_SBP : NP enc ⊆ SBP enc := by
  intro A hA
  obtain ⟨f, hf, hA⟩ := mem_NP_iff_exists_SharpP.mp hA
  refine ⟨f, hf, fun _ => 1, .const 1, fun a => ?_⟩
  rw [hA a]
  constructor <;> intro h <;> lia

/-- Amplifying BPP to error at most one quarter leaves a strict factor-two count gap. -/
theorem BPP_subset_SBP : BPP enc ⊆ SBP enc := by
  intro A hA
  obtain ⟨p, V, hV, hA⟩ := mem_BPP_iff_forall_decidesWithErrorExponent.mp hA 2
  have hf : (fun a => acceptCount V a (p.eval (enc a).length)) ∈ SharpP enc :=
    ⟨p, V, hV, fun _ => rfl⟩
  have hd : ComputableTidilyInPolyTime (fun a => 2 ^ p.eval (enc a).length) enc encNat :=
    ComputableTidilyInPolyTime.binary_two_pow.comp
      ((ComputableTidilyInPolyTime.unary_eval p).comp (.encoding_length enc))
  refine ⟨_, SharpP.mul_mem (SharpP.natCast_mem 3) hf,
    fun a => 2 * 2 ^ p.eval (enc a).length,
    (ComputableTidilyInPolyTime.const 2).binary_mul' hd, fun a => ?_⟩
  have hs := acceptCount_add_card_filter_eq_false (V := V) (a := a)
    (n := p.eval (enc a).length)
  have hp : 0 < 2 ^ p.eval (enc a).length := by positivity
  have h := hA a
  simp only [Polynomial.eval_ofNat] at h
  change (a ∈ A → _ ≤ 3 * acceptCount V a (p.eval (enc a).length)) ∧ _
  constructor <;> intro ha
  · have := h.1 ha
    lia
  · have := h.2 ha
    change 2 * (3 * acceptCount V a (p.eval (enc a).length)) < _
    rw [← acceptCount] at this
    lia

/-- The integer gap `2f - k + 1` is positive exactly on members, including zero thresholds. -/
theorem SBP_subset_PP : SBP enc ⊆ PP enc := by
  rintro A ⟨f, hf, k, hk, hA⟩
  have hg := GapP.sub_mem' (SharpP.natCast_mem_GapP (SharpP.add_mem hf hf))
    (SharpP.natCast_mem_GapP (SharpP.of_polyTime hk))
  refine mem_PP_iff_exists_GapP.mpr ⟨_, GapP.add_mem hg GapP.one_mem, fun a => ?_⟩
  change a ∈ A ↔ 0 < ((f a + f a : ℕ) : ℤ) - (k a : ℤ) + 1
  by_cases ha : a ∈ A
  · have := (hA a).1 ha
    simp only [ha, true_iff]
    lia
  · have := (hA a).2 ha
    simp only [ha, false_iff]
    lia

/-- Precomposition preserves both the count and the binary FP threshold. -/
theorem PolyTimeReducible.mem_SBP {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ SBP encB) : A ∈ SBP enc := by
  obtain ⟨r, hr, hAB⟩ := h
  obtain ⟨f, hf, k, hk, hB⟩ := hB
  exact ⟨f ∘ r, SharpP.comp_mem hf hr, k ∘ r, hk.comp hr, fun a => by
    simpa only [Function.comp_apply, ← hAB a] using hB (r a)⟩

/-- Normalize two positive thresholds by cross multiplication, then square and add the counts. -/
theorem union_mem_SBP (hA : A ∈ SBP enc) (hB : B ∈ SBP enc) : A ∪ B ∈ SBP enc := by
  obtain ⟨f, hf, k, hk, hkpos, hA⟩ := mem_SBP_iff_exists_pos_threshold.mp hA
  obtain ⟨g, hg, l, hl, hlpos, hB⟩ := mem_SBP_iff_exists_pos_threshold.mp hB
  have hfl := SharpP.mul_mem hf (SharpP.of_polyTime hl)
  have hgk := SharpP.mul_mem hg (SharpP.of_polyTime hk)
  refine ⟨_, SharpP.add_mem (SharpP.pow_mem hfl 2) (SharpP.pow_mem hgk 2),
    fun a => (k a * l a) ^ 2, (hk.binary_mul' hl).binary_pow' (.const 2), fun a => ?_⟩
  change (a ∈ A ∪ B → (k a * l a) ^ 2 ≤ (f a * l a) ^ 2 + (g a * k a) ^ 2) ∧
    (a ∉ A ∪ B → 2 * ((f a * l a) ^ 2 + (g a * k a) ^ 2) < (k a * l a) ^ 2)
  constructor
  · rintro (ha | ha)
    · have := Nat.mul_le_mul_right (l a) ((hA a).1 ha)
      exact (Nat.pow_le_pow_left this 2).trans (Nat.le_add_right _ _)
    · have := Nat.mul_le_mul_right (k a) ((hB a).1 ha)
      rw [Nat.mul_comm (l a)] at this
      exact (Nat.pow_le_pow_left this 2).trans (Nat.le_add_left _ _)
  · intro ha
    have haA : a ∉ A := fun h => ha (Or.inl h)
    have haB : a ∉ B := fun h => ha (Or.inr h)
    have h1 := Nat.mul_lt_mul_of_pos_right ((hA a).2 haA) (hlpos a)
    have h2 := Nat.mul_lt_mul_of_pos_right ((hB a).2 haB) (hkpos a)
    have h1' : 2 * (f a * l a) < k a * l a := by nlinarith
    have h2' : 2 * (g a * k a) < k a * l a := by nlinarith
    have hs1 := Nat.pow_lt_pow_left h1' (by decide : 2 ≠ 0)
    have hs2 := Nat.pow_lt_pow_left h2' (by decide : 2 ≠ 0)
    nlinarith only [hs1, hs2]

end Cslib.Complexity
