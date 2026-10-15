/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Hastad
import Complexity.Computability.Circuit.Depth
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Random restrictions simplify small circuits

The stages of Håstad's argument, counted: at most a `g / 2 ^ s` fraction of the restrictions
leaving `n / (16 s + 1) ^ d` bits free fail to make every gate of a program with `g` gates and
depth `d` shallow (`Unbounded.two_pow_mul_card_filter_exists_not_shallow_le`). A uniformly random
restriction with `ℓ'` free bits is obtained by first drawing one with `ℓ ≥ ℓ'` free bits and then
an extension of it, since every restriction with `ℓ'` free bits extends the same number of
restrictions with `ℓ` free bits (`Restriction.card_filter_extends_withFree`,
`Restriction.sum_card_filter_extensions`). At each stage, restrictions that were already bad are
counted fully, and a good one has at most a `2 ^ (-s)` fraction of bad extensions for each gate
of the next depth (`Unbounded.two_pow_mul_card_filter_not_shallow_le`). This counting form is
what bounds the Fourier tails of small circuits of constant depth [Linial, Mansour and Nisan]
[LinialMansourNisan1993].

## Main results

* `Cslib.Circuits.Boolean.Restriction.sum_card_filter_extensions`: double counting extensions.
* `Cslib.Circuits.Boolean.Unbounded.two_pow_mul_card_filter_exists_not_shallow_le`: random
  restrictions make small circuits of constant depth shallow.

## References

* [N. Linial, Y. Mansour, N. Nisan, *Constant depth circuits, Fourier transform, and
  learnability*][LinialMansourNisan1993]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Finset

variable {n : ℕ}

namespace Restriction

/-- **Double counting extensions.** Summed over the restrictions with `ℓ` free bits, the extensions
with `ℓ' ≤ ℓ` free bits satisfying `P` count each restriction with `ℓ'` free bits satisfying `P`
once for each of the `C(n - ℓ', ℓ - ℓ')` restrictions it extends. -/
theorem sum_card_filter_extensions (P : Restriction n → Prop) [DecidablePred P] {ℓ ℓ' : ℕ}
    (hℓ : ℓ' ≤ ℓ) :
    ∑ ρ ∈ withFree n ℓ, ((ρ.extensions ℓ').filter P).card =
      ((withFree n ℓ').filter P).card * (n - ℓ').choose (ℓ - ℓ') := by
  classical
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := withFree n ℓ)
    (t := (withFree n ℓ').filter P) (r := fun ρ ρ' => ρ'.Extends ρ)
  have habove (ρ : Restriction n) : ((ρ.extensions ℓ').filter P).card =
      (((withFree n ℓ').filter P).bipartiteAbove (fun ρ ρ' => ρ'.Extends ρ) ρ).card := by
    congr 1
    ext ρ'
    simp only [mem_filter, mem_extensions, bipartiteAbove]
    tauto
  rw [sum_congr rfl fun ρ _ => habove ρ, h, sum_congr rfl fun ρ' hρ' => ?_, sum_const,
    smul_eq_mul]
  have hfree : ρ'.free.card = ℓ' := mem_withFree.1 (mem_filter.1 hρ').1
  rw [bipartiteBelow, ← hfree, card_filter_extends_withFree (hfree ▸ hℓ)]

end Restriction

namespace Unbounded

variable {s g : ℕ}

/-- The number of free bits after `j` stages. -/
private theorem le_div_pow_of_mul_pow_le' {d j : ℕ} (hj : j ≤ d) (hn : s * (16 * s + 1) ^ d ≤ n) :
    s ≤ n / (16 * s + 1) ^ j := by
  rw [Nat.le_div_iff_mul_le (Nat.pow_pos (by omega))]
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hj)).trans hn

/-- One stage shrinks the free bits by the factor `16 s + 1`. -/
private theorem mul_div_pow_succ_le' (j : ℕ) :
    (16 * s + 1) * (n / (16 * s + 1) ^ (j + 1)) ≤ n / (16 * s + 1) ^ j := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  exact Nat.mul_div_le _ _

open scoped Classical in
/-- **One stage, counted**: if every gate of depth at most `j` is shallow under `ρ`, at most an
`H / 2 ^ s` fraction of the extensions of `ρ` with `ℓ'` free bits make some gate of depth at most
`j + 1` deep, where `H` is the number of gates of depth `j + 1`. -/
private theorem two_pow_mul_card_filter_extensions_le {p : Program signature n g} (hs : 2 ≤ s)
    {j ℓ' : ℕ} {ρ : Restriction n} (hsℓ' : s ≤ ℓ') (hℓ : (16 * s + 1) * ℓ' ≤ ρ.free.card)
    (hgood : ∀ k, p.depths k ≤ j → Shallow s ρ fun x => p.eval interpretation x k) :
    2 ^ s * ((ρ.extensions ℓ').filter fun ρ' =>
        ∃ k, p.depths k ≤ j + 1 ∧ ¬ Shallow s ρ' fun x => p.eval interpretation x k).card ≤
      (univ.filter fun k => p.depths k = j + 1).card * (ρ.extensions ℓ').card := by
  set T := univ.filter fun k => p.depths k = j + 1
  -- a bad extension makes a gate of depth exactly `j + 1` deep
  have hsub : ((ρ.extensions ℓ').filter fun ρ' =>
      ∃ k, p.depths k ≤ j + 1 ∧ ¬ Shallow s ρ' fun x => p.eval interpretation x k) ⊆
      T.biUnion fun k => (ρ.extensions ℓ').filter fun ρ' =>
        ¬ Shallow s ρ' fun x => p.eval interpretation x k := by
    intro ρ' hρ'
    obtain ⟨hext, k, hk, hdeep⟩ := mem_filter.1 hρ'
    refine mem_biUnion.2 ⟨k, mem_filter.2 ⟨mem_univ k, ?_⟩, mem_filter.2 ⟨hext, hdeep⟩⟩
    by_contra hk'
    exact hdeep ((hgood k (by omega)).mono (Restriction.mem_extensions.1 hext).1)
  calc 2 ^ s * ((ρ.extensions ℓ').filter fun ρ' =>
        ∃ k, p.depths k ≤ j + 1 ∧ ¬ Shallow s ρ' fun x => p.eval interpretation x k).card
      ≤ 2 ^ s * ∑ k ∈ T, ((ρ.extensions ℓ').filter fun ρ' =>
          ¬ Shallow s ρ' fun x => p.eval interpretation x k).card :=
        Nat.mul_le_mul_left _ ((card_le_card hsub).trans card_biUnion_le)
    _ = ∑ k ∈ T, 2 ^ s * ((ρ.extensions ℓ').filter fun ρ' =>
          ¬ Shallow s ρ' fun x => p.eval interpretation x k).card := mul_sum _ _ _
    _ ≤ ∑ _k ∈ T, (ρ.extensions ℓ').card := sum_le_sum fun k hk => by
        -- gate `k` is its operation on shallow wires
        have hgate : (fun x => p.eval interpretation x k) = fun x =>
            interpretation (p.lines k).op fun a => p.trace interpretation x ((p.lines k).wires a) :=
          funext fun x => (p.lines_eval interpretation x k).symm
        rw [hgate]
        refine two_pow_mul_card_filter_not_shallow_le (fun a => ?_) (by omega) hsℓ' hℓ
        have hlt := p.wireDepths_lines_lt k a
        cases hw : (p.lines k).wires a with
        | input i => exact shallow_proj hs ρ i
        | gate k' =>
          rw [hw, Program.wireDepths_gateWire] at hlt
          exact hgood k' (by have := (mem_filter.1 hk).2; omega)
    _ = T.card * (ρ.extensions ℓ').card := by rw [sum_const, smul_eq_mul]

open scoped Classical in
/-- **Random restrictions make small circuits of constant depth shallow.** For a program with
gates of depth at most `d`, `s ≥ 2` and `s (16 s + 1) ^ d ≤ n`, after `j ≤ d` stages at most a
`G / 2 ^ s` fraction of the restrictions leaving `n / (16 s + 1) ^ j` bits free make some gate of
depth at most `j` deep, where `G` is the number of gates of depth at most `j`. -/
theorem two_pow_mul_card_filter_exists_not_shallow_le {p : Program signature n g} (hs : 2 ≤ s)
    {d : ℕ} (hn : s * (16 * s + 1) ^ d ≤ n) :
    ∀ j ≤ d, 2 ^ s * ((Restriction.withFree n (n / (16 * s + 1) ^ j)).filter fun ρ =>
        ∃ k, p.depths k ≤ j ∧ ¬ Shallow s ρ fun x => p.eval interpretation x k).card ≤
      (univ.filter fun k => p.depths k ≤ j).card *
        (Restriction.withFree n (n / (16 * s + 1) ^ j)).card
  | 0, _ => by
    rw [filter_false_of_mem fun ρ _ => fun ⟨k, hk, _⟩ => absurd hk (by
      have := p.depths_pos k
      omega)]
    simp
  | j + 1, hj => by
    have ih := two_pow_mul_card_filter_exists_not_shallow_le (p := p) hs hn j (by omega)
    set ℓ := n / (16 * s + 1) ^ j
    set ℓ' := n / (16 * s + 1) ^ (j + 1)
    set W := Restriction.withFree n ℓ
    set B : ℕ → Restriction n → Prop := fun i ρ =>
      ∃ k, p.depths k ≤ i ∧ ¬ Shallow s ρ fun x => p.eval interpretation x k
    set H := (univ.filter fun k => p.depths k = j + 1).card
    have hsℓ' : s ≤ ℓ' := le_div_pow_of_mul_pow_le' hj hn
    have hℓ : (16 * s + 1) * ℓ' ≤ ℓ := mul_div_pow_succ_le' j
    have hℓn : ℓ ≤ n := Nat.div_le_self _ _
    have hℓ'ℓ : ℓ' ≤ ℓ := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hℓ
    set F := (n - ℓ').choose (ℓ - ℓ')
    have hF : 0 < F := Nat.choose_pos (by omega)
    set T := ℓ.choose ℓ' * 2 ^ (ℓ - ℓ')
    have hT : ∀ ρ ∈ W, (ρ.extensions ℓ').card = T := fun ρ hρ => by
      rw [Restriction.card_extensions, Restriction.mem_withFree.1 hρ]
    -- each restriction with `ℓ` free bits has few bad extensions, unless it is bad itself
    have hper : ∀ ρ ∈ W, 2 ^ s * ((ρ.extensions ℓ').filter (B (j + 1))).card ≤
        (if B j ρ then 2 ^ s else 0) * T + H * T := fun ρ hρ => by
      by_cases hb : B j ρ
      · simp only [hb, ↓reduceIte]
        rw [← hT ρ hρ]
        exact (Nat.mul_le_mul_left _ (card_filter_le _ _)).trans (Nat.le_add_right _ _)
      · simp only [hb, ↓reduceIte, zero_mul, zero_add]
        rw [← hT ρ hρ]
        refine two_pow_mul_card_filter_extensions_le hs hsℓ'
          ((Restriction.mem_withFree.1 hρ).symm ▸ hℓ) fun k hk => ?_
        by_contra h
        exact hb ⟨k, hk, h⟩
    -- the gates of depth at most `j + 1`
    have hG : (univ.filter fun k => p.depths k ≤ j + 1).card =
        (univ.filter fun k => p.depths k ≤ j).card + H := by
      rw [← card_union_of_disjoint (disjoint_filter.2 fun k _ h₁ h₂ => by omega)]
      congr 1
      ext k
      simp only [mem_filter, mem_univ, true_and, mem_union]
      omega
    -- double counting the extensions, with and without the condition
    have hdc := Restriction.sum_card_filter_extensions (B (j + 1)) hℓ'ℓ
    have hall := Restriction.sum_card_filter_extensions (n := n) (fun _ => True) hℓ'ℓ
    simp only [filter_true] at hall
    rw [sum_congr rfl hT, sum_const, smul_eq_mul] at hall
    refine Nat.le_of_mul_le_mul_right (?_ : _ * F ≤ _ * F) hF
    calc 2 ^ s * ((Restriction.withFree n ℓ').filter (B (j + 1))).card * F
        = ∑ ρ ∈ W, 2 ^ s * ((ρ.extensions ℓ').filter (B (j + 1))).card := by
          rw [mul_assoc, ← hdc, mul_sum]
      _ ≤ ∑ ρ ∈ W, ((if B j ρ then 2 ^ s else 0) * T + H * T) := sum_le_sum hper
      _ = 2 ^ s * (W.filter (B j)).card * T + W.card * H * T := by
          rw [sum_add_distrib, ← sum_mul, sum_ite, sum_const_zero, add_zero, sum_const,
            smul_eq_mul, sum_const, smul_eq_mul]
          ring
      _ ≤ (univ.filter fun k => p.depths k ≤ j).card * W.card * T + W.card * H * T := by
          gcongr
      _ = (univ.filter fun k => p.depths k ≤ j + 1).card * (Restriction.withFree n ℓ').card *
            F := by
          rw [mul_assoc _ (Restriction.withFree n ℓ').card, hG, ← hall]
          ring

end Unbounded

end Cslib.Circuits.Boolean
