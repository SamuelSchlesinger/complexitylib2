/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Code.Basic
public import Complexity.Foundations.Data.ListDecoding
import Complexity.Foundations.Data.Hamming
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.List.GetD

/-!
# The Johnson bound

Let `C` be a code of length `n` and minimum distance at least `d`, and let `w` be a word. Each
codeword `c` within distance `e` of `w` agrees with `w` on a set of at least `a = n - e`
coordinates, and two distinct codewords agree with each other, hence on the intersection of their
sets, on at most `t = n - d` coordinates. Counting the pairs of such codewords that agree with
`w` at a coordinate, and applying the Cauchy–Schwarz inequality to the numbers of codewords that
agree with `w` at each coordinate, the number `L` of codewords within distance `e` satisfies
`L * (a ^ 2 - n * t) ≤ n * (a - t)` (`Cslib.Code.card_filter_hammingDist_le_mul_le`). When
`a ^ 2 > n * t`, that is when `e < n - √(n * (n - d))`, a Hamming ball of radius `e` therefore
contains at most `n * (d - e)` codewords (`Cslib.Code.card_filter_hammingDist_le_le`), whatever
the alphabet: the **Johnson bound** [Johnson1962], [GuruswamiRudraSudan2019]. Listing the messages
whose codewords lie in the ball is then a list decoder up to radius `e / n` with lists of
`n * (d - e)` messages (`Cslib.Code.exists_listCode_listDecodes`), in the sense of
`Cslib.ListCode.ListDecodes`; the decoder is chosen noncomputably, and no running time is claimed.

## Main results

* `Cslib.Code.card_filter_hammingDist_le_mul_le`: the Johnson bound, in agreement form.
* `Cslib.Code.card_filter_hammingDist_le_le`: the Johnson bound on list sizes.
* `Cslib.Code.exists_listCode_listDecodes`: list decoding up to the Johnson radius.

## References

* [S. M. Johnson, *A new upper bound for error-correcting codes*][Johnson1962]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2019]
-/

@[expose] public section

namespace Cslib.Code

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq α]

/-- **Double counting for the Johnson bound.** If `L` sets `B c ⊆ ι` of size `a` meet pairwise in
at most `t` elements, then `L * a ^ 2 ≤ n * (a + (L - 1) * t)`, where `n = |ι|`. -/
private theorem card_mul_sq_le {κ : Type*} [DecidableEq ι] (L : Finset κ)
    (B : κ → Finset ι) {a t : ℕ} (hB : ∀ c ∈ L, #(B c) = a)
    (hinter : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' → #(B c ∩ B c') ≤ t) :
    #L * a ^ 2 ≤ Fintype.card ι * (a + (#L - 1) * t) := by
  classical
  -- `m i` codewords agree with the word at the coordinate `i`
  let m : ι → ℕ := fun i => #{c ∈ L | i ∈ B c}
  have hsum : ∑ i, m i = #L * a := by
    simp only [m, card_filter]
    rw [sum_comm]
    simp only [← card_filter, filter_mem_eq_inter, univ_inter]
    rw [sum_congr rfl hB, sum_const, smul_eq_mul]
  have hsq : ∑ i, m i ^ 2 = ∑ c ∈ L, ∑ c' ∈ L, #(B c ∩ B c') := by
    simp only [m, card_filter, sq, sum_mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun c _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun c' _ => ?_
    simp only [ite_zero_mul_ite_zero, mul_one, ← card_filter]
    congr 1
    ext i
    simp
  have hrow : ∀ c ∈ L, ∑ c' ∈ L, #(B c ∩ B c') ≤ a + (#L - 1) * t := by
    intro c hc
    rw [← add_sum_erase L _ hc, inter_self, hB c hc]
    gcongr
    calc ∑ c' ∈ L.erase c, #(B c ∩ B c') ≤ ∑ _c' ∈ L.erase c, t :=
          sum_le_sum fun c' hc' => hinter c hc c' (mem_of_mem_erase hc') (ne_of_mem_erase hc').symm
      _ = (#L - 1) * t := by rw [sum_const, card_erase_of_mem hc, smul_eq_mul]
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι)) (f := m)
  rw [hsum, hsq, card_univ] at hcs
  rcases L.eq_empty_or_nonempty with rfl | hL
  · simp
  have hL0 : 0 < #L := hL.card_pos
  have : (#L * a) ^ 2 ≤ Fintype.card ι * (#L * (a + (#L - 1) * t)) :=
    hcs.trans (Nat.mul_le_mul_left _ ((sum_le_sum hrow).trans_eq (by rw [sum_const, smul_eq_mul])))
  rw [mul_pow, sq (#L), mul_assoc, Nat.mul_left_comm (Fintype.card ι) (#L)] at this
  exact Nat.le_of_mul_le_mul_left this hL0

/-- **The Johnson bound**, in agreement form: for a code of length `n` and minimum distance at
least `d`, the number `L` of codewords within distance `e` of a word `w` satisfies
`L * ((n - e) ^ 2 - n * (n - d)) ≤ n * (d - e)`. It bounds `L` when `n * (n - d) < (n - e) ^ 2`
and says nothing otherwise. -/
theorem card_filter_hammingDist_le_mul_le {C : Finset (ι → α)} {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α))) (w : ι → α) (e : ℕ) :
    #{c ∈ C | hammingDist c w ≤ e} *
        ((Fintype.card ι - e) ^ 2 - Fintype.card ι * (Fintype.card ι - d)) ≤
      Fintype.card ι * (d - e) := by
  classical
  set n := Fintype.card ι
  set L : Finset (ι → α) := {c ∈ C | hammingDist c w ≤ e}
  -- each codeword in the ball agrees with `w` on a set `B c` of exactly `n - e` coordinates
  have hagree : ∀ c ∈ L, n - e ≤ #({i | c i = w i} : Finset ι) := by
    intro c hc
    have h1 := card_filter_eq_add_hammingDist c w
    have h2 := (mem_filter.1 hc).2
    omega
  choose! B hBsub hBcard using fun c hc => exists_subset_card_eq (hagree c hc)
  -- two distinct codewords agree on at most `n - d` coordinates
  have hinter : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' → #(B c ∩ B c') ≤ n - d := by
    intro c hc c' hc' hne
    have hsub : B c ∩ B c' ⊆ ({i | c i = c' i} : Finset ι) := by
      intro i hi
      have h1 := (mem_filter.1 (hBsub c hc (mem_inter.1 hi).1)).2
      have h2 := (mem_filter.1 (hBsub c' hc' (mem_inter.1 hi).2)).2
      exact mem_filter.2 ⟨mem_univ i, h1.trans h2.symm⟩
    have h1 := card_filter_eq_add_hammingDist c c'
    have h2 := Nat.cast_le.1 (le_minDist_iff.1 hd c (mem_filter.1 hc).1 c' (mem_filter.1 hc').1 hne)
    have := card_le_card hsub
    omega
  have key := card_mul_sq_le L B hBcard hinter
  -- arithmetic, with `a = n - e` and `t = n - d`
  have hmain : #L * ((n - e) ^ 2 - n * (n - d)) ≤ n * ((n - e) - (n - d)) := by
    rcases le_or_gt ((n - e) ^ 2) (n * (n - d)) with h | h
    · rw [Nat.sub_eq_zero_of_le h, mul_zero]
      exact Nat.zero_le _
    rcases Nat.eq_zero_or_pos #L with hL | hL
    · rw [hL, zero_mul]
      exact Nat.zero_le _
    have ht : n - d ≤ n := Nat.sub_le _ _
    have hat : n - d ≤ n - e := by
      by_contra hlt
      have : (n - e) ^ 2 ≤ (n - d) * (n - d) := by
        rw [sq]
        exact Nat.mul_le_mul (by omega) (by omega)
      exact absurd h (not_lt.2 (this.trans (Nat.mul_le_mul_right _ ht)))
    zify [h.le, hat, Nat.one_le_iff_ne_zero.2 hL.ne'] at key ⊢
    nlinarith
  exact hmain.trans (Nat.mul_le_mul_left _ (by omega))

/-- **The Johnson bound** [Johnson1962]: if `n * (n - d) < (n - e) ^ 2`, that is if
`e < n - √(n * (n - d))`, a Hamming ball of radius `e` contains at most `n * (d - e)` codewords of a
code of length `n` and minimum distance at least `d`, whatever the alphabet. -/
theorem card_filter_hammingDist_le_le {C : Finset (ι → α)} {d e : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α)))
    (h : Fintype.card ι * (Fintype.card ι - d) < (Fintype.card ι - e) ^ 2) (w : ι → α) :
    #{c ∈ C | hammingDist c w ≤ e} ≤ Fintype.card ι * (d - e) :=
  (Nat.le_mul_of_pos_right _ (Nat.sub_pos_of_lt h)).trans
    (card_filter_hammingDist_le_mul_le hd w e)

/-- **List decoding up to the Johnson radius.** Let `enc` be an injective encoding of a finite
nonempty set of messages whose codewords have minimum distance at least `d`. If
`n * (n - d) < (n - e) ^ 2`, some list decoder with lists of `n * (d - e)` messages list decodes
`enc` up to radius `e / n`: it lists the messages whose codewords are within distance `e` of the
received word. -/
theorem exists_listCode_listDecodes {M : Type*} [Finite M] [Nonempty M]
    {enc : M → ι → α} (henc : Function.Injective enc) {d e : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (Set.range enc))
    (h : Fintype.card ι * (Fintype.card ι - d) < (Fintype.card ι - e) ^ 2) :
    ∃ C : ListCode M ι α (Fintype.card ι * (d - e)),
      C.encode = enc ∧ C.ListDecodes (e / Fintype.card ι) := by
  classical
  have := Fintype.ofFinite M
  -- the messages whose codewords are within distance `e`
  let S : (ι → α) → Finset M := fun w => {x | hammingDist (enc x) w ≤ e}
  have hS (w : ι → α) : #(S w) ≤ Fintype.card ι * (d - e) := by
    have hC : (d : ℕ∞) ≤ minDist ((univ.image enc : Finset (ι → α)) : Set (ι → α)) := by
      rwa [coe_image, coe_univ, Set.image_univ]
    calc #(S w) = #{c ∈ univ.image enc | hammingDist c w ≤ e} := by
          rw [filter_image, card_image_of_injective _ henc]
      _ ≤ _ := card_filter_hammingDist_le_le hC h w
  refine ⟨⟨enc, fun w k => (S w).toList.getD k (Classical.arbitrary M)⟩, rfl, fun x w hx => ?_⟩
  have hxe : hammingDist (enc x) w ≤ e := by
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with hn | hn
    · have := hammingDist_le_card_fintype (x := enc x) (y := w)
      omega
    · rw [div_mul_cancel₀ _ (by positivity)] at hx
      exact_mod_cast hx
  have hx : x ∈ (S w).toList := mem_toList.2 (mem_filter.2 ⟨mem_univ x, hxe⟩)
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.1 hx
  refine ⟨⟨i, hi.trans_le ((length_toList _).trans_le (hS w))⟩, ?_⟩
  change (S w).toList.getD i _ = x
  rw [List.getD_eq_getElem _ _ hi, hix]

end Cslib.Code
