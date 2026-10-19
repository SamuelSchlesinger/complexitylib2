/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.InputTime
public import Complexity.Computability.Circuit.Boolean.Iteration.LabelCircuit
public import Complexity.Foundations.Combinatorics.FunctionalGraph.Projection
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Long input times at additive cost

Binary powering iterates for an `m`-bit input time with `m` fixed-power circuits
(`variable_time`). For long times this is wasteful: the state after `T` steps is the state after
a time below `2 * 2 ^ n`, namely `T` itself or `2 ^ n` plus `T - 2 ^ n` modulo the cycle length
(`FunctionalGraph.iterate_normalizedTime`). The cycle length is part of the canonical label, the
reduction streams through the time bits at `O(n)` gates per bit, and only `n + 3` time bits remain
for binary powering (`compressedTime`). This gives a circuit of size at most
`200000 * (n + 1) * powerBudget n s (2 ^ n) L + 80 * m * (n + 1)`, additive in the time width
(`variable_time_additive`), and `600000 * (n + 1) * optimizedBudget n s (2 ^ n) + 80 * m * (n + 1)`
balanced (`variable_time_additive_optimized`). Together with `variable_time_optimized` this gives
the minimum of the two bounds.

The circuits are native De Morgan circuits: every NOT, AND and OR gate and every constant is
charged, while wiring and fanout are free. They exist for each `m` and `L`; nothing here bounds
the time to construct them.

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.compressedTime`: a short time with the same state.

## Main results

* `Cslib.Circuits.Boolean.Iteration.toNat_compressedTime`: it is the normalized time.
* `Cslib.Circuits.Boolean.Iteration.variable_time_additive`,
  `Cslib.Circuits.Boolean.Iteration.variable_time_additive_optimized`: long input times.

## References

* Adapted from `lean/Proofs/LongTime.lean` in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions], whose
  bound is `33000000 * (n + 1) * optimizedBudget n s (2 ^ n) + 200 * m * (n + 1)`.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open FunctionalGraph

variable {n m a : ℕ}

/-- For a time given by `m` bits and a cycle length `ell`, the time itself if it is below
`2 ^ n`, and otherwise `2 ^ n` plus the excess modulo `ell`, in `n + 3` bits. -/
def compressedTime (n : ℕ) (ell : BitVec (n + 3)) (bits : BitString m) : BitVec (n + 3) :=
  if (word bits).ult (BitVec.ofNat m (2 ^ n)) then (word bits).setWidth (n + 3)
  else BitVec.ofNat (n + 3) (2 ^ n) +
    subMod (streamRemainder ell bits) (BitVec.ofNat (n + 3) (2 ^ n)) ell

/-- With the cycle length of `x`, the compressed time is the normalized time. -/
theorem toNat_compressedTime (f : BitString n → BitString n) (x : BitString n)
    (bits : BitString m) (hnm : n < m) :
    (compressedTime n (BitVec.ofNat (n + 3) (cycleLength f x)) bits).toNat =
      normalizedTime f x (word bits).toNat := by
  have h8 : 2 ^ (n + 3) = 8 * 2 ^ n := by rw [pow_add]; ring
  have hNm : 2 ^ n < 2 ^ m := Nat.pow_lt_pow_right (by decide) hnm
  have hl := cycleLength_le_two_pow f x
  have hp := cycleLength_pos f x
  have hell := toNat_ofNat_cycleLength f x
  have hw : 2 * (BitVec.ofNat (n + 3) (cycleLength f x)).toNat ≤ 2 ^ (n + 3) := by omega
  have hr := toNat_streamRemainder _ bits (by omega) hw
  rw [hell] at hr
  have hcard : Fintype.card (BitString n) = 2 ^ n := by simp
  unfold compressedTime normalizedTime
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hNm, decide_eq_true_eq, hcard]
  split_ifs with ht
  · rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  · have hd : (subMod (streamRemainder (BitVec.ofNat (n + 3) (cycleLength f x)) bits)
        (BitVec.ofNat (n + 3) (2 ^ n)) (BitVec.ofNat (n + 3) (cycleLength f x))).toNat =
        ((word bits).toNat - 2 ^ n) % cycleLength f x := by
      rw [toNat_subMod _ _ _ (by omega) hw, hr, hell, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 2 ^ n < 2 ^ (n + 3))]
      apply sub_mod_eq_of_modEq hp (Nat.mod_lt _ hp)
      calc ((word bits).toNat - 2 ^ n) % cycleLength f x + 2 ^ n
          ≡ ((word bits).toNat - 2 ^ n) + 2 ^ n [MOD cycleLength f x] :=
            (Nat.mod_modEq _ _).add_right _
        _ = (word bits).toNat := Nat.sub_add_cancel (by omega)
        _ ≡ (word bits).toNat % cycleLength f x [MOD cycleLength f x] := (Nat.mod_modEq _ _).symm
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 2 ^ n < 2 ^ (n + 3)),
      hd]
    have := Nat.mod_lt ((word bits).toNat - 2 ^ n) hp
    exact Nat.mod_eq_of_lt (by omega)

/-- Compressing an available time with an available cycle length: one streaming remainder over
the time bits, one modular difference, one addition, one comparison and one selection. -/
theorem synthesis_compressedTime (s : Set (BooleanFunction a)) (ell : BitString a → BitVec (n + 3))
    (bits : BitString a → BitString m) (hl : wordWires ell ⊆ s) (hb : ∀ j, (fun x => bits x j) ∈ s)
    (hc : ∀ b : Bool, (fun _ : BitString a => b) ∈ s) :
    Synthesis interpretation s (wordWires fun x => compressedTime n (ell x) (bits x))
      (m * (22 * (n + 3) + 3) + 50 * (n + 4) ^ 2 + 16 * (n + 3) + 1 + (5 * m + 2)) := by
  let rem := fun x => streamRemainder (ell x) (bits x)
  let bound := fun _ : BitString a => BitVec.ofNat (n + 3) (2 ^ n)
  have hrem := synthesis_streamRemainder s ell bits (fun i => hl ⟨i, rfl⟩) hb (hc false)
  let s1 := s ∪ wordWires rem
  let difference := fun x => subMod (rem x) (bound x) (ell x)
  have hdiff := synthesis_subMod s1 rem bound ell (fun i => Or.inr ⟨i, rfl⟩)
    (fun i => Or.inl (hc ((BitVec.ofNat (n + 3) (2 ^ n)).getLsbD i.val)))
    (fun i => Or.inl (hl ⟨i, rfl⟩)) (Or.inl (hc false))
  let s2 := s1 ∪ wordWires difference
  let advance := fun x => bound x + difference x
  have hadd := Synthesis.word_add (s := s2) bound difference
    (fun i => Or.inl (Or.inl (hc ((BitVec.ofNat (n + 3) (2 ^ n)).getLsbD i.val))))
    fun i => Or.inr ⟨i, rfl⟩
  let s3 := s2 ∪ wordWires advance
  have hword (i : Fin m) : (fun x => (word (bits x)).getLsbD i.val) ∈ s3 := by
    rw [show (fun x => (word (bits x)).getLsbD i.val) = fun x => bits x i from
      funext fun x => getLsbD_word _ i]
    exact Or.inl (Or.inl (Or.inl (hb i)))
  let short := fun x => (word (bits x)).ult (BitVec.ofNat m (2 ^ n))
  have hcmp := Synthesis.word_ult (s := s3) (fun x => word (bits x))
    (fun _ => BitVec.ofNat m (2 ^ n)) hword
    fun i => Or.inl (Or.inl (Or.inl (hc ((BitVec.ofNat m (2 ^ n)).getLsbD i.val))))
  let s4 := s3 ∪ {short}
  have hresize := wordWires_setWidth_subset (v := n + 3) (s := s4)
    (value := fun x => word (bits x)) (by rintro _ ⟨i, rfl⟩; exact Or.inl (hword i))
    (Or.inl (Or.inl (Or.inl (Or.inl (hc false)))))
  have hmux := Synthesis.word_mux (s := s4) (fun x => (word (bits x)).setWidth (n + 3)) advance
    short (Or.inr rfl) (fun i => hresize ⟨i, rfl⟩) fun i => Or.inl (Or.inr ⟨i, rfl⟩)
  exact (hrem.trans (hdiff.trans (hadd.trans (hcmp.trans hmux)))).mono Set.Subset.rfl
    Set.Subset.rfl (by rw [show n + 3 + 1 = n + 4 from rfl]; omega)

/-- The gate count of the long-time construction: constants, the label circuit, the time
compression and binary powering over `n + 3` time bits. -/
def longTimeBudget (n s m L : ℕ) : ℕ :=
  2 + 60000 * powerBudget n s (2 ^ n) L +
    (m * (22 * (n + 3) + 3) + 50 * (n + 4) ^ 2 + 16 * (n + 3) + 1 + (5 * m + 2)) +
    (n + 3) * (40000 * powerBudget n s (2 ^ n) L + 4 * n)

theorem long_time_circuit (c : Circuit signature n n) (m L : ℕ) (hnm : n < m) (hL : 0 < L)
    (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature (n + m) n,
      out.Computes interpretation (inputTimeIterate (c.eval interpretation) m) ∧
      out.size ≤ longTimeBudget n c.size m L := by
  let f := c.eval interpretation
  let init := fun z : BitString (n + m) => fun i : Fin n => z (Fin.castAdd m i)
  let bits := fun z : BitString (n + m) => fun j : Fin m => z (Fin.natAdd n j)
  let constants : Set (BooleanFunction (n + m)) := {fun _ => false, fun _ => true}
  have hconst : Synthesis interpretation (inputs (n + m)) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  let s0 := inputs (n + m) ∪ constants
  have hc (b : Bool) : (fun _ : BitString (n + m) => b) ∈ s0 := by
    cases b <;> simp [s0, constants]
  obtain ⟨labels, hl, hls⟩ := cycle_label_circuit c L hL hLN
  have hlabels : Synthesis interpretation s0 (wires fun z => canonicalLabel f (init z))
      labels.size := by
    refine (Synthesis.circuit (I := interpretation) (s := s0) labels (fun i z => init z i)
      fun i => Or.inl ⟨_, rfl⟩).mono Set.Subset.rfl ?_ le_rfl
    rintro _ ⟨bit, rfl⟩
    exact ⟨bit, funext fun z => by
      change labels.eval interpretation (init z) bit = _
      rw [hl]⟩
  let s1 := s0 ∪ wires fun z => canonicalLabel f (init z)
  let ell := fun z => labelLength (canonicalLabel f (init z))
  have hlength : wordWires ell ⊆ s1 := by
    rintro _ ⟨i, rfl⟩
    simp only [ell, labelLength, getLsbD_word]
    exact Or.inr ⟨_, rfl⟩
  have htime := synthesis_compressedTime s1 ell bits hlength (fun j => Or.inl (Or.inl ⟨_, rfl⟩))
    fun b => Or.inl (hc b)
  let time := fun z => compressedTime n (ell z) (bits z)
  let s2 := s1 ∪ wordWires time
  have hpower := synthesis_binary_powering (m := n + 3) f _
    (fun j _ => fixed_power n c (2 ^ j) L hL hLN) s2 init (fun z i => (time z).getLsbD i.val)
    (by rintro _ ⟨i, rfl⟩; exact Or.inl (Or.inl (Or.inl ⟨_, rfl⟩)))
    (by rintro _ ⟨i, rfl⟩; exact Or.inr ⟨i, rfl⟩)
  obtain ⟨out, ho, hs⟩ :=
    (hconst.trans (hlabels.trans (htime.trans hpower))).exists_circuit_outputs
  refine ⟨out, fun z => ?_, hs.trans ?_⟩
  · rw [ho z]
    change f^[(word fun i : Fin (n + 3) => (time z).getLsbD i.val).toNat] (init z) =
      f^[(word (bits z)).toNat] (init z)
    rw [word_getLsbD]
    simp only [time, ell, canonicalLabel, labelLength_labelBits]
    rw [toNat_compressedTime f _ _ hnm, iterate_normalizedTime]
  · unfold longTimeBudget
    omega

theorem longTimeBudget_le (n s m L : ℕ) :
    longTimeBudget n s m L ≤
      200000 * (n + 1) * powerBudget n s (2 ^ n) L + 80 * m * (n + 1) := by
  set B := powerBudget n s (2 ^ n) L
  have hb : (n + 1) ^ 3 ≤ B := by
    have h := Nat.mul_le_mul_left ((n + 1) ^ 3) (Nat.le_add_left 1 (L + 2 ^ n / L))
    simp only [B, powerBudget]
    nlinarith
  have hfour : (n + 4) ^ 2 ≤ 16 * (n + 1) ^ 2 := by
    have := Nat.pow_le_pow_left (show n + 4 ≤ 4 * (n + 1) by omega) 2
    nlinarith
  have hpoly : 2 + 50 * (n + 4) ^ 2 + 16 * (n + 3) + 1 + 2 + (n + 3) * (4 * n) ≤ 1000 * B := by
    nlinarith [Nat.zero_le (n ^ 3)]
  have htime : m * (22 * (n + 3) + 3) + 5 * m ≤ 80 * m * (n + 1) := by nlinarith
  have hcost : 60000 * B + (n + 3) * (40000 * B) + 1000 * B ≤ 200000 * (n + 1) * B := by
    nlinarith
  unfold longTimeBudget
  nlinarith

/-- **Long input times.** For every `0 < L ≤ 2 ^ n`, some circuit of size at most
`200000 * (n + 1) * powerBudget n c.size (2 ^ n) L + 80 * m * (n + 1)` iterates `c` for a number
of steps given by `m` input bits. The cost of the time bits is additive. -/
theorem variable_time_additive (c : Circuit signature n n) (m L : ℕ) (hL : 0 < L)
    (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature (n + m) n,
      out.Computes interpretation (inputTimeIterate (c.eval interpretation) m) ∧
      out.size ≤ 200000 * (n + 1) * powerBudget n c.size (2 ^ n) L + 80 * m * (n + 1) := by
  by_cases hnm : n < m
  · obtain ⟨out, ho, hs⟩ := long_time_circuit c m L hnm hL hLN
    exact ⟨out, ho, hs.trans (longTimeBudget_le n c.size m L)⟩
  · obtain ⟨out, ho, hs⟩ := variable_time c m L hL hLN
    refine ⟨out, ho, hs.trans ?_⟩
    set B := powerBudget n c.size (2 ^ n) L
    have hb : (n + 1) ^ 3 ≤ B := by
      have h := Nat.mul_le_mul_left ((n + 1) ^ 3) (Nat.le_add_left 1 (L + 2 ^ n / L))
      simp only [B, powerBudget]
      nlinarith
    have hm : m ≤ n := by omega
    have h1 := Nat.mul_le_mul_right (40000 * B) hm
    have h2 : m * (4 * n) ≤ B := by
      have := Nat.mul_le_mul_right (4 * n) hm
      nlinarith
    nlinarith

/-- **Square-root long input times.** Some circuit of size at most
`600000 * (n + 1) * optimizedBudget n c.size (2 ^ n) + 80 * m * (n + 1)` iterates `c` for a
number of steps given by `m` input bits. -/
theorem variable_time_additive_optimized (c : Circuit signature n n) (m : ℕ) :
    ∃ out : Circuit signature (n + m) n,
      out.Computes interpretation (inputTimeIterate (c.eval interpretation) m) ∧
      (out.size : ℝ) ≤ 600000 * (n + 1) * optimizedBudget n c.size (2 ^ n) + 80 * m * (n + 1) := by
  obtain ⟨L, hL, hLN, hopt⟩ := exists_powerBudget_le_optimizedBudget n c.size (2 ^ n) le_rfl
  obtain ⟨out, ho, hs⟩ := variable_time_additive c m L hL hLN
  refine ⟨out, ho, ?_⟩
  have hs' : (out.size : ℝ) ≤
      200000 * (n + 1) * (powerBudget n c.size (2 ^ n) L : ℝ) + 80 * m * (n + 1) := by
    exact_mod_cast hs
  have h := mul_le_mul_of_nonneg_left hopt (show 0 ≤ 200000 * (n + 1 : ℝ) by positivity)
  nlinarith

end Cslib.Circuits.Boolean.Iteration
