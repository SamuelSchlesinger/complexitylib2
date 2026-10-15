/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.AC0
public import Complexity.Computability.Circuit.Boolean.Threshold
import Complexity.Foundations.Data.Fin.Append
import Mathlib.Data.Fintype.Fin

/-!
# Majority is not in AC⁰

Majority reduces to parity in constant depth: padding the input with constants turns majority on
`2 n + 2` bits into every threshold function on `n` bits (`thresholdCircuit`), two thresholds give
"exactly `k` bits are true", and parity is the disjunction of these for odd `k`
(`parityCircuit`). The circuit has depth `4` more and size polynomially larger than the circuit
for majority, so if majority were in AC⁰ then so would be parity, contradicting
`Cslib.Circuits.Boolean.Unbounded.parity_notMem_AC0` [FurstSaxeSipser1984],
[ChandraStockmeyerVishkin1984].

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.parityCircuit`: parity from a circuit for majority.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.majority_notMem_AC0`: majority is not in AC⁰.

## References

* [M. Furst, J. B. Saxe, M. Sipser, *Parity, circuits, and the polynomial-time
  hierarchy*][FurstSaxeSipser1984]
* [A. K. Chandra, L. Stockmeyer, U. Vishkin, *Constant depth reducibility*]
  [ChandraStockmeyerVishkin1984]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Unbounded

open Finset

variable {n : ℕ}

/-- The inputs followed by `a` copies of `true` and then copies of `false`, `n + 2` constants in
all. -/
def padCircuit (n a : ℕ) : Circuit signature n (n + (n + 2)) :=
  (Circuit.id signature n).append
    (Circuit.pi fun j : Fin (n + 2) => constCircuit (decide (j.val < a)))

theorem eval_padCircuit (a : ℕ) (x : BitString n) :
    (padCircuit n a).eval interpretation x = Fin.append x fun j => decide (j.val < a) := by
  rw [padCircuit, Circuit.eval_append, Circuit.eval_pi]
  congr 1
  funext j
  exact eval_constCircuit _ x 0

theorem size_padCircuit (a : ℕ) : (padCircuit n a).size = n + 2 := by
  simp [padCircuit, Circuit.size_pi]

theorem depth_padCircuit_le (a : ℕ) : (padCircuit n a).depth ≤ 1 :=
  (Circuit.depth_append_le _ _).trans
    (max_le (by simp) (Circuit.depth_pi_le _ fun _ => depth_constCircuit_le _))

/-- The threshold function `Th^n_k` for `k ≤ n + 1`, from a circuit `M` for majority on
`n + (n + 2)` bits. -/
def thresholdCircuit (M : Circuit signature (n + (n + 2)) 1) (k : ℕ) : Circuit signature n 1 :=
  M.comp (padCircuit n (n + 1 - k))

variable {M : Circuit signature (n + (n + 2)) 1}

theorem eval_thresholdCircuit (hM : M.Computes interpretation (single (majority (n + (n + 2)))))
    {k : ℕ} (hk : k ≤ n + 1) (x : BitString n) :
    (thresholdCircuit M k).eval interpretation x 0 = threshold n k x := by
  rw [thresholdCircuit, Circuit.eval_comp, hM, eval_padCircuit]
  simp only [single, majority, threshold, Fin.card_filter_append (· = true), decide_eq_true_eq,
    Fin.card_filter_val_lt]
  rw [show (n + (n + 2) + 1) / 2 = n + 1 by omega, decide_eq_decide]
  omega

theorem size_thresholdCircuit (k : ℕ) : (thresholdCircuit M k).size = n + 2 + M.size := by
  simp [thresholdCircuit, size_padCircuit]

theorem depth_thresholdCircuit_le (k : ℕ) : (thresholdCircuit M k).depth ≤ M.depth + 1 :=
  (Circuit.depth_comp_le _ _).trans (Nat.add_le_add_left (depth_padCircuit_le _) _)

/-- Whether exactly `k` of the bits are true, from a circuit for majority. -/
def exactlyCircuit (M : Circuit signature (n + (n + 2)) 1) (k : ℕ) : Circuit signature n 1 :=
  binCircuit (.and 2) rfl (thresholdCircuit M k) (notCircuit (thresholdCircuit M (k + 1)))

theorem eval_exactlyCircuit (hM : M.Computes interpretation (single (majority (n + (n + 2)))))
    {k : ℕ} (hk : k ≤ n) (x : BitString n) :
    (exactlyCircuit M k).eval interpretation x 0 = decide (#{i | x i = true} = k) := by
  rw [exactlyCircuit, eval_binCircuit_and, eval_notCircuit, eval_thresholdCircuit hM (by omega),
    eval_thresholdCircuit hM (by omega)]
  simp only [threshold]
  by_cases h : #{i | x i = true} = k
  · simp [h]
  · rcases Nat.lt_or_gt_of_ne h with h' | h'
    · simp [h, show ¬ k ≤ #{i | x i = true} by omega]
    · simp [h, show k ≤ #{i | x i = true} by omega, show k + 1 ≤ #{i | x i = true} by omega]

theorem size_exactlyCircuit (k : ℕ) : (exactlyCircuit M k).size = 2 * (n + 2 + M.size) + 2 := by
  rw [exactlyCircuit, size_binCircuit, size_notCircuit, size_thresholdCircuit,
    size_thresholdCircuit]
  ring

theorem depth_exactlyCircuit_le (k : ℕ) : (exactlyCircuit M k).depth ≤ M.depth + 3 :=
  (depth_binCircuit_le _ _ _ _).trans (by
    have := depth_thresholdCircuit_le (M := M) k
    have := (depth_notCircuit_le _).trans
      (Nat.add_le_add_right (depth_thresholdCircuit_le (M := M) (k + 1)) 1)
    omega)

/-- **Parity from majority**: the disjunction, over odd `k ≤ n`, of "exactly `k` bits are true". -/
def parityCircuit (M : Circuit signature (n + (n + 2)) 1) : Circuit signature n 1 :=
  (Circuit.oneGate (Op.or (n + 1) : signature.Op) id).comp
    (Circuit.pi fun k : Fin (n + 1) =>
      if k.val % 2 = 1 then exactlyCircuit M k else constCircuit false)

theorem computes_parityCircuit
    (hM : M.Computes interpretation (single (majority (n + (n + 2))))) :
    (parityCircuit M).Computes interpretation (single (parity n)) := by
  intro x
  funext j
  rw [parityCircuit, Circuit.eval_comp, Circuit.eval_oneGate, Circuit.eval_pi]
  simp only [single, interpretation_or, id]
  set c := #{i | x i = true}
  have hc : c ≤ n := (card_filter_le _ _).trans (by simp)
  rw [parity, parityOn, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨k, hk⟩
    split_ifs at hk with hodd
    · rw [eval_exactlyCircuit hM (by omega)] at hk
      simpa [c, ← of_decide_eq_true hk] using hodd
    · simp at hk
  · intro hodd
    refine ⟨⟨c, by omega⟩, ?_⟩
    simp only [show c % 2 = 1 from by simpa [c] using hodd, ↓reduceIte]
    rw [eval_exactlyCircuit hM hc]
    simp [c]

theorem size_parityCircuit_le :
    (parityCircuit M).size ≤ 1 + (n + 1) * (2 * (n + 2 + M.size) + 2) := by
  rw [parityCircuit, Circuit.size_comp, Circuit.size_pi, Circuit.size_oneGate, add_comm]
  refine Nat.add_le_add_left ((Finset.sum_le_card_nsmul univ _ (2 * (n + 2 + M.size) + 2)
    fun k _ => ?_).trans_eq (by rw [card_univ, Fintype.card_fin, smul_eq_mul])) _
  split_ifs
  · exact (size_exactlyCircuit _).le
  · rw [size_constCircuit]
    omega

theorem depth_parityCircuit_le : (parityCircuit M).depth ≤ M.depth + 4 :=
  (Circuit.depth_comp_le _ _).trans (by
    have := Circuit.depth_pi_le (fun k : Fin (n + 1) =>
      if k.val % 2 = 1 then exactlyCircuit M k else constCircuit false) (D := M.depth + 3)
      fun k => by
        split_ifs
        · exact depth_exactlyCircuit_le _
        · exact (depth_constCircuit_le _).trans (by omega)
    have := Circuit.depth_oneGate_le (σ := signature) (n := n + 1) (Op.or (n + 1)) id
    omega)

/-- **Majority is not in AC⁰.** -/
theorem majority_notMem_AC0 : Language.ofSlices majority ∉ AC0 := by
  rintro ⟨d, size, hsize, hC⟩
  refine parity_notMem_AC0 ⟨d + 4, fun n => 1 + (n + 1) * (2 * (n + 2 + size (n + (n + 2))) + 2),
    by fun_prop, fun n => ?_⟩
  obtain ⟨M, hM, hMd, hMs⟩ := hC (n + (n + 2))
  rw [Language.slice_ofSlices] at hM
  refine ⟨parityCircuit M, ?_, depth_parityCircuit_le.trans (by omega),
    size_parityCircuit_le.trans ?_⟩
  · rw [Language.slice_ofSlices]
    exact computes_parityCircuit hM
  · beta_reduce
    gcongr

end Cslib.Circuits.Boolean.Unbounded
