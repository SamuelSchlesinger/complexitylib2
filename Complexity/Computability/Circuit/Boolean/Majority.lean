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
# Parity reduces to majority in constant depth

Padding the input with constants turns majority on `2 n + 2` bits into every threshold function on
`n` bits (`thresholdCircuit`), two thresholds give "exactly `k` bits are true"
(`exactlyCircuit`), and parity is the disjunction of these for odd `k` (`parityCircuit`)
[ChandraStockmeyerVishkin1984]. The circuit for parity has depth `4` more and size polynomially
larger than the circuit for majority, and besides the majority circuit it uses only gates of the
unbounded fan-in basis. So over every basis containing that basis, if majority has polynomial-size
constant-depth circuits then so does parity (`parity_mem_of_majority_mem`). Over the unbounded
fan-in basis itself this contradicts `Cslib.Circuits.Boolean.Unbounded.parity_notMem_AC0`:
**majority is not in AC⁰** [FurstSaxeSipser1984].

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.parityCircuit`: parity from a circuit for majority.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.parity_mem_of_majority_mem`: over a basis containing the
  unbounded fan-in basis, parity has polynomial-size constant-depth circuits if majority does.
* `Cslib.Circuits.Boolean.Unbounded.majority_notMem_AC0`: majority is not in AC⁰.

## References

* [A. K. Chandra, L. Stockmeyer, U. Vishkin, *Constant depth reducibility*]
  [ChandraStockmeyerVishkin1984]
* [M. Furst, J. B. Saxe, M. Sipser, *Parity, circuits, and the polynomial-time
  hierarchy*][FurstSaxeSipser1984]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Unbounded

open Finset

variable {n : ℕ}

/-! ### Gadgets over the unbounded fan-in basis -/

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
  simp [padCircuit]

theorem depth_padCircuit_le (a : ℕ) : (padCircuit n a).depth ≤ 1 :=
  (Circuit.depth_append_le _ _).trans
    (max_le (by simp) (Circuit.depth_pi_le _ fun _ => depth_constCircuit_le _))

/-- The circuit of `x 0 ∧ ¬ x 1`. -/
def andNotCircuit : Circuit signature 2 1 :=
  binCircuit (.and 2) rfl (Circuit.wiring signature fun _ => 0)
    (notCircuit (Circuit.wiring signature fun _ => 1))

theorem eval_andNotCircuit (x : Fin 2 → Bool) (j : Fin 1) :
    andNotCircuit.eval interpretation x j = (x 0 && !x 1) := by
  simp [andNotCircuit]

@[simp] theorem size_andNotCircuit : andNotCircuit.size = 2 :=
  rfl

theorem depth_andNotCircuit_le : andNotCircuit.depth ≤ 2 :=
  (depth_binCircuit_le _ _ _ _).trans (by
    have := depth_notCircuit_le (Circuit.wiring signature fun (_ : Fin 1) => (1 : Fin 2))
    simp only [Circuit.depth_wiring] at this ⊢
    omega)

/-! ### Over a basis containing the unbounded fan-in basis -/

variable {σ : Signature} {I : Interpretation σ Bool} (φ : signature.Hom σ)

/-- The threshold function `Th^n_k` for `k ≤ n + 1`, from a circuit `M` for majority on
`n + (n + 2)` bits. -/
def thresholdCircuit (M : Circuit σ (n + (n + 2)) 1) (k : ℕ) : Circuit σ n 1 :=
  M.comp ((padCircuit n (n + 1 - k)).mapOp φ)

/-- Whether exactly `k` of the bits are true, from a circuit for majority. -/
def exactlyCircuit (M : Circuit σ (n + (n + 2)) 1) (k : ℕ) : Circuit σ n 1 :=
  (andNotCircuit.mapOp φ).comp ((thresholdCircuit φ M k).append (thresholdCircuit φ M (k + 1)))

/-- **Parity from majority**: the disjunction, over odd `k ≤ n`, of "exactly `k` bits are true". -/
def parityCircuit (M : Circuit σ (n + (n + 2)) 1) : Circuit σ n 1 :=
  ((Circuit.oneGate (Op.or (n + 1) : signature.Op) id).mapOp φ).comp
    (Circuit.pi fun k : Fin (n + 1) =>
      if k.val % 2 = 1 then exactlyCircuit φ M k else (constCircuit false).mapOp φ)

variable {φ} {M : Circuit σ (n + (n + 2)) 1}

section Eval

variable (hφ : φ.Preserves interpretation I)
  (hM : M.Computes I (single (majority (n + (n + 2)))))
include hφ hM

theorem eval_thresholdCircuit {k : ℕ} (hk : k ≤ n + 1) (x : BitString n) :
    (thresholdCircuit φ M k).eval I x 0 = threshold n k x := by
  rw [thresholdCircuit, Circuit.eval_comp, hM, Circuit.eval_mapOp hφ, eval_padCircuit]
  simp only [single, majority, threshold, Fin.card_filter_append (· = true), decide_eq_true_eq,
    Fin.card_filter_val_lt]
  rw [show (n + (n + 2) + 1) / 2 = n + 1 by omega, decide_eq_decide]
  omega

theorem eval_exactlyCircuit {k : ℕ} (hk : k ≤ n) (x : BitString n) :
    (exactlyCircuit φ M k).eval I x 0 = decide (#{i | x i = true} = k) := by
  rw [exactlyCircuit, Circuit.eval_comp, Circuit.eval_mapOp hφ, eval_andNotCircuit,
    Circuit.eval_append, show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl, Fin.append_left,
    show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl, Fin.append_right,
    eval_thresholdCircuit hφ hM (by omega), eval_thresholdCircuit hφ hM (by omega)]
  simp only [threshold]
  by_cases h : #{i | x i = true} = k
  · simp [h]
  · rcases Nat.lt_or_gt_of_ne h with h' | h'
    · simp [h, show ¬ k ≤ #{i | x i = true} by omega]
    · simp [h, show k ≤ #{i | x i = true} by omega, show k + 1 ≤ #{i | x i = true} by omega]

theorem computes_parityCircuit : (parityCircuit φ M).Computes I (single (parity n)) := by
  intro x
  funext j
  rw [parityCircuit, Circuit.eval_comp, Circuit.eval_mapOp hφ, Circuit.eval_oneGate,
    Circuit.eval_pi]
  simp only [single, interpretation_or, id]
  set c := #{i | x i = true}
  have hc : c ≤ n := (card_filter_le _ _).trans (by simp)
  rw [parity, parityOn, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨k, hk⟩
    split_ifs at hk with hodd
    · rw [eval_exactlyCircuit hφ hM (by omega)] at hk
      simpa [c, ← of_decide_eq_true hk] using hodd
    · simp [Circuit.eval_mapOp hφ] at hk
  · intro hodd
    refine ⟨⟨c, by omega⟩, ?_⟩
    simp only [show c % 2 = 1 from by simpa [c] using hodd, ↓reduceIte]
    rw [eval_exactlyCircuit hφ hM hc]
    simp [c]

end Eval

theorem size_thresholdCircuit (k : ℕ) : (thresholdCircuit φ M k).size = n + 2 + M.size := by
  rw [thresholdCircuit, Circuit.size_comp, Circuit.size_mapOp, size_padCircuit]

theorem depth_thresholdCircuit_le (k : ℕ) : (thresholdCircuit φ M k).depth ≤ M.depth + 1 :=
  (Circuit.depth_comp_le _ _).trans
    (Nat.add_le_add_left ((Circuit.depth_mapOp _).trans_le (depth_padCircuit_le _)) _)

theorem size_exactlyCircuit (k : ℕ) :
    (exactlyCircuit φ M k).size = 2 * (n + 2 + M.size) + 2 := by
  rw [exactlyCircuit, Circuit.size_comp, Circuit.size_append, Circuit.size_mapOp,
    size_thresholdCircuit, size_thresholdCircuit, size_andNotCircuit]
  ring

theorem depth_exactlyCircuit_le (k : ℕ) : (exactlyCircuit φ M k).depth ≤ M.depth + 3 :=
  (Circuit.depth_comp_le _ _).trans (by
    have := (Circuit.depth_append_le (thresholdCircuit φ M k) (thresholdCircuit φ M (k + 1))).trans
      (max_le (depth_thresholdCircuit_le k) (depth_thresholdCircuit_le (k + 1)))
    have := (Circuit.depth_mapOp (φ := φ) andNotCircuit).trans_le depth_andNotCircuit_le
    omega)

theorem size_parityCircuit_le :
    (parityCircuit φ M).size ≤ 1 + (n + 1) * (2 * (n + 2 + M.size) + 2) := by
  rw [parityCircuit, Circuit.size_comp, Circuit.size_pi, Circuit.size_mapOp, Circuit.size_oneGate,
    add_comm]
  refine Nat.add_le_add_left ((Finset.sum_le_card_nsmul univ _ (2 * (n + 2 + M.size) + 2)
    fun k _ => ?_).trans_eq (by rw [card_univ, Fintype.card_fin, smul_eq_mul])) _
  split_ifs
  · exact (size_exactlyCircuit _).le
  · rw [Circuit.size_mapOp, size_constCircuit]
    omega

theorem depth_parityCircuit_le : (parityCircuit φ M).depth ≤ M.depth + 4 :=
  (Circuit.depth_comp_le _ _).trans (by
    have := Circuit.depth_pi_le (fun k : Fin (n + 1) =>
      if k.val % 2 = 1 then exactlyCircuit φ M k else (constCircuit false).mapOp φ)
      (D := M.depth + 3) fun k => by
        split_ifs
        · exact depth_exactlyCircuit_le _
        · exact ((Circuit.depth_mapOp _).trans_le (depth_constCircuit_le _)).trans (by omega)
    rw [Circuit.depth_mapOp, Circuit.depth_oneGate]
    omega)

/-- **Parity reduces to majority**: over a basis containing the unbounded fan-in basis, parity has
polynomial-size constant-depth circuits if majority does. -/
theorem parity_mem_of_majority_mem (hφ : φ.Preserves interpretation I)
    (h : Language.ofSlices majority ∈ ConstDepth I) : Language.ofSlices parity ∈ ConstDepth I := by
  obtain ⟨d, size, hsize, hC⟩ := h
  refine ⟨d + 4, fun n => 1 + (n + 1) * (2 * (n + 2 + size (n + (n + 2))) + 2), by fun_prop,
    fun n => ?_⟩
  obtain ⟨M, hM, hMd, hMs⟩ := hC (n + (n + 2))
  rw [Language.slice_ofSlices] at hM
  refine ⟨parityCircuit φ M, ?_, depth_parityCircuit_le.trans (by omega),
    size_parityCircuit_le.trans ?_⟩
  · rw [Language.slice_ofSlices]
    exact computes_parityCircuit hφ hM
  · beta_reduce
    gcongr

/-- **Majority is not in AC⁰.** -/
theorem majority_notMem_AC0 : Language.ofSlices majority ∉ AC0 :=
  fun h => parity_notMem_AC0 (parity_mem_of_majority_mem (Signature.Hom.preserves_id _) h)

end Cslib.Circuits.Boolean.Unbounded
