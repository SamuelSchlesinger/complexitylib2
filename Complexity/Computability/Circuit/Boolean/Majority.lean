/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.AC0
public import Complexity.Computability.Circuit.Boolean.Threshold
public import Complexity.Computability.Circuit.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Fin

/-!
# Majority is not in AC⁰

Majority reduces to parity in constant depth: padding the input with constants turns majority on
`2 n + 2` bits into every threshold function on `n` bits (`thresholdCircuit`), two thresholds give
"exactly `k` bits are true", and parity is the disjunction of these for odd `k`
(`parityCircuit`). The circuit has depth `4` more and size polynomially larger than the circuit
for majority, so if majority were in AC⁰ then so would be parity, contradicting
`Cslib.Circuits.Boolean.Unbounded.parity_notMem_AC0` [FurstSaxeSipser1984].

## Main definitions

* `Cslib.Circuits.Boolean.majority`: the majority function.
* `Cslib.Circuits.Boolean.Unbounded.parityCircuit`: parity from a circuit for majority.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.majority_notMem_AC0`: majority is not in AC⁰.

## References

* [M. Furst, J. B. Saxe, M. Sipser, *Parity, circuits, and the polynomial-time
  hierarchy*][FurstSaxeSipser1984]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

/-- The majority function on `m` bits: whether at least half of them are true. -/
def majority (m : ℕ) : BooleanFunction m :=
  threshold m ((m + 1) / 2)

namespace Unbounded

open Finset

variable {n : ℕ}

/-- The number of true bits of two words side by side. -/
private theorem card_true_append {m p : ℕ} (x : Fin m → Bool) (y : Fin p → Bool) :
    #{i | Fin.append x y i = true} = #{i | x i = true} + #{j | y j = true} := by
  simp only [card_filter]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- The constant `b`, as a circuit of one gate. -/
def constCircuit : Bool → Circuit signature n 1
  | true => Circuit.oneGate (Op.and 0 : signature.Op) Fin.elim0
  | false => Circuit.oneGate (Op.or 0 : signature.Op) Fin.elim0

@[simp] theorem eval_constCircuit (b : Bool) (x : BitString n) (j : Fin 1) :
    (constCircuit b).eval interpretation x j = b := by
  cases b
  · simp [constCircuit]
  · simp [constCircuit]

@[simp] theorem size_constCircuit (b : Bool) : (constCircuit (n := n) b).size = 1 := by
  cases b <;> rfl

theorem depth_constCircuit_le (b : Bool) : (constCircuit (n := n) b).depth ≤ 1 := by
  cases b <;> exact Circuit.depth_oneGate_le _ _

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
  simp only [single, majority, threshold, card_true_append, Fin.card_filter_val_lt,
    decide_eq_true_eq]
  rw [show (n + (n + 2) + 1) / 2 = n + 1 by omega, decide_eq_decide]
  omega

theorem size_thresholdCircuit (k : ℕ) : (thresholdCircuit M k).size = n + 2 + M.size := by
  simp [thresholdCircuit, size_padCircuit]

theorem depth_thresholdCircuit_le (k : ℕ) : (thresholdCircuit M k).depth ≤ M.depth + 1 :=
  (Circuit.depth_comp_le _ _).trans (Nat.add_le_add_left (depth_padCircuit_le _) _)

/-- The two circuits under `andNotCircuit`: `x 0`, through a conjunction of one argument, and
`¬ x 1`. -/
def andNotArgs (j : Fin 2) : Circuit signature 2 1 :=
  Fin.cases (Circuit.oneGate (σ := signature) (Op.and 1) fun _ => 0)
    (fun _ => Circuit.oneGate (σ := signature) Op.not fun _ => 1) j

/-- The circuit of `x 0 ∧ ¬ x 1`. -/
def andNotCircuit : Circuit signature 2 1 :=
  (Circuit.oneGate (σ := signature) (Op.and 2) fun j => j).comp (Circuit.pi andNotArgs)

theorem eval_andNotCircuit (x : Fin 2 → Bool) :
    andNotCircuit.eval interpretation x 0 = (x 0 && !x 1) := by
  have h₀ : (andNotArgs 0).eval interpretation x 0 = x 0 := by
    change decide (∀ _ : Fin 1, x 0 = true) = x 0
    cases x 0 <;> decide
  have h₁ : (andNotArgs 1).eval interpretation x 0 = !x 1 := rfl
  rw [andNotCircuit, Circuit.eval_comp, Circuit.eval_oneGate, Circuit.eval_pi]
  change decide (∀ j : Fin 2, (andNotArgs j).eval interpretation x 0 = true) = _
  simp only [Fin.forall_fin_two, h₀, h₁]
  cases x 0 <;> cases x 1 <;> decide

theorem size_andNotCircuit : andNotCircuit.size = 3 := by
  rw [andNotCircuit, Circuit.size_comp, Circuit.size_pi, Fin.sum_univ_two]
  rfl

theorem depth_andNotCircuit_le : andNotCircuit.depth ≤ 2 := by
  have h₁ := Circuit.depth_oneGate_le (σ := signature) (n := 2) (Op.and 2) fun j => j
  have h₂ : (Circuit.pi andNotArgs).depth ≤ 1 := Circuit.depth_pi_le _ fun j => by
    refine Fin.cases ?_ (fun _ => ?_) j <;> exact Circuit.depth_oneGate_le _ _
  exact (Circuit.depth_comp_le _ _).trans (by omega)

/-- Whether exactly `k` of the bits are true, from a circuit for majority. -/
def exactlyCircuit (M : Circuit signature (n + (n + 2)) 1) (k : ℕ) : Circuit signature n 1 :=
  andNotCircuit.comp ((thresholdCircuit M k).append (thresholdCircuit M (k + 1)))

theorem eval_exactlyCircuit (hM : M.Computes interpretation (single (majority (n + (n + 2)))))
    {k : ℕ} (hk : k ≤ n) (x : BitString n) :
    (exactlyCircuit M k).eval interpretation x 0 = decide (#{i | x i = true} = k) := by
  rw [exactlyCircuit, Circuit.eval_comp, Circuit.eval_append, eval_andNotCircuit]
  rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl, Fin.append_left,
    show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl, Fin.append_right,
    eval_thresholdCircuit hM (by omega), eval_thresholdCircuit hM (by omega)]
  simp only [threshold]
  by_cases h : #{i | x i = true} = k
  · simp [h]
  · rcases Nat.lt_or_gt_of_ne h with h' | h'
    · simp [h, show ¬ k ≤ #{i | x i = true} by omega]
    · simp [h, show k ≤ #{i | x i = true} by omega, show k + 1 ≤ #{i | x i = true} by omega]

theorem size_exactlyCircuit (k : ℕ) : (exactlyCircuit M k).size = 2 * (n + 2 + M.size) + 3 := by
  simp [exactlyCircuit, size_thresholdCircuit, size_andNotCircuit]
  ring

theorem depth_exactlyCircuit_le (k : ℕ) : (exactlyCircuit M k).depth ≤ M.depth + 3 :=
  (Circuit.depth_comp_le _ _).trans (by
    have := (Circuit.depth_append_le (thresholdCircuit M k) (thresholdCircuit M (k + 1))).trans
      (max_le (depth_thresholdCircuit_le k) (depth_thresholdCircuit_le (k + 1)))
    have := depth_andNotCircuit_le
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
    (parityCircuit M).size ≤ 1 + (n + 1) * (2 * (n + 2 + M.size) + 3) := by
  rw [parityCircuit, Circuit.size_comp, Circuit.size_pi, Circuit.size_oneGate, add_comm]
  refine Nat.add_le_add_left ((Finset.sum_le_card_nsmul univ _ (2 * (n + 2 + M.size) + 3)
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
  refine parity_notMem_AC0 ⟨d + 4, fun n => 1 + (n + 1) * (2 * (n + 2 + size (n + (n + 2))) + 3),
    by fun_prop, fun n => ?_⟩
  obtain ⟨M, hM, hMd, hMs⟩ := hC (n + (n + 2))
  rw [Language.slice_ofSlices] at hM
  refine ⟨parityCircuit M, ?_, depth_parityCircuit_le.trans (by omega),
    size_parityCircuit_le.trans ?_⟩
  · rw [Language.slice_ofSlices]
    exact computes_parityCircuit hM
  · beta_reduce
    gcongr

end Unbounded

end Cslib.Circuits.Boolean
