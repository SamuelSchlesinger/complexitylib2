/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# Fixed-length radix arithmetic

These lemmas use Mathlib's `Nat.ofDigits` and `finFunctionFinEquiv` to relate fixed tuples
of digits, exact carry equations, and ordinary natural-number values. No modular overflow is
implicit in a carry equation.

## Main results

* `Nat.ofDigits_ofFn_eq_sum`: fixed tuples have the usual weighted value.
* `Nat.exists_ofDigits_ofFn`: every value below the fixed capacity has bounded digits.
* `Nat.radix_carry_split`: one exact low-digit equation and its remaining carry.

## References

The application to full-tuple numeric predicates follows [Immerman1999], Exercise 1.33(3).
-/

@[expose] public section

namespace Nat

theorem ofDigits_ofFn_succ {d : ℕ} (B : ℕ) (x : Fin (d + 1) → ℕ) :
    ofDigits B (List.ofFn x) = x 0 + B * ofDigits B (List.ofFn (fun i => x i.succ)) := by
  rw [List.ofFn_succ, ofDigits_cons]

theorem ofDigits_ofFn_eq_sum {d : ℕ} (B : ℕ) (x : Fin d → ℕ) :
    ofDigits B (List.ofFn x) = ∑ i, x i * B ^ i.val := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [ofDigits_ofFn_succ, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem ofDigits_ofFn_lt {B d : ℕ} (hB : 1 < B) (x : Fin d → ℕ)
    (hx : ∀ i, x i < B) : ofDigits B (List.ofFn x) < B ^ d := by
  simpa only [List.length_ofFn] using ofDigits_lt_base_pow_length hB
    (show ∀ a ∈ List.ofFn x, a < B by simpa using hx)

/-- Fixed-length digits exist for every fitting value, including the empty tuple at zero. -/
theorem exists_ofDigits_ofFn {B d v : ℕ} (hv : v < B ^ d) :
    ∃ x : Fin d → ℕ, (∀ i, x i < B) ∧ ofDigits B (List.ofFn x) = v := by
  let x := finFunctionFinEquiv.symm (⟨v, hv⟩ : Fin (B ^ d))
  refine ⟨fun i => (x i).val, fun i => (x i).isLt, ?_⟩
  rw [ofDigits_ofFn_eq_sum, ← finFunctionFinEquiv_apply]
  exact congrArg Fin.val (finFunctionFinEquiv.apply_symm_apply ⟨v, hv⟩)

theorem ofDigits_ofFn_div_mod {B d : ℕ} (x : Fin d → ℕ) (hx : ∀ i, x i < B)
    (i : Fin d) : ofDigits B (List.ofFn x) / B ^ i.val % B = x i := by
  let y : Fin d → Fin B := fun i => ⟨x i, hx i⟩
  have hv : (finFunctionFinEquiv y).val = ofDigits B (List.ofFn x) := by
    rw [finFunctionFinEquiv_apply, ofDigits_ofFn_eq_sum]
  simpa only [Equiv.symm_apply_apply, hv] using
    (finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv y) i).symm

/-- A zero-ended sequence of exact quotients decodes a word without ignoring high digits. -/
theorem ofDigits_eq_of_quotients {B d : ℕ} (x : Fin d → ℕ) (q : Fin (d + 1) → ℕ)
    (hq : q (Fin.last d) = 0)
    (hs : ∀ i : Fin d, q i.castSucc = x i + B * q i.succ) :
    ofDigits B (List.ofFn x) = q 0 := by
  induction d with
  | zero => simpa using hq.symm
  | succ d ih =>
    rw [ofDigits_ofFn_succ, ih (fun i => x i.succ) (fun i => q i.succ) hq
      (fun i => hs i.succ)]
    exact (hs 0).symm

/-- All suffix quotients of a word are bounded by its whole value. -/
theorem exists_radix_quotients {B d : ℕ} (hB : 1 ≤ B) (x : Fin d → ℕ) :
    ∃ q : Fin (d + 1) → ℕ, q 0 = ofDigits B (List.ofFn x) ∧ q (Fin.last d) = 0 ∧
      (∀ i, q i ≤ ofDigits B (List.ofFn x)) ∧
      ∀ i : Fin d, q i.castSucc = x i + B * q i.succ := by
  induction d with
  | zero => exact ⟨fun _ => 0, rfl, rfl, fun _ => by simp, fun i => i.elim0⟩
  | succ d ih =>
    obtain ⟨q, hq0, hqe, hqb, hqs⟩ := ih (fun i => x i.succ)
    have ht : ofDigits B (List.ofFn (fun i => x i.succ)) ≤ ofDigits B (List.ofFn x) := by
      rw [ofDigits_ofFn_succ]
      nlinarith
    refine ⟨Fin.cons (ofDigits B (List.ofFn x)) q, rfl, ?_, ?_, ?_⟩
    · simpa using hqe
    · intro i
      exact Fin.cases (le_refl _) (fun j => le_trans (hqb j) ht) i
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one,
          Fin.cons_one, hq0] using ofDigits_ofFn_succ B x
      · simpa only [← Fin.succ_castSucc, Fin.cons_succ] using hqs j

/-- A bit of a binary-radix word belongs to exactly one of its fixed chunks. -/
theorem testBit_ofDigits_ofFn {e d : ℕ} (he : 0 < e) (x : Fin d → ℕ)
    (hx : ∀ i, x i < 2 ^ e) (j : ℕ) :
    (ofDigits (2 ^ e) (List.ofFn x)).testBit j = true ↔
      ∃ r : Fin d, ∃ b : Fin e, r.val * e + b.val = j ∧ (x r).testBit b.val = true := by
  let z := ofDigits (2 ^ e) (List.ofFn x)
  have hbit (r : Fin d) (b : Fin e) :
      (x r).testBit b.val = z.testBit (r.val * e + b.val) := by
    rw [← ofDigits_ofFn_div_mod x hx r, Nat.testBit_mod_two_pow,
      decide_eq_true b.isLt, Bool.true_and, ← pow_mul, Nat.testBit_div_two_pow]
    congr 1
    lia
  constructor
  · intro hj
    have hz := ofDigits_ofFn_lt (show 1 < 2 ^ e by
      exact one_lt_pow₀ (by decide) (by lia)) x hx
    rw [← pow_mul] at hz
    have hje : j < d * e := by
      by_contra hn
      have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show e * d ≤ j by lia)
      have hj' : 2 ^ j ≤ z := Nat.ge_two_pow_of_testBit hj
      dsimp [z] at hj'
      lia
    let r : Fin d := ⟨j / e, (Nat.div_lt_iff_lt_mul he).mpr hje⟩
    let b : Fin e := ⟨j % e, Nat.mod_lt _ he⟩
    have hrb : r.val * e + b.val = j := by
      simpa only [r, b, Nat.mul_comm] using Nat.div_add_mod j e
    exact ⟨r, b, hrb, by rw [hbit, hrb]; exact hj⟩
  · rintro ⟨r, b, hrb, hb⟩
    rwa [hbit, hrb] at hb

/-- An exact low-digit equation determines both the carry and the remaining value. -/
theorem radix_carry_split {B t u z v : ℕ} (hB : 0 < B) (hz : z < B)
    (h : t + B * u = z + B * v) :
    t = z + B * (t / B) ∧ u + t / B = v := by
  have hm := congrArg (· % B) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hz] at hm
  have ht : t = z + B * (t / B) := by
    simpa only [hm] using (Nat.mod_add_div t B).symm
  exact ⟨ht, by nlinarith⟩

/-- Bounded, zero-ended carries characterize multiplication by one digit plus another word. -/
theorem radix_affine_carries_iff {B d b c₀ : ℕ} (hB : 1 < B) (hb : b ≤ B)
    (hc₀ : c₀ ≤ B) (x y z : Fin d → ℕ)
    (hx : ∀ i, x i < B) (hy : ∀ i, y i < B) (hz : ∀ i, z i < B) :
    (∃ c : Fin (d + 1) → ℕ, c 0 = c₀ ∧ c (Fin.last d) = 0 ∧
      (∀ i, c i ≤ B) ∧ ∀ i : Fin d,
        x i * b + y i + c i.castSucc = z i + B * c i.succ) ↔
      b * ofDigits B (List.ofFn x) + ofDigits B (List.ofFn y) + c₀ =
        ofDigits B (List.ofFn z) := by
  induction d generalizing c₀ with
  | zero =>
    simp only [List.ofFn_zero, ofDigits_nil, mul_zero, zero_add]
    constructor
    · rintro ⟨c, hc, he, _, _⟩
      exact hc.symm.trans he
    · intro hc
      subst c₀
      exact ⟨fun _ => 0, rfl, rfl, fun _ => by lia, fun i => i.elim0⟩
  | succ d ih =>
    rw [ofDigits_ofFn_succ, ofDigits_ofFn_succ, ofDigits_ofFn_succ]
    constructor
    · rintro ⟨c, hc, he, hcb, hstep⟩
      have ht := (ih (hcb 1) (fun i => x i.succ) (fun i => y i.succ)
        (fun i => z i.succ) (fun i => hx i.succ) (fun i => hy i.succ)
        (fun i => hz i.succ)).mp
        ⟨fun i => c i.succ, rfl, he, fun i => hcb i.succ, fun i => hstep i.succ⟩
      have h0 := hstep 0
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, hc] at h0
      nlinarith [congrArg (B * ·) ht]
    · intro he
      let t := x 0 * b + y 0 + c₀
      have ht : t < B * (B + 1) := by
        have hx0 := hx 0
        have hy0 := hy 0
        have hp := Nat.mul_le_mul (show x 0 ≤ B - 1 by lia) hb
        have hpred : B - 1 + 1 = B := by lia
        dsimp [t]
        nlinarith
      obtain ⟨he0, he1⟩ := radix_carry_split (by lia : 0 < B) (hz 0)
        (show t + B * (b * ofDigits B (List.ofFn (fun i => x i.succ)) +
            ofDigits B (List.ofFn (fun i => y i.succ))) =
            z 0 + B * ofDigits B (List.ofFn (fun i => z i.succ)) by
          dsimp [t]
          nlinarith [he])
      have hc : t / B ≤ B := by
        have := (Nat.div_lt_iff_lt_mul (by lia : 0 < B)).mpr
          (show t < (B + 1) * B by nlinarith)
        lia
      obtain ⟨c, hc0, hce, hcb, hstep⟩ :=
        (ih hc (fun i => x i.succ) (fun i => y i.succ) (fun i => z i.succ)
          (fun i => hx i.succ) (fun i => hy i.succ) (fun i => hz i.succ)).mpr he1
      refine ⟨Fin.cons c₀ c, rfl, ?_, ?_, ?_⟩
      · simpa using hce
      · intro i
        refine Fin.cases hc₀ (fun j => ?_) i
        exact hcb j
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Fin.cons_zero, Fin.castSucc_zero, Fin.succ_zero_eq_one,
            Fin.cons_one, hc0] using he0
        · simpa only [← Fin.succ_castSucc, Fin.cons_succ] using hstep j

/-- A linear number of small digits still fits in the corresponding exponential capacity. -/
theorem mul_pred_lt_pow {B d : ℕ} (hB : 1 < B) : d * (B - 1) < B ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ]
    have hp : 1 ≤ B ^ d := Nat.one_le_pow d B (by lia)
    have hb : B - 1 + 1 = B := by lia
    nlinarith

/-- Every universe larger than eight admits binary digits whose products fit, while its
cardinality itself fits in seven digits. The cardinality need not be a source element. -/
theorem exists_binary_radix {n : ℕ} (hn : 8 < n) :
    ∃ e : ℕ, 0 < e ∧ (2 ^ e) ^ 3 < n ∧ n < (2 ^ e) ^ 7 := by
  let h := Nat.log 2 (n - 1)
  have hh : 3 ≤ h := Nat.le_log_of_pow_le (by decide) (by dsimp; lia)
  have hl : 2 ^ h ≤ n - 1 := Nat.pow_log_le_self 2 (by lia)
  have hu : n - 1 < 2 ^ (h + 1) := Nat.lt_pow_succ_log_self (by decide) _
  let e := h / 3
  have he : 0 < e := by dsimp [e]; lia
  have hr := Nat.mod_lt h (by decide : 0 < 3)
  have hd := Nat.div_add_mod h 3
  have h3 : 2 ^ (e * 3) ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) (by dsimp [e]; lia)
  have h6 : 2 ^ (h + 1) ≤ 2 ^ (e * 6) :=
    Nat.pow_le_pow_right (by decide) (by dsimp [e] at *; lia)
  have h7 : 2 ^ (e * 6) < 2 ^ (e * 7) := Nat.pow_lt_pow_right (by decide) (by lia)
  refine ⟨e, he, ?_, ?_⟩ <;> rw [← pow_mul] <;> lia

end Nat
