/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.ModGates
public import Complexity.Foundations.Data.BitString.LowDegree
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Smolensky's gate approximators

Over `ZMod p` for a prime `p`, every gate of the AC⁰[p] basis has a polynomial approximator that
multiplies degrees by at most `(p - 1) ℓ`:

* `MOD_p` of `u₁, …, u_m` is exactly `(∑ uᵢ) ^ (p - 1)`, since nonzero elements of `ZMod p` have
  `(p - 1)`-st power `1` (`modApprox`);
* OR of `u₁, …, u_m` is approximated by `1 - ∏_{j < ℓ} (1 - (∑_{i ∈ T j} uᵢ) ^ (p - 1))` for a tuple
  `T` of `ℓ` sets of arguments (`orApprox`), and AND is its De Morgan dual;
* negation is exactly `1 - u`.

For a nonzero Boolean vector, adding or removing a true coordinate changes the count of a set by
one, so at most half of the sets have a count divisible by `p`, and at most a `2 ^ (-ℓ)` fraction of
the tuples err (`card_orApprox_wrong_mul_le`). Double counting over the inputs gives, for every
gate and every way its arguments depend on the input, an approximator that errs on at most
`2 ^ n / 2 ^ ℓ` inputs (`exists_gate_approx`) [Razborov1987], [Smolensky1987].

## Main results

* `Cslib.Circuits.Boolean.Smolensky.exists_gate_approx`: the gate approximators.

## References

* [A. A. Razborov, *Lower bounds on the size of bounded depth circuits over a complete basis with
  logical addition*][Razborov1987]
* [R. Smolensky, *Algebraic methods in the theory of lower bounds for Boolean circuit
  complexity*][Smolensky1987]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Smolensky

open Finset BitString

variable {p : ℕ} [Fact p.Prime] {n m ℓ : ℕ}

/-- The OR approximator for a tuple `T` of `ℓ` sets of arguments. -/
def orApprox (T : Fin ℓ → Finset (Fin m)) (u : Fin m → ZMod p) : ZMod p :=
  1 - ∏ j, (1 - (∑ i ∈ T j, u i) ^ (p - 1))

/-- The AND approximator, the De Morgan dual of `orApprox`. -/
def andApprox (T : Fin ℓ → Finset (Fin m)) (u : Fin m → ZMod p) : ZMod p :=
  1 - orApprox T fun i => 1 - u i

/-- The exact `MOD_p` polynomial. -/
def modApprox (u : Fin m → ZMod p) : ZMod p :=
  (∑ i, u i) ^ (p - 1)

theorem orApprox_comp_mem {D : ℕ} (T : Fin ℓ → Finset (Fin m)) {v : Fin m → BitString n → ZMod p}
    (hv : ∀ k, v k ∈ lowDegree (ZMod p) n D) :
    (fun x => orApprox T fun k => v k x) ∈ lowDegree (ZMod p) n (ℓ * ((p - 1) * D)) := by
  have hfun : (fun x => orApprox T fun k => v k x) = 1 - ∏ j, (1 - (∑ i ∈ T j, v i) ^ (p - 1)) := by
    funext x
    simp only [orApprox, Pi.sub_apply, Pi.one_apply, Finset.prod_apply, Pi.pow_apply,
      Finset.sum_apply]
  rw [hfun]
  refine one_sub_mem_lowDegree ?_
  have h := prod_mem_lowDegree (R := ZMod p) (n := n) univ (a := (p - 1) * D)
    (f := fun j => 1 - (∑ i ∈ T j, v i) ^ (p - 1)) fun j _ =>
      one_sub_mem_lowDegree (pow_mem_lowDegree (sum_mem_lowDegree _ fun i _ => hv i) (p - 1))
  rwa [card_univ, Fintype.card_fin] at h

theorem andApprox_comp_mem {D : ℕ} (T : Fin ℓ → Finset (Fin m)) {v : Fin m → BitString n → ZMod p}
    (hv : ∀ k, v k ∈ lowDegree (ZMod p) n D) :
    (fun x => andApprox T fun k => v k x) ∈ lowDegree (ZMod p) n (ℓ * ((p - 1) * D)) := by
  have hmem := orApprox_comp_mem T (v := fun k => 1 - v k) fun k => one_sub_mem_lowDegree (hv k)
  have hfun : (fun x => andApprox T fun k => v k x) =
      1 - fun x => orApprox T fun k => (1 - v k) x := by
    funext x
    simp [andApprox]
  rw [hfun]
  exact one_sub_mem_lowDegree hmem

theorem modApprox_comp_mem {D : ℕ} {v : Fin m → BitString n → ZMod p}
    (hv : ∀ k, v k ∈ lowDegree (ZMod p) n D) :
    (fun x => modApprox fun k => v k x) ∈ lowDegree (ZMod p) n ((p - 1) * D) := by
  have hfun : (fun x => modApprox fun k => v k x) = (∑ i, v i) ^ (p - 1) := by
    funext x
    simp [modApprox, Finset.sum_apply]
  rw [hfun]
  exact pow_mem_lowDegree (sum_mem_lowDegree _ fun i _ => hv i) (p - 1)

/-! ### Exactness on bits -/

/-- A sum of bits is their count. -/
theorem sum_bitVal (S : Finset (Fin m)) (u : Fin m → Bool) :
    ∑ i ∈ S, bitVal (ZMod p) (u i) = (#(S.filter fun i => u i = true) : ZMod p) := by
  rw [Finset.card_filter, Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => by cases u i <;> simp [bitVal]

/-- The `(p - 1)`-st power of a count is whether the count is not divisible by `p`. -/
theorem natCast_pow_eq_bitVal (c : ℕ) :
    (c : ZMod p) ^ (p - 1) = bitVal (ZMod p) (decide (c % p ≠ 0)) := by
  have hp := (Fact.out : p.Prime).two_le
  by_cases hc : c % p = 0
  · have : (c : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff c p).2 (Nat.dvd_of_mod_eq_zero hc)
    rw [this, zero_pow (by omega)]
    simp [hc, bitVal]
  · rw [ZMod.pow_card_sub_one_eq_one fun h => hc (Nat.mod_eq_zero_of_dvd
      ((ZMod.natCast_eq_zero_iff c p).1 h))]
    simp [hc, bitVal]

/-- The `MOD_p` polynomial is exact on bits. -/
theorem modApprox_bitVal (u : Fin m → Bool) :
    modApprox (fun i => bitVal (ZMod p) (u i)) = bitVal (ZMod p) (modGate p m u) := by
  rw [modApprox, sum_bitVal, natCast_pow_eq_bitVal]
  rfl

/-! ### Counting erring tuples -/

/-- Toggle one coordinate in a set. -/
private def toggle (k : Fin m) (S : Finset (Fin m)) : Finset (Fin m) :=
  if k ∈ S then S.erase k else insert k S

private theorem toggle_toggle (k : Fin m) (S : Finset (Fin m)) : toggle k (toggle k S) = S := by
  unfold toggle
  by_cases hk : k ∈ S
  · simp [hk, Finset.insert_erase hk]
  · simp [hk, Finset.erase_insert hk]

/-- If some coordinate is true, at most half of the sets have a count divisible by `p`. -/
theorem two_mul_card_sum_eq_zero_le (u : Fin m → Bool) {k : Fin m} (hk : u k = true) :
    2 * #(univ.filter fun S : Finset (Fin m) => ∑ i ∈ S, bitVal (ZMod p) (u i) = 0) ≤ 2 ^ m := by
  set Z := univ.filter fun S : Finset (Fin m) => ∑ i ∈ S, bitVal (ZMod p) (u i) = 0
  set NZ := univ.filter fun S : Finset (Fin m) => ¬∑ i ∈ S, bitVal (ZMod p) (u i) = 0
  have htotal : #Z + #NZ = 2 ^ m := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_finset,
      Fintype.card_fin]
  have hle : #Z ≤ #NZ := by
    refine Finset.card_le_card_of_injOn (toggle k) (fun S hS => ?_) fun S _ T _ hST => ?_
    · simp only [Z, NZ, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hS ⊢
      unfold toggle
      by_cases hkS : k ∈ S
      · rw [ite_eq_left hkS, Finset.sum_erase_eq_sub hkS, hS, hk, bitVal_true, zero_sub]
        exact neg_ne_zero.2 one_ne_zero
      · rw [ite_eq_right hkS, Finset.sum_insert hkS, hS, hk, bitVal_true, add_zero]
        exact one_ne_zero
    · simpa only [toggle_toggle] using congrArg (toggle k) hST
  omega

theorem orApprox_bitVal_of_exists (T : Fin ℓ → Finset (Fin m)) (u : Fin m → Bool)
    (hT : ∃ j, ∑ i ∈ T j, bitVal (ZMod p) (u i) ≠ 0) :
    orApprox T (fun i => bitVal (ZMod p) (u i)) = 1 := by
  obtain ⟨j, hj⟩ := hT
  unfold orApprox
  rw [Finset.prod_eq_zero (Finset.mem_univ j)
    (by rw [ZMod.pow_card_sub_one_eq_one hj, sub_self]), sub_zero]

theorem orApprox_bitVal_of_forall_false (T : Fin ℓ → Finset (Fin m)) (u : Fin m → Bool)
    (hu : ∀ i, u i = false) : orApprox T (fun i => bitVal (ZMod p) (u i)) = 0 := by
  have hp := (Fact.out : p.Prime).two_le
  simp [orApprox, hu, bitVal, zero_pow (show p - 1 ≠ 0 by omega)]

/-- At most a `2 ^ (-ℓ)` fraction of the tuples make the OR approximator err on a fixed Boolean
vector. -/
theorem card_orApprox_wrong_mul_le (u : Fin m → Bool) :
    #(univ.filter fun T : Fin ℓ → Finset (Fin m) => orApprox T (fun i => bitVal (ZMod p) (u i)) ≠
        bitVal (ZMod p) (decide (∃ j, u j = true))) * 2 ^ ℓ ≤ (2 ^ m) ^ ℓ := by
  by_cases hex : ∃ k, u k = true
  · obtain ⟨k, hk⟩ := hex
    set Z := univ.filter fun S : Finset (Fin m) => ∑ i ∈ S, bitVal (ZMod p) (u i) = 0
    have hsub : (univ.filter fun T : Fin ℓ → Finset (Fin m) =>
        orApprox T (fun i => bitVal (ZMod p) (u i)) ≠
          bitVal (ZMod p) (decide (∃ j, u j = true))) ⊆ Fintype.piFinset fun _ => Z := by
      intro T hT
      simp only [mem_filter, mem_univ, true_and, show (∃ j, u j = true) from ⟨k, hk⟩,
        decide_true] at hT
      rw [Fintype.mem_piFinset]
      intro j
      simp only [Z, mem_filter, mem_univ, true_and]
      by_contra hj
      exact hT (orApprox_bitVal_of_exists T u ⟨j, hj⟩)
    calc _ ≤ #(Fintype.piFinset fun _ : Fin ℓ => Z) * 2 ^ ℓ :=
          Nat.mul_le_mul_right _ (card_le_card hsub)
      _ = (2 * #Z) ^ ℓ := by
          rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, mul_pow, mul_comm]
      _ ≤ (2 ^ m) ^ ℓ := Nat.pow_le_pow_left (two_mul_card_sum_eq_zero_le u hk) ℓ
  · push Not at hex
    have hu : ∀ i, u i = false := fun i => by simpa using hex i
    rw [filter_false_of_mem fun T _ => by
      rw [orApprox_bitVal_of_forall_false T u hu]
      simp [hu]]
    simp

/-- **Averaging over the inputs.** For arguments `u x` depending on the input, some tuple makes the
OR approximator err on at most `2 ^ n / 2 ^ ℓ` inputs. -/
theorem exists_orApprox (u : BitString n → Fin m → Bool) :
    ∃ T : Fin ℓ → Finset (Fin m),
      #(univ.filter fun x => orApprox T (fun i => bitVal (ZMod p) (u x i)) ≠
          bitVal (ZMod p) (decide (∃ j, u x j = true))) * 2 ^ ℓ ≤ 2 ^ n := by
  classical
  let Wrong : (Fin ℓ → Finset (Fin m)) → BitString n → Prop := fun T x =>
    orApprox T (fun i => bitVal (ZMod p) (u x i)) ≠ bitVal (ZMod p) (decide (∃ j, u x j = true))
  have hsum : ∑ T, #(univ.filter fun x => Wrong T x) * 2 ^ ℓ ≤
      ∑ _T : Fin ℓ → Finset (Fin m), 2 ^ n := by
    calc ∑ T, #(univ.filter fun x => Wrong T x) * 2 ^ ℓ =
          ∑ x, #(univ.filter fun T => Wrong T x) * 2 ^ ℓ := by
          simp only [card_filter, sum_mul]
          exact sum_comm
      _ ≤ ∑ _x : BitString n, (2 ^ m) ^ ℓ :=
          sum_le_sum fun x _ => card_orApprox_wrong_mul_le (u x)
      _ = ∑ _T : Fin ℓ → Finset (Fin m), 2 ^ n := by
          simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_finset, Fintype.card_fin, smul_eq_mul]
          ring
  obtain ⟨T, _, hT⟩ := exists_le_of_sum_le univ_nonempty hsum
  exact ⟨T, hT⟩

/-- **Gate approximators.** For every operation of the AC⁰[p] basis and every way `u` its
arguments depend on the input, some approximator multiplies degrees by at most `(p - 1) ℓ` and errs
on at most `2 ^ n / 2 ^ ℓ` inputs. -/
theorem exists_gate_approx (hℓ : 1 ≤ ℓ) (op : Unbounded.extSignature.Op)
    (u : BitString n → Fin (Unbounded.extSignature.Arity op) → Bool) :
    ∃ A : (Fin (Unbounded.extSignature.Arity op) → ZMod p) → ZMod p,
      (∀ (D : ℕ) (v : Fin (Unbounded.extSignature.Arity op) → BitString n → ZMod p),
        (∀ k, v k ∈ lowDegree (ZMod p) n D) →
          (fun x => A fun k => v k x) ∈ lowDegree (ZMod p) n ((p - 1) * ℓ * D)) ∧
      #(univ.filter fun x => A (fun k => bitVal (ZMod p) (u x k)) ≠
          bitVal (ZMod p) (Unbounded.extInterpretation (modGate p) op (u x))) * 2 ^ ℓ ≤ 2 ^ n := by
  have hp := (Fact.out : p.Prime).two_le
  have hdeg : ∀ D : ℕ, ℓ * ((p - 1) * D) = (p - 1) * ℓ * D := fun D => by ring
  cases op with
  | ac op =>
    cases op with
    | not =>
      refine ⟨fun u => 1 - u 0, fun D v hv => ?_, ?_⟩
      · refine lowDegree_mono ?_ (one_sub_mem_lowDegree (hv 0))
        have : 1 ≤ (p - 1) * ℓ := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
        nlinarith
      · rw [filter_false_of_mem fun x _ => by
          simp [Unbounded.extInterpretation, Unbounded.interpretation, bitVal_not]]
        simp
    | or m =>
      obtain ⟨T, hT⟩ := exists_orApprox (p := p) (ℓ := ℓ) u
      exact ⟨orApprox T, fun D v hv => hdeg D ▸ orApprox_comp_mem T hv, hT⟩
    | and m =>
      obtain ⟨T, hT⟩ := exists_orApprox (p := p) (ℓ := ℓ) fun x k => !u x k
      refine ⟨andApprox T, fun D v hv => hdeg D ▸ andApprox_comp_mem T hv, ?_⟩
      convert hT using 4 with x
      simp only [andApprox, bitVal_not, Unbounded.extInterpretation, Unbounded.interpretation,
        ne_eq]
      rw [show decide (∀ j : Fin m, u x j = true) = !decide (∃ j, (!u x j) = true) by
          rw [Bool.eq_iff_iff, Bool.not_eq_true', decide_eq_true_iff, decide_eq_false_iff_not,
            not_exists]
          simp,
        bitVal_not, sub_right_inj]
  | gate m =>
    refine ⟨modApprox, fun D v hv => lowDegree_mono (Nat.mul_le_mul_right D
      (Nat.le_mul_of_pos_right _ (by omega))) (modApprox_comp_mem hv), ?_⟩
    rw [filter_false_of_mem fun x _ => by
      rw [modApprox_bitVal]
      simp [Unbounded.extInterpretation]]
    simp

end Cslib.Circuits.Boolean.Smolensky
