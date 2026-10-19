/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.PPoly
public import Complexity.Computability.Circuit.Boolean.Substitution
public import Complexity.Computability.Complexity.Classes.PH
public import Complexity.Computability.MCSP.NP
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Cslib.Computability.Circuit.Boolean.Shannon
import Cslib.Foundations.Data.Nat.Asymptotics

/-!
# Kannan's theorem

For every `k`, some language in `Σ₂` has no circuits of size `O(n ^ k)`
[Kannan][Kannan1982], [Arora and Barak, Exercise 6.5][AroraBarak09].

## Main definitions

* `Cslib.Complexity.Kannan.language`: a language in `Σ₃` without circuits of size `O(n ^ k)`.

## Main results

* `Cslib.Complexity.Kannan.language_not_mem_SIZE`: Kannan's language has no circuits of size
  `O(n ^ k)`.

## References

* [R. Kannan, *Circuit-size lower bounds and non-reducibility to sparse sets*][Kannan1982]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Circuits Circuits.Boolean Turing.MultiTapeTM Filter

namespace Kannan

/-! ### Parameters -/

/-- The number of inputs of the hard functions at input length `n`. -/
def arity (k n : ℕ) : ℕ := (k + 3) * (Nat.log 2 (n + 1) + 1)

/-- The number of gates that the hard functions at input length `n` exceed. -/
def threshold (k n : ℕ) : ℕ := (n + 1) ^ (k + 1)

theorem two_pow_arity (k n : ℕ) : 2 ^ arity k n = (2 ^ (Nat.log 2 (n + 1) + 1)) ^ (k + 3) := by
  rw [arity, Nat.mul_comm, pow_mul]

theorem two_pow_arity_le (k n : ℕ) : 2 ^ arity k n ≤ 2 ^ (k + 3) * (n + 1) ^ (k + 3) := by
  rw [two_pow_arity, ← Nat.mul_pow, pow_succ 2 (Nat.log 2 (n + 1)), Nat.mul_comm _ 2]
  exact Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (Nat.succ_ne_zero n))) _

theorem lt_two_pow_arity (k n : ℕ) : (n + 1) ^ (k + 3) < 2 ^ arity k n := by
  rw [two_pow_arity]
  exact Nat.pow_lt_pow_left (Nat.lt_pow_succ_log_self (by norm_num) _) (by omega)

theorem arity_le (k n : ℕ) : arity k n ≤ (k + 3) * (n + 1) :=
  Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (Nat.log_lt_self 2 (Nat.succ_ne_zero n)))

/-- The hard functions have enough inputs for `2 ^ m / m` to exceed the threshold. -/
theorem threshold_mul_arity_lt {k n : ℕ} (hn : k + 3 ≤ n + 1) :
    threshold k n * arity k n < 2 ^ arity k n := by
  refine lt_of_le_of_lt ?_ (lt_two_pow_arity k n)
  calc threshold k n * arity k n ≤ (n + 1) ^ (k + 1) * ((n + 1) * (n + 1)) :=
        Nat.mul_le_mul_left _ ((arity_le k n).trans (Nat.mul_le_mul_right _ hn))
    _ = (n + 1) ^ (k + 3) := by ring

theorem le_arity (k n : ℕ) : Nat.log 2 (n + 1) + 1 ≤ arity k n :=
  Nat.le_mul_of_pos_left _ (by omega)

/-- The hard functions eventually have no more inputs than the instance. -/
theorem eventually_arity_le (k : ℕ) : ∀ᶠ n in atTop, arity k n ≤ n := by
  filter_upwards [Nat.eventually_mul_log_le (2 * (k + 3)) one_lt_two, eventually_ge_atTop 4]
    with n hn h4
  have hlog : Nat.log 2 (n + 1) ≤ Nat.log 2 n + 1 := by
    calc Nat.log 2 (n + 1) ≤ Nat.log 2 (n * 2) := Nat.log_mono_right (by omega)
      _ = Nat.log 2 n + 1 := Nat.log_mul_base (by norm_num) (by omega)
  have h2 : 2 ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 (by omega)
  calc arity k n ≤ (k + 3) * (Nat.log 2 n + 2) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ 2 * (k + 3) * Nat.log 2 n := by nlinarith
    _ ≤ n := hn

/-- The hard functions eventually have at least `N` inputs. -/
theorem eventually_le_arity (k N : ℕ) : ∀ᶠ n in atTop, N ≤ arity k n := by
  filter_upwards [eventually_ge_atTop (2 ^ N)] with n hn
  have : N ≤ Nat.log 2 (n + 1) := (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 (by omega)
  exact this.trans ((Nat.le_succ _).trans (le_arity k n))

/-! ### Hard truth tables -/

/-- The function on `m` inputs with the truth table `T`, read as MCSP reads truth tables. -/
def tableFunction (m : ℕ) (T : List Bool) : BooleanFunction m :=
  fun y => MCSP.tableValue T (List.ofFn y)

/-- `T` is a truth table on `arity k n` inputs whose function needs more than `threshold k n`
gates. -/
def IsHard (k n : ℕ) (T : List Bool) : Prop :=
  T.length = 2 ^ arity k n ∧
    threshold k n < complexity interpretation (single (tableFunction (arity k n) T))

/-- `T` is the first hard truth table in lexicographic order: the hard table that is least as a
binary number, most significant bit first. -/
def IsFirstHard (k n : ℕ) (T : List Bool) : Prop :=
  IsHard k n T ∧ ∀ T', IsHard k n T' → BitString.binaryValue T ≤ BitString.binaryValue T'

/-- **Kannan's language**: the words `x` whose first `arity k x.length` bits, as an input of the
first hard truth table, give `true`. The slices at the lengths without hard truth tables are
empty. -/
def language (k : ℕ) : Language Bool :=
  {x | ∃ T, IsFirstHard k x.length T ∧ MCSP.tableValue T (x.take (arity k x.length)) = true}

/-- Lists of the same length with the same binary value are equal. -/
theorem binaryValue_injective {u v : List Bool} (hlen : u.length = v.length)
    (h : BitString.binaryValue u = BitString.binaryValue v) : u = v := by
  induction u using List.reverseRecOn generalizing v with
  | nil => simpa [eq_comm] using hlen
  | append_singleton u a ih =>
    obtain ⟨v, b, rfl⟩ : ∃ v' b, v = v' ++ [b] :=
      ⟨v.dropLast, v.getLast (List.ne_nil_of_length_pos (by simp at hlen; omega)),
        (List.dropLast_append_getLast _).symm⟩
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlen
    rw [BitString.binaryValue_snoc, BitString.binaryValue_snoc] at h
    have hab : a = b := by
      cases a <;> cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] at h <;>
        first | rfl | omega
    subst hab
    rw [ih hlen (by omega)]

theorem IsFirstHard.unique {k n : ℕ} {T₁ T₂ : List Bool} (h₁ : IsFirstHard k n T₁)
    (h₂ : IsFirstHard k n T₂) : T₁ = T₂ :=
  binaryValue_injective (h₁.1.1.trans h₂.1.1.symm) ((h₁.2 _ h₂.1).antisymm (h₂.2 _ h₁.1))

/-- If some truth table is hard, there is a first one. -/
theorem exists_isFirstHard {k n : ℕ} (h : ∃ T, IsHard k n T) : ∃ T, IsFirstHard k n T := by
  classical
  have hex : ∃ v, ∃ T, IsHard k n T ∧ BitString.binaryValue T = v :=
    let ⟨T, hT⟩ := h
    ⟨_, T, hT, rfl⟩
  obtain ⟨T, hT, hv⟩ := Nat.find_spec hex
  exact ⟨T, hT, fun T' hT' => hv ▸ Nat.find_min' hex ⟨T', hT', rfl⟩⟩

/-- The truth table of a function, as a list, is read back as the function. -/
theorem tableFunction_ofFn_truthTable (m : ℕ) (f : BooleanFunction m) :
    tableFunction m (List.ofFn (MCSP.truthTable m f)) = f := by
  funext y
  exact MCSP.tableValue_ofFn ⟨m, MCSP.truthTable m f, 0⟩ y |>.trans (by simp [MCSP.Instance.function])

/-- **Shannon's counting argument**: hard truth tables exist at all large lengths. -/
theorem eventually_exists_isHard (k : ℕ) : ∀ᶠ n in atTop, ∃ T, IsHard k n T := by
  obtain ⟨N, hN⟩ := Shannon.lt_complexity
  filter_upwards [eventually_le_arity k (max N 1), eventually_ge_atTop (k + 2)] with n hm hn
  obtain ⟨f, hf⟩ := hN (arity k n) (le_of_max_le_left hm)
  refine ⟨List.ofFn (MCSP.truthTable _ f), by simp, ?_⟩
  rw [tableFunction_ofFn_truthTable]
  have hm0 : (0 : ℝ) < arity k n := by exact_mod_cast (le_of_max_le_right hm)
  have hlt : (threshold k n : ℝ) * arity k n < 2 ^ arity k n := by
    exact_mod_cast threshold_mul_arity_lt (by omega)
  have : (threshold k n : ℝ) < 2 ^ arity k n / arity k n := by
    rwa [lt_div_iff₀ hm0]
  exact_mod_cast this.trans hf

/-! ### The circuit lower bound -/

/-- The slice of Kannan's language is the function of the first hard truth table on the first
`arity k n` bits. -/
theorem slice_language {k n : ℕ} {T : List Bool} (hT : IsFirstHard k n T) (x : Fin n → Bool) :
    (language k).slice n x = MCSP.tableValue T ((List.ofFn x).take (arity k n)) := by
  rw [Bool.eq_iff_iff, Language.slice_eq_true_iff]
  change (∃ T', IsFirstHard k (List.ofFn x).length T' ∧ _) ↔ _
  simp only [List.length_ofFn]
  exact ⟨fun ⟨T', hT', h⟩ => hT.unique hT' ▸ h, fun h => ⟨T, hT, h⟩⟩

/-- Feeding the first `m ≤ n` inputs from `m` variables and the others with `false`. -/
def restriction (m n : ℕ) (j : Fin n) : Fin m ⊕ Bool :=
  if h : j.val < m then .inl ⟨j.val, h⟩ else .inr false

theorem take_ofFn_substitute_restriction {m n : ℕ} (h : m ≤ n) (y : Fin m → Bool) :
    (List.ofFn (substitute (restriction m n) y)).take m = List.ofFn y := by
  refine List.ext_getElem (by simp [h]) fun i h₁ h₂ => ?_
  simp only [List.length_ofFn] at h₂
  simp [restriction, substitute, h₂]

/-- The slices of Kannan's language need more than `threshold k n - 2` gates where a hard truth
table exists on at most `n` inputs. -/
theorem threshold_lt_complexity_slice {k n : ℕ} {T : List Bool} (hT : IsFirstHard k n T)
    (hm : arity k n ≤ n) :
    threshold k n < complexity interpretation (single ((language k).slice n)) + 2 := by
  refine hT.1.2.trans_le (le_of_eq_of_le ?_
    (complexity_substitute_le (restriction (arity k n) n) ((language k).slice n)))
  congr 2
  funext y
  rw [slice_language hT, take_ofFn_substitute_restriction hm]
  rfl

/-- **Kannan's language has no circuits of size `O(n ^ k)`.** -/
theorem language_not_mem_SIZE (k c : ℕ) : language k ∉ SIZE fun n => c * (n + 1) ^ k := by
  intro hL
  obtain ⟨n, ⟨T, hT⟩, hm, hc⟩ := ((eventually_exists_isHard k).and
    ((eventually_arity_le k).and (eventually_ge_atTop (c + 2)))).exists
  obtain ⟨T, hT⟩ := exists_isFirstHard ⟨T, hT⟩
  have hlt := threshold_lt_complexity_slice hT hm
  have hle := hL n
  have hpow : (c + 3) * (n + 1) ^ k ≤ threshold k n := by
    rw [threshold, pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (by omega)
  have hpos : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  nlinarith

end Kannan

end Cslib.Complexity
