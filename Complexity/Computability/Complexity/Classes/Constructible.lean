/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.SpaceInTime
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Arith
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import Complexity.Computability.Machines.Turing.MultiTape.Universal.Compose
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant

/-!
# Constructible resource bounds

A time- or space-constructible bound is computed in binary from a word of length `n` by one
finite-state binary-alphabet machine, within `O(t n)` time or `O(s n)` work space respectively.
The input tape is read-only and the output tape write-only. Neither definition imposes a lower
bound on the resource function; hierarchy theorems state the lower bounds they need separately.

The shared length and arithmetic routines give concrete constructible bounds, without importing
any hierarchy theorem.

## Main definitions

* `Cslib.Complexity.TimeConstructible`: time-constructible bounds.
* `Cslib.Complexity.SpaceConstructible`: space-constructible bounds.

## Main results

* `Cslib.Complexity.TimeConstructible.spaceConstructible`: time constructibility implies
  space constructibility.
* `Cslib.Complexity.timeConstructible_two_pow`, `Cslib.Complexity.timeConstructible_succ_pow`,
  `Cslib.Complexity.TimeConstructible.succ_mul`: time-constructible bounds.
* `Cslib.Complexity.spaceConstructible_const`, `Cslib.Complexity.spaceConstructible_id`,
  `Cslib.Complexity.spaceConstructible_succ`, `Cslib.Complexity.spaceConstructible_succ_pow`,
  `Cslib.Complexity.spaceConstructible_two_pow`: space-constructible bounds.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Definition 9.1][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 1.2][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- The binary digits of `m` are logarithmic: `2 ^ (encNat m).length ≤ 2 * (m + 1)`. -/
theorem two_pow_length_encNat_le (m : ℕ) : 2 ^ (encNat m).length ≤ 2 * (m + 1) := by
  rw [encNat_apply, Nat.size_eq_bits_len]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h₁ : 2 ^ (m.size - 1) ≤ m := Nat.lt_size.mp (by
      have := Nat.size_pos.mpr hm
      omega)
    have h₂ : 1 ≤ m.size := Nat.size_pos.mpr hm
    rw [show m.size = (m.size - 1) + 1 by omega, pow_succ]
    omega

/-- Every power of the number of binary digits of `m` is `O(m + 1)`. -/
theorem exists_pow_length_encNat_le (d : ℕ) :
    ∃ C, ∀ m, ((encNat m).length + 1) ^ d ≤ C * (m + 1) := by
  obtain ⟨C, hC⟩ := Cslib.PolynomiallyBounded.exists_le_mul_two_pow (p := fun L => (L + 1) ^ d)
    (by fun_prop)
  refine ⟨2 * C, fun m => (hC _).trans ?_⟩
  calc C * 2 ^ (encNat m).length ≤ C * (2 * (m + 1)) :=
        Nat.mul_le_mul_left _ (two_pow_length_encNat_le m)
    _ = 2 * C * (m + 1) := by ring

/-! ### Lengths and comparisons, computed -/

namespace ComputableTidilyInO

/-- The length of a bit word in unary, within linear time and space, by the streaming machine of
`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.length_bits`. -/
theorem lengthUnary : ComputableTidilyInO (fun l : List Bool => l.length) encBits encUnary
    (fun l => l.length) fun l => l.length :=
  .of_bounds ComputableTidilyInTimeAndSpace.length_bits 8 (fun l => by omega)
    (fun _ => Nat.zero_le _) fun l => by simp only [encUnary_apply, List.length_replicate]; omega

/-- The length of a bit word in binary, by a binary counter, within quadratic time and linear
space. -/
theorem lengthNat : ComputableTidilyInO (fun l : List Bool => l.length) encBits encNat
    (fun l => (l.length + 1) ^ 2) fun l => l.length + 1 := by
  obtain ⟨C, hC⟩ := exists_pow_length_encNat_le 2
  have hstep := natSucc.comp (fst encNat encBool)
  have hlen (x : List Bool) (i : ℕ) :
      (List.take i x).foldl (fun n _ => n + 1) 0 = min i x.length := by
    simp [List.foldl_const]
  have h := foldl (encA := encBool) (encL := encBits) (encB := encNat) (list := id)
    (init := fun _ => 0) (step := fun n _ => n + 1) (of_linear (.of_eq fun _ => rfl)) (const 0)
    hstep (R := fun x => (C + 3) * (x.length + 1)) (Q := fun x => 3 * (x.length + 1))
    (B := fun x => x.length)
    (fun x i hi => by
      simp only [id] at hi ⊢
      rw [hlen]
      have h₁ := hC (min i x.length)
      have h₂ := Universal.length_encNat_le (min i x.length)
      have h₃ : C * (min i x.length + 1) ≤ C * (x.length + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have e : (C + 3) * (x.length + 1) = C * (x.length + 1) + 3 * (x.length + 1) := by ring
      simp only [length_encPair, encBool_apply, List.length_singleton]
      omega)
    (fun x i hi => by
      simp only [id] at hi ⊢
      rw [hlen]
      have h₂ := Universal.length_encNat_le (min i x.length)
      simp only [length_encPair, encBool_apply, List.length_singleton]
      omega)
    (fun x i hi => by
      simp only [id] at hi ⊢
      rw [hlen]
      exact (Universal.length_encNat_le _).trans (Nat.min_le_right _ _))
  refine (h.mono (C + 16) (fun x => ?_) fun x => ?_).of_enc_eq fun x => ?_
  · simp only [id, encBits_apply]
    nlinarith
  · simp only [id, encBits_apply]
    nlinarith
  · simp [List.foldl_const]

/-- The comparison of unary numbers, by counting down, within quadratic time and linear space. -/
theorem unaryLe : ComputableTidilyInO (fun p : ℕ × ℕ => decide (p.1 ≤ p.2))
    (encPair encUnary encUnary) encBool (fun p => ((encPair encUnary encUnary p).length + 1) ^ 2)
    fun p => (encPair encUnary encUnary p).length + 1 := by
  have hstep := (ComputableTidilyInDegree.unary_pred.inO_one).comp (fst encUnary encBool)
  have hrep (a b : ℕ) : (List.replicate b true).foldl (fun n _ => n - 1) a = a - b := by
    induction b generalizing a with
    | zero => rfl
    | succ b ih => rw [List.replicate_succ, List.foldl_cons, ih]; omega
  have h := foldl (encA := encBool) (encL := encBits) (encB := encUnary)
    (list := fun p : ℕ × ℕ => List.replicate p.2 true) (init := fun p => p.1)
    (step := fun n _ => n - 1)
    ((of_linear (.of_eq (f := fun n => List.replicate n true) (encIn := encUnary)
      (encMid := encBits) fun _ => rfl)).comp (snd encUnary encUnary))
    (fst encUnary encUnary) hstep
    (R := fun p => 3 * ((encPair encUnary encUnary p).length + 1))
    (Q := fun p => 3 * ((encPair encUnary encUnary p).length + 1))
    (B := fun p => (encPair encUnary encUnary p).length)
    (fun p i hi => by
      rw [List.take_replicate, hrep]
      simp only [length_encPair, encUnary_apply, List.length_replicate,
        encBool_apply, List.length_singleton]
      omega)
    (fun p i hi => by
      rw [List.take_replicate, hrep]
      simp only [length_encPair, encUnary_apply, List.length_replicate,
        encBool_apply, List.length_singleton]
      omega)
    (fun p i hi => by
      rw [List.take_replicate, hrep]
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      omega)
  have hz := (ComputableTidilyInDegree.unary_isZero.inO_one).comp_linear h
  refine (hz.mono 16 (fun p => ?_) fun p => ?_).of_enc_eq fun p => ?_
  · simp only [length_encPair, encUnary_apply, List.length_replicate,
      encBits_apply]
    nlinarith
  · simp only [length_encPair, encUnary_apply, List.length_replicate,
      encBits_apply]
    omega
  · simp only [Function.comp_apply, hrep, Nat.sub_eq_zero_iff_le]

end ComputableTidilyInO

/-- **From binary to unary**, by counting down: within time `O((n + 1) ^ 3)` and space `O(n)`. -/
theorem ComputableTidilyInO.natToUnary : ComputableTidilyInO (fun n : ℕ => n) encNat encUnary
    (fun n => (n + 1) ^ 3) fun n => n := by
  have hiter (n : ℕ) : (· + 1)^[n] 0 = n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih]
  have h := ComputableTidilyInO.iterate (n := fun n : ℕ => n) (init := fun _ => 0)
    (step := (· + 1)) (encIn := encNat) (encB := encUnary)
    (ComputableTidilyInO.of_linear (.of_eq fun _ => rfl)) (ComputableTidilyInO.const 0)
    ComputableTidilyInDegree.unary_succ.inO_one (R := fun n => n) (Q := fun n => n)
    (B := fun n => n)
    (fun n k hk => by simp only [hiter, encUnary_apply, List.length_replicate]; exact hk)
    (fun n k hk => by simp only [hiter, encUnary_apply, List.length_replicate]; exact hk)
    (fun n k hk => by simp only [hiter, encUnary_apply, List.length_replicate]; exact hk)
  refine (h.of_enc_eq fun n => by rw [hiter]).mono 8 (fun n => ?_) fun n => ?_
  all_goals
    have := Universal.length_encNat_le n
    have h₁ : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have h₂ : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have h₃ := Nat.pow_le_pow_left (show (encNat n).length + 1 ≤ n + 1 by omega) 2
  · nlinarith
  · omega

end Turing.MultiTapeTM

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- A bound `t` is time-constructible when some machine with a binary alphabet and finitely many
states computes `t n` in binary from any word of length `n` within time `O(t n)`. Arora and Barak
also ask for `n ≤ t n` [Arora and Barak, Section 1.2][AroraBarak09]; this definition omits that
condition, and the results that need it, such as `Cslib.Complexity.DTIME_ssubset_DTIME`, assume it
separately. -/
def TimeConstructible (t : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∃ s : ℕ → ℕ, ComputableInTimeAndSpaceOfLength (fun x : List Bool => t x.length) encBits
    encNat (fun n => c * t n + c) s

/-- A time-constructible bound is computed tidily within time and space `O(t n)`. -/
theorem TimeConstructible.computableTidilyInO {t : ℕ → ℕ} (ht : TimeConstructible t) :
    ComputableTidilyInO (fun x : List Bool => t x.length) encBits encNat (fun x => t x.length)
      fun x => t x.length := by
  obtain ⟨c, s, h⟩ := ht
  obtain ⟨k, h⟩ := ComputableInTimeAndSpace.exists_space_linear h
  obtain ⟨d, h⟩ := h.exists_computableTidilyInTimeAndSpace
  have ht (T : ℕ) : 2 * (c * T + c) + 3 * (k * (c * T + c) + k) + d ≤
      ((2 + 3 * k) * c + 3 * k + d) * (T + 1) := by
    have e₁ : 2 * (c * T + c) + 3 * (k * (c * T + c) + k) + d =
        (2 + 3 * k) * c * (T + 1) + (3 * k + d) := by ring
    have e₂ : ((2 + 3 * k) * c + 3 * k + d) * (T + 1) =
        (2 + 3 * k) * c * (T + 1) + (3 * k + d) * (T + 1) := by ring
    have := Nat.le_mul_of_pos_right (3 * k + d) (show 0 < T + 1 by omega)
    omega
  have hs (T : ℕ) : d * (k * (c * T + c) + k + 1) ≤ d * (k * c + k + 1) * (T + 1) := by
    have e₁ : d * (k * (c * T + c) + k + 1) = d * (k * c) * (T + 1) + d * (k + 1) := by ring
    have e₂ : d * (k * c + k + 1) * (T + 1) =
        d * (k * c) * (T + 1) + d * (k + 1) * (T + 1) := by ring
    have := Nat.le_mul_of_pos_right (d * (k + 1)) (show 0 < T + 1 by omega)
    omega
  refine .of_bounds h ((2 + 3 * k) * c + 3 * k + d + d * (k * c + k + 1) + 1) (fun x => ?_)
    (fun x => ?_) fun x => (length_encNat_le _).trans ?_
  · simp only [encBits_apply]
    exact (ht _).trans (Nat.mul_le_mul_right _ (by omega))
  · simp only [encBits_apply]
    exact (hs _).trans (Nat.mul_le_mul_right _ (by omega))
  · exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (by omega))

/-- A tidy computation of `t n` in binary within time `O(t n)` makes `t` time-constructible. -/
theorem TimeConstructible.of_computableTidilyInO {t : ℕ → ℕ} {T S : List Bool → ℕ} {s : ℕ → ℕ}
    (c : ℕ) (h : ComputableTidilyInO (fun x : List Bool => t x.length) encBits encNat T S)
    (hT : ∀ x, T x ≤ c * t x.length + c) (hS : ∀ x, S x ≤ s x.length) : TimeConstructible t := by
  obtain ⟨k, hk, -⟩ := h
  refine ⟨k * (c + 1), fun n => k * (s n + 1), hk.computableInTimeAndSpace.mono (fun x => ?_)
    fun x => ?_⟩
  · simp only [encBits_apply]
    have := Nat.mul_le_mul_left k (Nat.add_le_add_right (hT x) 1)
    have e₁ : k * (c * t x.length + c + 1) = k * c * t x.length + k * c + k := by ring
    have e₂ : k * (c + 1) * t x.length + k * (c + 1) =
        k * c * t x.length + k * t x.length + k * c + k := by ring
    omega
  · simp only [encBits_apply]
    exact Nat.mul_le_mul_left k (Nat.add_le_add_right (hS x) 1)

/-- `2 ^ n` is time-constructible: its binary digits are `n` zeros followed by a one. -/
theorem timeConstructible_two_pow : TimeConstructible (2 ^ ·) :=
  .of_computableTidilyInO 1 (ComputableTidilyInDegree.two_pow_length encBits).inO_one
    (s := fun n => n) (fun x => by
      simp only [encBits_apply]
      have := Nat.lt_two_pow_self (n := x.length)
      omega) fun _ => le_rfl

private theorem cube_add_le (u v : ℕ) : (u + v) ^ 3 ≤ 8 * (u ^ 3 + v ^ 3) := by
  rcases le_total u v with h | h
  · have h₁ : (u + v) ^ 3 ≤ (2 * v) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h₂ : (2 * v) ^ 3 = 8 * v ^ 3 := by ring
    omega
  · have h₁ : (u + v) ^ 3 ≤ (2 * u) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h₂ : (2 * u) ^ 3 = 8 * u ^ 3 := by ring
    omega

/-- If `f n` is computed in binary from words of length `n` within time `O((n + 1) * f n)` and
`n ≤ f n`, then `(n + 1) * f n` is time-constructible: writing the length of the word in binary
takes time `O(n ^ 2)`, and the product time polylogarithmic in the factors. -/
theorem TimeConstructible.succ_mul_of_computableTidilyInO {f : ℕ → ℕ} {T : List Bool → ℕ}
    {S : ℕ → ℕ} (c : ℕ)
    (hf : ComputableTidilyInO (fun x : List Bool => f x.length) encBits encNat T
      fun x => S x.length)
    (hT : ∀ x, T x ≤ c * ((x.length + 1) * f x.length) + c) (hn : ∀ n, n ≤ f n) :
    TimeConstructible fun n => (n + 1) * f n := by
  have hlen := ComputableTidilyInO.natSucc.comp ComputableTidilyInO.lengthNat
  have h := computableTidilyInDegree_mul.inO.comp (hlen.prod hf)
  obtain ⟨C, hC⟩ := exists_pow_length_encNat_le 3
  obtain ⟨C₂, hC₂⟩ := exists_pow_length_encNat_le 2
  refine .of_computableTidilyInO (150 * C + C₂ + c + 10) h (fun x => ?_) (s := fun n =>
    n + 1 + ((encNat n).length + 1) + S n + (2 * (encNat (n + 1)).length + 1 +
      (encNat (f n)).length + 1) ^ 3) fun x => ?_
  · simp only [Function.comp_apply, length_encPair]
    have hTx := hT x
    set n := x.length
    have hfn := hn n
    have h₁ : (n + 1) ^ 2 ≤ 2 * ((n + 1) * f n) + 1 := by nlinarith
    have h₂ : ((encNat n).length + 1) ^ 2 ≤ C₂ * ((n + 1) * f n) + C₂ := by
      have := hC₂ n
      have : C₂ * (n + 1) ≤ C₂ * ((n + 1) * f n + 1) := Nat.mul_le_mul_left _ (by nlinarith)
      have e : C₂ * ((n + 1) * f n + 1) = C₂ * ((n + 1) * f n) + C₂ := by ring
      omega
    have h₃ : f n ≤ (n + 1) * f n := Nat.le_mul_of_pos_left _ (by omega)
    have h₄ := cube_add_le (2 * ((encNat (n + 1)).length + 1)) ((encNat (f n)).length + 1)
    have h₅ : (2 * ((encNat (n + 1)).length + 1)) ^ 3 = 8 * ((encNat (n + 1)).length + 1) ^ 3 := by
      ring
    have h₆ := hC (n + 1)
    have h₇ := hC (f n)
    have h₈ : (2 * (encNat (n + 1)).length + 1 + (encNat (f n)).length + 1) ^ 3 ≤
        (2 * ((encNat (n + 1)).length + 1) + ((encNat (f n)).length + 1)) ^ 3 :=
      Nat.pow_le_pow_left (by omega) 3
    have h₉ : C * (n + 1 + 1) ≤ C * ((n + 1) * f n) + 2 * C := by
      have : n + 1 + 1 ≤ (n + 1) * f n + 2 := by nlinarith
      have := Nat.mul_le_mul_left C this
      have e : C * ((n + 1) * f n + 2) = C * ((n + 1) * f n) + 2 * C := by ring
      omega
    have h₁₀ : C * (f n + 1) ≤ C * ((n + 1) * f n) + C := by
      have := Nat.mul_le_mul_left C (Nat.add_le_add_right h₃ 1)
      have e : C * ((n + 1) * f n + 1) = C * ((n + 1) * f n) + C := by ring
      omega
    have e : (150 * C + C₂ + c + 10) * ((n + 1) * f n) =
        150 * (C * ((n + 1) * f n)) + C₂ * ((n + 1) * f n) + c * ((n + 1) * f n) +
          10 * ((n + 1) * f n) := by
      ring
    omega
  · simp only [Function.comp_apply, length_encPair]
    exact le_rfl

/-- If `f` is time-constructible and `n ≤ f n`, then so is `(n + 1) * f n`. -/
theorem TimeConstructible.succ_mul {f : ℕ → ℕ} (hf : TimeConstructible f) (hn : ∀ n, n ≤ f n) :
    TimeConstructible fun n => (n + 1) * f n :=
  succ_mul_of_computableTidilyInO 1 hf.computableTidilyInO (fun x => by
    have : f x.length ≤ (x.length + 1) * f x.length := Nat.le_mul_of_pos_left _ (by omega)
    omega) hn

/-- `(n + 1) ^ 2` is time-constructible. -/
theorem timeConstructible_succ_sq : TimeConstructible fun n => (n + 1) ^ 2 := by
  have hlen := ComputableTidilyInO.natSucc.comp ComputableTidilyInO.lengthNat
  obtain ⟨C₂, hC₂⟩ := exists_pow_length_encNat_le 2
  have h := TimeConstructible.succ_mul_of_computableTidilyInO (f := fun n => n + 1)
    (S := fun n => n + 1 + ((encNat n).length + 1)) (C₂ + 2) hlen (fun x => by
      have := hC₂ x.length
      have e : (C₂ + 2) * ((x.length + 1) * (x.length + 1)) =
          C₂ * ((x.length + 1) * (x.length + 1)) + 2 * ((x.length + 1) * (x.length + 1)) := by
        ring
      have : C₂ * (x.length + 1) ≤ C₂ * ((x.length + 1) * (x.length + 1)) :=
        Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
      nlinarith) fun n => Nat.le_succ n
  simpa only [sq] using h

/-- `(n + 1) ^ k` is time-constructible for `k ≥ 2`. -/
theorem timeConstructible_succ_pow {k : ℕ} (hk : 2 ≤ k) :
    TimeConstructible fun n => (n + 1) ^ k := by
  induction k, hk using Nat.le_induction with
  | base => exact timeConstructible_succ_sq
  | succ k hk ih =>
    have h := ih.succ_mul fun n =>
      (Nat.le_succ n).trans (Nat.le_self_pow (by omega) _)
    simpa only [pow_succ', mul_comm] using h

/-! ### Space-constructible bounds -/

/-- A bound `s` is space-constructible when some machine with a binary alphabet and finitely many
states computes `s n` in binary from any word of length `n` within space `O(s n)`, halting
[Sipser, Definition 9.1][Sipser2013]. Unlike [Sipser, Definition 9.1][Sipser2013], `s n ≥ log n`
is not required here; the space hierarchy theorem asks for `n ≤ s n`. -/
def SpaceConstructible (s : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∃ t : ℕ → ℕ, ComputableInTimeAndSpaceOfLength (fun x : List Bool => s x.length) encBits
    encNat t fun n => c * s n + c

/-- A space-constructible bound is computed tidily within space `O(s n)`, within some time. -/
theorem SpaceConstructible.computableTidilyInO {s : ℕ → ℕ} (hs : SpaceConstructible s) :
    ∃ T, ComputableTidilyInO (fun x : List Bool => s x.length) encBits encNat T
      fun x => s x.length := by
  obtain ⟨c, t, h⟩ := hs
  obtain ⟨d, h⟩ := ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace h
  refine ⟨_, .of_bounds h (d * (c + 1) + 1) (T := fun x => 2 * t x.length +
    3 * (c * s x.length + c) + d) (fun x => ?_) (fun x => ?_) fun x => ?_⟩
  · exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (by omega))
  · dsimp only [encBits_apply]
    nlinarith
  · exact (Universal.length_encNat_le _).trans
      ((Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (by omega)))

/-- A time-constructible bound is space-constructible, since space is at most time. -/
theorem TimeConstructible.spaceConstructible {t : ℕ → ℕ} (ht : TimeConstructible t) :
    SpaceConstructible t := by
  obtain ⟨c, s, h⟩ := ht
  obtain ⟨k, h⟩ := ComputableInTimeAndSpace.exists_space_linear h
  exact ⟨k * c + k, fun n => c * t n + c, ComputableInTimeAndSpace.mono h (fun _ => le_rfl)
    fun x => by dsimp only; nlinarith⟩

/-- A tidy computation of `s n` in binary within space `O(s n)` makes `s` space-constructible:
it halts within a time bound of `n`, its number of configurations. -/
theorem SpaceConstructible.of_computableTidilyInO {s : ℕ → ℕ} {T S : List Bool → ℕ} (c : ℕ)
    (h : ComputableTidilyInO (fun x : List Bool => s x.length) encBits encNat T S)
    (hS : ∀ x, S x ≤ c * s x.length + c) : SpaceConstructible s := by
  obtain ⟨k, hk, -⟩ := h
  obtain ⟨t, ht⟩ := ComputableInTimeAndSpace.exists_time_of_length
    (s := fun n => k * (c * s n + c + 1)) (hk.computableInTimeAndSpace.mono (fun _ => le_rfl)
      fun x => Nat.mul_le_mul_left k (by have := hS x; simp only [encBits_apply]; omega))
  exact ⟨k * (c + 1), t, ComputableInTimeAndSpace.mono ht (fun _ => le_rfl) fun x => by
    dsimp only; nlinarith⟩

/-- `n` is space-constructible: count the length of the word in binary. -/
theorem spaceConstructible_id : SpaceConstructible fun n => n :=
  .of_computableTidilyInO 1 ComputableTidilyInO.lengthNat fun x => by omega

/-- `n + 1` is space-constructible. -/
theorem spaceConstructible_succ : SpaceConstructible fun n => n + 1 :=
  .of_computableTidilyInO 2 (ComputableTidilyInO.natSucc.comp ComputableTidilyInO.lengthNat)
    fun x => by have := Universal.length_encNat_le x.length; omega

/-- Constant bounds are space-constructible, in zero space. -/
theorem spaceConstructible_const (c : ℕ) : SpaceConstructible fun _ => c := by
  obtain ⟨t, h⟩ := computableInTimeAndSpace_of_const (α := List Bool) (encIn := encBits)
    (encOut := encNat) c
  exact ⟨0, fun _ => t, h.mono (fun _ => le_rfl) fun _ => Nat.zero_le _⟩

/-- `(n + 1) ^ k` is space-constructible. -/
theorem spaceConstructible_succ_pow (k : ℕ) : SpaceConstructible fun n => (n + 1) ^ k := by
  rcases k with _ | _ | k
  · simpa using spaceConstructible_const 1
  · simpa using spaceConstructible_succ
  · exact (timeConstructible_succ_pow (by omega)).spaceConstructible

/-- `2 ^ n` is space-constructible. -/
theorem spaceConstructible_two_pow : SpaceConstructible (2 ^ ·) :=
  timeConstructible_two_pow.spaceConstructible

end Cslib.Complexity
