/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Hierarchy
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Arith
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Deterministic time classes and the time hierarchy theorem

`Cslib.Complexity.DTIME enc t` consists of the problems that some machine with a binary alphabet
and finitely many states decides within time `c₁ * t n + c₂`, for constants `c₁` and `c₂`, on
instances whose encoding under `enc` has length `n`, with any space bound (upstream
`Turing.MultiTapeTM.DecidableInTimeAndSpace`) [Arora and Barak, Definition 1.12][AroraBarak09].
This is the definition of the classes proposed upstream in cslib pull request #767, stated for
encoded instances, with bounds that are functions of the length of the encoded instance. A bound
`t` is *time-constructible* (`Cslib.Complexity.TimeConstructible`) when such a machine computes
`t n` in binary from any word of length `n` within time `O(t n)`; so are `2 ^ n` and `(n + 1) ^ k`
for `k ≥ 2`.

## The time hierarchy theorem

`Cslib.Complexity.clockedDiagonal J` is the diagonal function `Cslib.Complexity.diagonal` with the
clock `J n` in place of `2 ^ n`: it runs the machine described at the start of its input `x` on `x`
for `J x.length` steps with the universal function, and negates the verdict.
`Cslib.Complexity.timeDiagonal J` applies it only when the framed description is short,
`2 ^ |unframe x| ≤ |x|` (`Cslib.Complexity.Diagonal.shortDesc`), and answers `false` otherwise.
Decoding a description of `L` bits takes time polynomial in `L`, of a degree fixed by the decoder,
hence `O(2 ^ L)`, which is `O(n)` on short descriptions; padded descriptions are short.

The native universal machine simulates `J` steps of a description of length `B` within time
`O(B ^ 5 * J ^ 3)` (`Cslib.Complexity.Diagonal.universal_bounds_le`), so the problem decided by
`timeDiagonal J` is in `DTIME ((n + 1) ^ 5 * (J n + 1) ^ 3)` for a time-constructible clock `J`
(`Cslib.Complexity.setOf_timeDiagonal_mem_DTIME`). It is not in `DTIME f` when every `c * f n + c`
is eventually below `J n`, by the diagonal argument
(`Cslib.Complexity.setOf_timeDiagonal_not_mem_DTIME`). Hence `DTIME f ⊂ DTIME g`
[Arora and Barak, Theorem 3.1][AroraBarak09], [Sipser, Theorem 9.10][Sipser2013]:

* when such a time-constructible clock `J` has `(n + 1) ^ 5 * (J n + 1) ^ 3 ≤ g n` eventually
  (`Cslib.Complexity.DTIME_ssubset_DTIME_of_clock`);
* when `f` is time-constructible, `n ≤ f n` and `(n + 1) ^ 8 * (f n + 1) ^ 3 ≤ g n` eventually,
  with the clock `(n + 1) * f n` (`Cslib.Complexity.DTIME_ssubset_DTIME`). As `n ≤ f n`, the gap
  `(f n + 1) ^ 11 ≤ g n` suffices.

The polynomial gap is the overhead of the native universal machine, which is polynomial in the
description and in the clock. The textbook gap `f n * log (f n) = o(g n)` needs a simulation with
logarithmic overhead and is not claimed here.

## Main definitions

* `Cslib.Complexity.DTIME`: deterministic time classes.
* `Cslib.Complexity.TimeConstructible`: time-constructible bounds.
* `Cslib.Complexity.clockedDiagonal`, `Cslib.Complexity.timeDiagonal`: the diagonal with a clock.

## Main results

* `Cslib.Complexity.setOf_timeDiagonal_mem_DTIME`,
  `Cslib.Complexity.setOf_timeDiagonal_not_mem_DTIME`: the clocked diagonal is decidable within
  the time of the universal machine, and not within time `O(f)` for clocks beyond every `O(f)`.
* `Cslib.Complexity.DTIME_ssubset_DTIME_of_clock`: the time hierarchy theorem, for a clock.
* `Cslib.Complexity.DTIME_ssubset_DTIME`: the time hierarchy theorem, for a time-constructible
  bound.
* `Cslib.Complexity.timeConstructible_two_pow`, `Cslib.Complexity.timeConstructible_succ_pow`,
  `Cslib.Complexity.TimeConstructible.succ_mul`: time-constructible bounds.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-! ### Lengths of words and numbers -/

/-- The word framed at the start of a word is no longer than the word. -/
theorem length_unframe_le : ∀ w : List Bool, (unframe w).length ≤ w.length
  | true :: _ :: v => by
    simp only [unframe, List.length_cons]
    have := length_unframe_le v
    omega
  | [] | [true] | false :: _ => by simp [unframe]

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

/-- The length of a bit word in unary, within quadratic time and linear space. -/
theorem lengthUnary : ComputableTidilyInO (fun l : List Bool => l.length) encBits encUnary
    (fun l => (l.length + 1) ^ 2) fun l => l.length + 1 := by
  have hstep := (ComputableTidilyInDegree.unary_succ.inO_one).comp (fst encUnary encBool)
  have hlen (x : List Bool) (i : ℕ) :
      (List.take i x).foldl (fun n _ => n + 1) 0 = min i x.length := by
    simp [List.foldl_const]
  have h := foldl (encA := encBool) (encL := encBits) (encB := encUnary) (list := id)
    (init := fun _ => 0) (step := fun n _ => n + 1) (of_linear (.of_eq fun _ => rfl)) (const 0)
    hstep (R := fun x => 3 * (x.length + 1)) (Q := fun x => 3 * (x.length + 1))
    (B := fun x => x.length)
    (fun x i hi => by
      simp only [id] at hi ⊢
      rw [hlen]
      simp only [length_encPair, encUnary_apply, List.length_replicate,
        encBool_apply, List.length_singleton]
      omega)
    (fun x i hi => by
      simp only [id] at hi ⊢
      rw [hlen]
      simp only [length_encPair, encUnary_apply, List.length_replicate,
        encBool_apply, List.length_singleton]
      omega)
    (fun x i hi => by
      simp only [id] at hi ⊢
      rw [hlen]
      simp only [encUnary_apply, List.length_replicate]
      omega)
  refine (h.mono 16 (fun x => ?_) fun x => ?_).of_enc_eq fun x => ?_
  · simp only [id, encBits_apply]
    nlinarith
  · simp only [id, encBits_apply]
    omega
  · simp [List.foldl_const]

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

/-! ### Halted runs -/

/-- A machine that computes `out` within time `t` has halted with output `out` after any number of
steps from `t` on. -/
theorem ComputesInTimeAndSpace.runFrom_of_le {k : ℕ} {Symbol State : Type*}
    {tm : MultiTapeTM k Symbol State} {x out : List Symbol} {t s J : ℕ}
    (h : tm.ComputesInTimeAndSpace x out t s) (hJ : t ≤ J) :
    (tm.runFrom (tm.initCfg x) J).Halted ∧ (tm.runFrom (tm.initCfg x) J).output = out := by
  obtain ⟨⟨u, hu, hout⟩, htime, -⟩ := h
  have hhalt := MultiTapeTM.runsInTime_iff_halted.mp htime
  rw [MultiTapeTM.runFrom_eq_of_halt tm _ hJ hhalt]
  refine ⟨hhalt, ?_⟩
  rcases le_total u t with hut | htu
  · exact (congrArg Cfg.output (MultiTapeTM.runFrom_eq_of_halt tm _ hut hu)).trans hout
  · exact (congrArg Cfg.output (MultiTapeTM.runFrom_eq_of_halt tm _ htu hhalt)).symm.trans hout

end Turing.MultiTapeTM

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Filter

variable {α : Type*}

/-! ### Time classes -/

/-- The problems decidable within time `O(t n)`, that is `c₁ * t n + c₂` for constants `c₁` and
`c₂`, on instances whose encoding under `enc` has length `n`, by a machine with a binary alphabet
and finitely many states, with any space bound. -/
def DTIME (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ c₁ c₂ : ℕ, ∃ s : ℕ → ℕ,
    DecidableInTimeAndSpace A enc (fun a => c₁ * t (enc a).length + c₂) fun a => s (enc a).length}

/-- `DTIME` is monotone in the time bound. -/
theorem DTIME_mono {enc : α ↪ List Bool} {t₁ t₂ : ℕ → ℕ} (h : ∀ n, t₁ n ≤ t₂ n) :
    DTIME enc t₁ ⊆ DTIME enc t₂ := by
  rintro A ⟨c₁, c₂, s, hA⟩
  exact ⟨c₁, c₂, s, ComputableInTimeAndSpace.mono hA
    (fun a => Nat.add_le_add_right (Nat.mul_le_mul_left _ (h _)) _) fun _ => le_rfl⟩

/-- `DTIME` only depends on the time bound eventually: the finitely many other values are absorbed
by the additive constant. -/
theorem DTIME_mono_of_eventually_le {enc : α ↪ List Bool} {t₁ t₂ : ℕ → ℕ}
    (h : ∀ᶠ n in atTop, t₁ n ≤ t₂ n) : DTIME enc t₁ ⊆ DTIME enc t₂ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  rintro A ⟨c₁, c₂, s, hA⟩
  refine ⟨c₁, c₁ * ∑ n ∈ Finset.range N, t₁ n + c₂, s,
    ComputableInTimeAndSpace.mono hA (fun a => ?_) fun _ => le_rfl⟩
  have : t₁ (enc a).length ≤ t₂ (enc a).length + ∑ n ∈ Finset.range N, t₁ n := by
    rcases le_or_gt N (enc a).length with h | h
    · have := hN _ h
      omega
    · have := Finset.single_le_sum (f := t₁) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr h)
      omega
  have := Nat.mul_le_mul_left c₁ this
  rw [Nat.mul_add] at this
  omega

/-- A Boolean function on words, tidily computable within bounds of the length of the word,
decides a problem within the corresponding time. -/
theorem setOf_mem_DTIME_of_computableTidilyInO {f : List Bool → Bool} {T S : List Bool → ℕ}
    {t s : ℕ → ℕ} (h : ComputableTidilyInO f encBits encBool T S) (hT : ∀ x, T x ≤ t x.length)
    (hS : ∀ x, S x ≤ s x.length) : {x | f x = true} ∈ DTIME encBits t := by
  obtain ⟨c, hc, -⟩ := h
  refine ⟨c, c, fun n => c * (s n + 1), decidableInTimeAndSpace_iff.mpr ⟨f, ?_, fun x => Iff.rfl⟩⟩
  refine hc.computableInTimeAndSpace.mono (fun x => ?_) fun x => ?_
  · simp only [encBits_apply]
    have := Nat.mul_le_mul_left c (hT x)
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · simp only [encBits_apply]
    exact Nat.mul_le_mul_left c (Nat.add_le_add_right (hS x) 1)

/-! ### Time-constructible bounds -/

/-- A bound `t` is time-constructible when some machine with a binary alphabet and finitely many
states computes `t n` in binary from any word of length `n` within time `O(t n)`. -/
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

/-! ### The clocked diagonal -/

/-- **The diagonal with clock `J`.** Run the machine described at the start of `x` on `x`, under the
coding `Turing.MultiTapeTM.Universal.eBit` of bits by `0` and `1`, for `J x.length` steps, and
return `false` exactly when it has halted with output `[true]`. -/
def clockedDiagonal (J : ℕ → ℕ) (x : List Bool) : Bool :=
  Diagonal.verdict (universal (decodeDesc (unframe x), x.map eBit, J x.length))

/-- The diagonal of `Cslib.Complexity.diagonal` has the clock `2 ^ n`. -/
theorem clockedDiagonal_two_pow : clockedDiagonal (2 ^ ·) = diagonal := rfl

/-- On its padded description, the clocked diagonal negates the answer of a machine that halts
within the clock. -/
theorem clockedDiagonal_desc {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) (pad : List Bool) (J : ℕ → ℕ) {b : Bool}
    (hhalt : (tm.runFrom (tm.initCfg (frame (eDesc (desc eS eBit tm)) ++ pad))
      (J (frame (eDesc (desc eS eBit tm)) ++ pad).length)).Halted)
    (hout : (tm.runFrom (tm.initCfg (frame (eDesc (desc eS eBit tm)) ++ pad))
      (J (frame (eDesc (desc eS eBit tm)) ++ pad).length)).output = [b]) :
    clockedDiagonal J (frame (eDesc (desc eS eBit tm)) ++ pad) = !b := by
  rw [clockedDiagonal, decodeDesc_unframe_frame_append, universal_desc, hout]
  simp only [List.map_cons, List.map_nil, Cfg.Halted] at hhalt ⊢
  rw [hhalt]
  cases b <;> simp [Diagonal.verdict, eBit]

namespace Diagonal

/-- The description framed at the start of `x` is *short*: `2 ^ |unframe x| ≤ |x|`. -/
def shortDesc (x : List Bool) : Bool := decide (2 ^ (unframe x).length ≤ x.length)

/-- Shortness compares the length of the description with the number of binary digits of the
length of the word. -/
theorem shortDesc_eq_decide (x : List Bool) :
    shortDesc x = decide ((unframe x).length + 1 ≤ (encNat x.length).length) := by
  rw [shortDesc, encNat_apply, Nat.size_eq_bits_len]
  exact decide_eq_decide.mpr (Nat.lt_size.symm.trans Nat.lt_iff_add_one_le)

/-- Shortness is decided within quadratic time and linear space. -/
theorem computableTidilyInO_shortDesc :
    ComputableTidilyInO shortDesc encBits encBool (fun x => (x.length + 1) ^ 2)
      fun x => x.length + 1 := by
  have hu : ComputableTidilyInO unframe encBits encBits (fun x => x.length) fun x => x.length :=
    ComputableTidilyInO.of_linear (.of_unframe fun _ => rfl)
  have ha := ComputableTidilyInDegree.unary_succ.inO_one.comp
    (ComputableTidilyInO.lengthUnary.comp hu)
  have hb := ComputableTidilyInO.lengthUnary.comp
    (ComputableTidilyInO.lengthNat.of_enc_eq (encOut := encBits)
      (g := fun x : List Bool => encNat x.length) fun _ => rfl)
  have h := ComputableTidilyInO.unaryLe.comp (ha.prod hb)
  refine (h.mono 64 (fun x => ?_) fun x => ?_).of_enc_eq fun x => ?_
  · have h₁ := length_unframe_le x
    have h₂ := Universal.length_encNat_le x.length
    simp only [Function.comp_apply, length_encPair, encUnary_apply,
      List.length_replicate] at h₁ h₂ ⊢
    nlinarith
  · have h₁ := length_unframe_le x
    have h₂ := Universal.length_encNat_le x.length
    simp only [Function.comp_apply, length_encPair, encUnary_apply,
      List.length_replicate] at h₁ h₂ ⊢
    omega
  · simp only [Function.comp_apply, shortDesc_eq_decide]

/-- The space of the universal run grows with the number of steps. -/
theorem runBound_le_succ (D N J : ℕ) : runBound D N J ≤ runBound D N (J + 1) := by
  simp only [runBound, ctxBound, cfgBound, tapeBound]
  gcongr <;> omega

/-- The numeric core of the resources of the clocked diagonal: for an input of length `n`, a
decoding time `A` linear in `n`, a decoded description of encoded length `D`, encoded symbols of
length `N`, a clock `J` of `L` binary digits and a result of encoded length `E`, everything is
within `K * (n + 1) ^ 5 * (J + 1) ^ 3` steps and cells. -/
theorem clockedBounds_aux (cA cD cO C₂ : ℕ) : ∃ K, ∀ {n A D N J L I E : ℕ},
    A ≤ cA * (n + 1) → D ≤ cD * (n + A + 1) → N ≤ 3 * n → (L + 1) ^ 2 ≤ C₂ * (J + 1) →
    I = 2 * D + 1 + (2 * N + 1 + L) →
    E ≤ cO * (n + A + (n + J) + (runBound D N J + I) + 1) →
    n + A + (n + J) + ((J + 1) * (stepBound D N J + runBound D N J + (L + 1) ^ 2) +
        (I + 1) ^ 2) + (E + 1) ^ 2 ≤ K * ((n + 1) ^ 5 * (J + 1) ^ 3) ∧
      n + A + (n + J) + (runBound D N J + I) + E ≤ K * ((n + 1) ^ 5 * (J + 1) ^ 3) := by
  set P := cD * (cA + 1) + 3 with hP
  set R := 5 * P + C₂ with hR
  set Q := cA + 4 + 200 * P ^ 2 + R with hQ
  refine ⟨cA + 3 + 100000 * P ^ 5 + C₂ + R ^ 2 + (cO * Q + 1) ^ 2 + 200 * P ^ 2 + R + cO * Q,
    fun {n A D N J L I E} hA hD hN hL hI hE => ?_⟩
  have hPn : P * (n + 1) = cD * (cA + 1) * (n + 1) + 3 * (n + 1) := by rw [hP]; ring
  have hD' : D ≤ cD * (cA + 1) * (n + 1) :=
    hD.trans ((Nat.mul_le_mul_left cD (show n + A + 1 ≤ (cA + 1) * (n + 1) by
      have : (cA + 1) * (n + 1) = cA * (n + 1) + (n + 1) := by ring
      omega)).trans (le_of_eq (by ring)))
  obtain ⟨hU₁, hU₂⟩ := universal_bounds_le (D := D) (N := N) (J := J + 1)
    (B := P * (n + 1) - 1) (L := 0) (by omega) (by omega) (Nat.zero_le _) (by omega)
  have hPX1 : 1 ≤ P * (n + 1) := by omega
  rw [Nat.sub_add_cancel hPX1] at hU₁ hU₂
  simp only [zero_add, one_pow] at hU₁
  have hstep := stepBound_mono (le_refl D) (le_refl N) (Nat.le_add_right J 1)
  have hrun := runBound_le_succ D N J
  have hD'' : D ≤ P * (n + 1) := by omega
  have hN' : N ≤ P * (n + 1) := by omega
  -- the monomials
  have hX1 : 1 ≤ n + 1 := by omega
  have hY1 : 1 ≤ J + 1 := by omega
  set W := (n + 1) ^ 5 * (J + 1) ^ 3 with hW
  set Z := (n + 1) ^ 2 * (J + 1) with hZ
  have hZ1 : 1 ≤ Z := Nat.mul_pos (Nat.pow_pos hX1) hY1
  have hXY : (n + 1) * (J + 1) ≤ W := Nat.mul_le_mul (Nat.le_self_pow (by norm_num) (n + 1))
    (Nat.le_self_pow (by norm_num) (J + 1))
  have hXYZ : (n + 1) * (J + 1) ≤ Z :=
    Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) (n + 1))
  have hZW : Z ≤ W := Nat.mul_le_mul (Nat.pow_le_pow_right hX1 (by omega))
    (Nat.le_self_pow (by norm_num) (J + 1))
  have hX2Y2 : (n + 1) ^ 2 * (J + 1) ^ 2 ≤ W := Nat.mul_le_mul (Nat.pow_le_pow_right hX1 (by omega))
    (Nat.pow_le_pow_right hY1 (by omega))
  have hX4Y2 : (n + 1) ^ 4 * (J + 1) ^ 2 ≤ W := Nat.mul_le_mul (Nat.pow_le_pow_right hX1 (by omega))
    (Nat.pow_le_pow_right hY1 (by omega))
  have hY2 : (J + 1) ^ 2 ≤ W := by
    have := Nat.mul_le_mul (Nat.one_le_pow 5 (n + 1) hX1)
      (Nat.pow_le_pow_right hY1 (show 2 ≤ 3 by omega))
    rwa [one_mul] at this
  -- the pieces
  have hU' : 100000 * (P * (n + 1)) ^ 5 * (J + 1) ^ 3 = 100000 * P ^ 5 * W := by rw [hW]; ring
  have hrunZ : runBound D N J ≤ 200 * P ^ 2 * Z := by
    have : 200 * (P * (n + 1)) ^ 2 * (J + 1) = 200 * P ^ 2 * Z := by rw [hZ]; ring
    omega
  have hLY : L ≤ C₂ * (J + 1) := (Nat.le_succ L).trans ((Nat.le_self_pow two_ne_zero _).trans hL)
  have hI1 : I + 1 ≤ R * ((n + 1) * (J + 1)) := by
    have h₁ : 5 * P * (n + 1) ≤ 5 * P * ((n + 1) * (J + 1)) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hY1)
    have h₂ : C₂ * (J + 1) ≤ C₂ * ((n + 1) * (J + 1)) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hX1)
    have e₁ : R * ((n + 1) * (J + 1)) =
        5 * P * ((n + 1) * (J + 1)) + C₂ * ((n + 1) * (J + 1)) := by
      rw [hR]; ring
    have e₂ : 5 * P * (n + 1) = 5 * (P * (n + 1)) := by ring
    omega
  have hpre : n + A + (n + J) ≤ (cA + 3) * ((n + 1) * (J + 1)) := by
    have h₁ : (cA + 2) * (n + 1) ≤ (cA + 2) * ((n + 1) * (J + 1)) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hY1)
    have h₂ : (J + 1) ≤ (n + 1) * (J + 1) := Nat.le_mul_of_pos_left _ hX1
    have e₁ : (cA + 3) * ((n + 1) * (J + 1)) =
        (cA + 2) * ((n + 1) * (J + 1)) + (n + 1) * (J + 1) := by ring
    have e₂ : (cA + 2) * (n + 1) = cA * (n + 1) + 2 * (n + 1) := by ring
    omega
  have hsum : n + A + (n + J) + (runBound D N J + I) + 1 ≤ Q * Z := by
    have h₁ := Nat.mul_le_mul_left (cA + 3) hXYZ
    have h₂ := Nat.mul_le_mul_left R hXYZ
    have e : Q * Z = (cA + 3) * Z + 200 * P ^ 2 * Z + R * Z + Z := by rw [hQ]; ring
    omega
  have hEZ : E ≤ cO * Q * Z :=
    hE.trans ((Nat.mul_le_mul_left cO hsum).trans (le_of_eq (by ring)))
  have hE1 : E + 1 ≤ (cO * Q + 1) * Z := by
    have e : (cO * Q + 1) * Z = cO * Q * Z + Z := by ring
    omega
  have hT₁ : (J + 1) * (stepBound D N J + runBound D N J + (L + 1) ^ 2) ≤
      100000 * P ^ 5 * W + C₂ * W := by
    have h₁ : (J + 1) * (stepBound D N J + runBound D N J) ≤
        (J + 1 + 1) * (stepBound D N (J + 1) + runBound D N (J + 1) + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h₂ : (J + 1) * (L + 1) ^ 2 ≤ C₂ * W := by
      calc (J + 1) * (L + 1) ^ 2 ≤ (J + 1) * (C₂ * (J + 1)) := Nat.mul_le_mul_left _ hL
        _ = C₂ * (J + 1) ^ 2 := by ring
        _ ≤ C₂ * W := Nat.mul_le_mul_left _ hY2
    rw [Nat.mul_add]
    omega
  have hI2 : (I + 1) ^ 2 ≤ R ^ 2 * W := by
    calc (I + 1) ^ 2 ≤ (R * ((n + 1) * (J + 1))) ^ 2 := Nat.pow_le_pow_left hI1 2
      _ = R ^ 2 * ((n + 1) ^ 2 * (J + 1) ^ 2) := by ring
      _ ≤ R ^ 2 * W := Nat.mul_le_mul_left _ hX2Y2
  have hE2 : (E + 1) ^ 2 ≤ (cO * Q + 1) ^ 2 * W := by
    calc (E + 1) ^ 2 ≤ ((cO * Q + 1) * Z) ^ 2 := Nat.pow_le_pow_left hE1 2
      _ = (cO * Q + 1) ^ 2 * ((n + 1) ^ 4 * (J + 1) ^ 2) := by rw [hZ]; ring
      _ ≤ (cO * Q + 1) ^ 2 * W := Nat.mul_le_mul_left _ hX4Y2
  have hpreW : n + A + (n + J) ≤ (cA + 3) * W := hpre.trans (Nat.mul_le_mul_left _ hXY)
  have hrunW : runBound D N J ≤ 200 * P ^ 2 * W := hrunZ.trans (Nat.mul_le_mul_left _ hZW)
  have hIW : I ≤ R * W := by
    have := hI1.trans (Nat.mul_le_mul_left R hXY)
    omega
  have hEW : E ≤ cO * Q * W := hEZ.trans (Nat.mul_le_mul_left _ hZW)
  have e : (cA + 3 + 100000 * P ^ 5 + C₂ + R ^ 2 + (cO * Q + 1) ^ 2 + 200 * P ^ 2 + R + cO * Q) *
      W = (cA + 3) * W + 100000 * P ^ 5 * W + C₂ * W + R ^ 2 * W + (cO * Q + 1) ^ 2 * W +
        200 * P ^ 2 * W + R * W + cO * Q * W := by ring
  rw [e]
  constructor <;> omega

end Diagonal

/-- **The clocked diagonal on short descriptions.** The clocked diagonal
`Cslib.Complexity.clockedDiagonal J` when the description framed at the start of `x` is short
(`Cslib.Complexity.Diagonal.shortDesc`), and `false` otherwise. -/
def timeDiagonal (J : ℕ → ℕ) (x : List Bool) : Bool :=
  if Diagonal.shortDesc x then clockedDiagonal J x else false

open Diagonal in
/-- **The clocked diagonal is computable within the time of the universal machine**: within time
and space `O((n + 1) ^ 5 * (J n + 1) ^ 3)` on inputs of length `n`, for a time-constructible clock
`J`, charging the shortness test, decoding, the symbols, the clock, the universal run and the
test. -/
theorem computableTidilyInO_timeDiagonal {J : ℕ → ℕ} (hJ : TimeConstructible J) :
    ComputableTidilyInO (timeDiagonal J) encBits encBool
      (fun x => (x.length + 1) ^ 5 * (J x.length + 1) ^ 3)
      fun x => (x.length + 1) ^ 5 * (J x.length + 1) ^ 3 := by
  obtain ⟨dd, ed, hdec⟩ := exists_computableTidilyInDegree_decodeDesc
  have hu : ComputableTidilyInO unframe encBits encBits (fun x => x.length) fun x => x.length :=
    ComputableTidilyInO.of_linear (.of_unframe fun _ => rfl)
  have hdesc := hdec.inO.comp hu
  have hsym := computableTidilyInDegree_map_eBit.inO_one
  have hclock := hJ.computableTidilyInO
  have hU := computableTidilyInO_universal.comp (hdesc.prod (hsym.prod hclock))
  have h := computableTidilyInO_shortDesc.ite (computableTidilyInO_verdict.comp hU)
    (ComputableTidilyInO.const (encMid := encBool) false)
  obtain ⟨cD, hcD⟩ := hdesc.length_le
  obtain ⟨cO, hcO⟩ := hU.length_le
  obtain ⟨cA, hcA⟩ := PolynomiallyBounded.exists_le_mul_two_pow (p := fun u => (u + 1) ^ dd)
    (by fun_prop)
  obtain ⟨C₂, hC₂⟩ := exists_pow_length_encNat_le 2
  obtain ⟨K, hK⟩ := clockedBounds_aux cA cD cO C₂
  have hbounds (x : List Bool) (hs : shortDesc x = true) := by
    have hA : ((unframe x).length + 1) ^ dd ≤ cA * (x.length + 1) :=
      (hcA _).trans (Nat.mul_le_mul_left _ ((of_decide_eq_true hs).trans (Nat.le_succ _)))
    have hN : (encList encUnary (x.map eBit)).length ≤ 3 * x.length :=
      (length_encList_le encUnary _ (b := 1) fun s hs => by
        obtain ⟨b, -, rfl⟩ := List.mem_map.mp hs
        cases b
        · exact Nat.zero_le _
        · exact le_rfl).trans (by rw [List.length_map]; omega)
    have hD := hcD x
    have hE := hcO x
    dsimp only [Function.comp_apply, encBits_apply] at hD hE
    exact hK (D := descLen (decodeDesc (unframe x))) hA hD hN (hC₂ _)
      (by rw [length_encPair, length_encPair]) hE
  have hW (x : List Bool) : x.length + 1 ≤ (x.length + 1) ^ 5 * (J x.length + 1) ^ 3 :=
    (Nat.le_self_pow (by norm_num) _).trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega)))
  have hW2 (x : List Bool) : (x.length + 1) ^ 2 ≤ (x.length + 1) ^ 5 * (J x.length + 1) ^ 3 :=
    (Nat.pow_le_pow_right (by omega) (by omega)).trans
      (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega)))
  refine h.mono (K + 2) (fun x => ?_) fun x => ?_
  · have e : (K + 2) * ((x.length + 1) ^ 5 * (J x.length + 1) ^ 3 + 1) =
        K * ((x.length + 1) ^ 5 * (J x.length + 1) ^ 3) +
          2 * ((x.length + 1) ^ 5 * (J x.length + 1) ^ 3) + K + 2 := by ring
    have := hW x
    have := hW2 x
    dsimp only [Function.comp_apply, encBits_apply]
    split_ifs with hs
    · have := (hbounds x hs).1
      omega
    · omega
  · have e : (K + 2) * ((x.length + 1) ^ 5 * (J x.length + 1) ^ 3 + 1) =
        K * ((x.length + 1) ^ 5 * (J x.length + 1) ^ 3) +
          2 * ((x.length + 1) ^ 5 * (J x.length + 1) ^ 3) + K + 2 := by ring
    have := hW x
    dsimp only [Function.comp_apply, encBits_apply]
    split_ifs with hs
    · have := (hbounds x hs).2
      omega
    · omega

/-- **The diagonal argument for time.** The problem of the clocked diagonal is not decidable within
time `O(f)` when every `c * f n + c` is eventually below the clock: on its own description, padded
to a short one beyond the point where the clock dominates, a machine deciding it would answer the
negation of its answer. -/
theorem setOf_timeDiagonal_not_mem_DTIME {f J : ℕ → ℕ}
    (hJ : ∀ c, ∀ᶠ n in atTop, c * f n + c ≤ J n) :
    {x | timeDiagonal J x = true} ∉ DTIME encBits f := by
  rintro ⟨c₁, c₂, s, hA⟩
  obtain ⟨g, ⟨k, State, hfinite, tm, htm⟩, hg⟩ := decidableInTimeAndSpace_iff.mp hA
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hJ (max c₁ c₂))
  -- the description, padded beyond `N` and to a length where it is short
  suffices ∀ pad : List Bool, N + 2 ^ (eDesc (desc eS eBit tm)).length ≤ pad.length → False from
    this (List.replicate _ false) (List.length_replicate ..).ge
  intro pad hpad
  have hpow := Nat.one_le_two_pow (n := (eDesc (desc eS eBit tm)).length)
  have hlen : (frame (eDesc (desc eS eBit tm)) ++ pad).length =
      2 * (eDesc (desc eS eBit tm)).length + 1 + pad.length := by
    rw [List.length_append, length_frame]
  have hshort : Diagonal.shortDesc (frame (eDesc (desc eS eBit tm)) ++ pad) = true := by
    rw [Diagonal.shortDesc, unframe_frame_append, hlen]
    exact decide_eq_true (by omega)
  have htime : c₁ * f (frame (eDesc (desc eS eBit tm)) ++ pad).length + c₂ ≤
      J (frame (eDesc (desc eS eBit tm)) ++ pad).length := by
    have := hN _ (show N ≤ (frame (eDesc (desc eS eBit tm)) ++ pad).length by omega)
    have h₁ : c₁ * f (frame (eDesc (desc eS eBit tm)) ++ pad).length ≤
        max c₁ c₂ * f (frame (eDesc (desc eS eBit tm)) ++ pad).length :=
      Nat.mul_le_mul_right _ (le_max_left _ _)
    have h₂ : c₂ ≤ max c₁ c₂ := le_max_right _ _
    omega
  obtain ⟨hhalt, hout⟩ := (htm _).runFrom_of_le htime
  have hd := clockedDiagonal_desc eS tm pad J hhalt hout
  have hgx := hg (frame (eDesc (desc eS eBit tm)) ++ pad)
  simp only [Set.mem_ofPred_eq, timeDiagonal, hshort, ↓reduceIte, hd] at hgx
  revert hgx
  cases g (frame (eDesc (desc eS eBit tm)) ++ pad) <;> decide

/-- The problem of the clocked diagonal is decidable within time
`O((n + 1) ^ 5 * (J n + 1) ^ 3)`. -/
theorem setOf_timeDiagonal_mem_DTIME {J : ℕ → ℕ} (hJ : TimeConstructible J) :
    {x | timeDiagonal J x = true} ∈ DTIME encBits fun n => (n + 1) ^ 5 * (J n + 1) ^ 3 :=
  setOf_mem_DTIME_of_computableTidilyInO (computableTidilyInO_timeDiagonal hJ)
    (t := fun n => (n + 1) ^ 5 * (J n + 1) ^ 3) (s := fun n => (n + 1) ^ 5 * (J n + 1) ^ 3)
    (fun _ => le_rfl) fun _ => le_rfl

/-! ### The time hierarchy theorem -/

/-- **The time hierarchy theorem, for a clock.** If a time-constructible clock `J` eventually
exceeds every `c * f n + c`, then `DTIME f` is strictly contained in every `DTIME g` with
`(n + 1) ^ 5 * (J n + 1) ^ 3 ≤ g n` eventually [Arora and Barak, Theorem 3.1][AroraBarak09]. -/
theorem DTIME_ssubset_DTIME_of_clock {f g J : ℕ → ℕ} (hJ : TimeConstructible J)
    (hfJ : ∀ c, ∀ᶠ n in atTop, c * f n + c ≤ J n)
    (hg : ∀ᶠ n in atTop, (n + 1) ^ 5 * (J n + 1) ^ 3 ≤ g n) :
    DTIME encBits f ⊂ DTIME encBits g := by
  have hsub : DTIME encBits f ⊆ DTIME encBits g := DTIME_mono_of_eventually_le <| by
    filter_upwards [hfJ 1, hg] with n h₁ h₂
    have : J n ≤ (n + 1) ^ 5 * (J n + 1) ^ 3 :=
      (Nat.le_succ _).trans ((Nat.le_self_pow (by norm_num) _).trans
        (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))))
    omega
  exact (Set.ssubset_iff_of_subset hsub).mpr ⟨_,
    DTIME_mono_of_eventually_le hg (setOf_timeDiagonal_mem_DTIME hJ),
    setOf_timeDiagonal_not_mem_DTIME hfJ⟩

/-- **The time hierarchy theorem.** If `f` is time-constructible and `n ≤ f n`, then `DTIME f` is
strictly contained in every `DTIME g` with `(n + 1) ^ 8 * (f n + 1) ^ 3 ≤ g n` eventually
[Arora and Barak, Theorem 3.1][AroraBarak09], [Sipser, Theorem 9.10][Sipser2013]. The gap is the
polynomial overhead of the native universal machine, not the textbook `f n * log (f n)`. -/
theorem DTIME_ssubset_DTIME {f g : ℕ → ℕ} (hf : TimeConstructible f) (hn : ∀ n, n ≤ f n)
    (hg : ∀ᶠ n in atTop, (n + 1) ^ 8 * (f n + 1) ^ 3 ≤ g n) :
    DTIME encBits f ⊂ DTIME encBits g := by
  refine DTIME_ssubset_DTIME_of_clock (hf.succ_mul hn) (fun c => ?_) (hg.mono fun n h => ?_)
  · filter_upwards [eventually_ge_atTop c] with n hc
    have := hn n
    have : c * f n ≤ n * f n := Nat.mul_le_mul_right _ hc
    rw [Nat.succ_mul]
    omega
  · refine le_trans ?_ h
    calc (n + 1) ^ 5 * ((n + 1) * f n + 1) ^ 3 ≤ (n + 1) ^ 5 * ((n + 1) * (f n + 1)) ^ 3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by rw [Nat.mul_succ]; omega) 3)
      _ = (n + 1) ^ 8 * (f n + 1) ^ 3 := by ring

end Cslib.Complexity
