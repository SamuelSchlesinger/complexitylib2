/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.HardnessAmplification
public import Complexity.Computability.Circuit.Boolean.HardnessAmplification.WorstCase
public import Complexity.Computability.Languages.Slice
public import Complexity.Computability.Circuit.Boolean.Substitution
public import Complexity.Foundations.FieldTheory.Finite.BinaryField
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Exponential worst-case hardness gives exponential average-case hardness

Let `L` be a language whose slices need De Morgan circuits of size `2 ^ (γ n)` for all large `n`.
This module encodes the slices of `L` with the reconstruction theorem of Sudan, Trevisan and
Vadhan (`Cslib.Circuits.Boolean.complexity_le_pow_of_agree_hardnessEncode`) along a concrete
schedule of parameters, and proves that the encoded language is average-case hard for circuits
of size `2 ^ ⌊N / c⌋` at all large lengths `N`
(`Cslib.Circuits.Boolean.eventually_isAverageCaseHard_encodedSlice`).

**The schedule.** Let `M = ⌈40 / γ⌉ + 1` (`Cslib.Circuits.Boolean.blockFactor`). At length `N`,
the block length is `b = ⌊N / (4 (M + 1))⌋` (`Cslib.Circuits.Boolean.blockLength`); the slice of
`L` at length `n = M b` is encoded over the explicit binary field of degree `w = 4 b`
(`Cslib.BinaryField`), with `b`-bit blocks embedded as polynomials of degree less than `b`. The
encoding has `(M + 1) w ≤ N` input bits; the remaining input bits are ignored
(`Cslib.Circuits.Boolean.encodedSlice`), and the encoded slices form the encoded language
(`Cslib.Circuits.Boolean.encodedLanguage`). For the hardness `s = 2 ^ σ`, `σ = ⌊N / c⌋` with
`c = 200 (M + 1)` (`Cslib.Circuits.Boolean.hardnessDivisor`), the parameters of the
reconstruction are `K = 2 σ + ⌊log₂ w⌋ + 2` masks, the Sudan parameter `D = 2 ^ (3 b - ⌊b / 4⌋)`
and majority trees of depth `L = ⌊log₂ (M b)⌋ + 1`.

**The argument.** A circuit of size `s` agreeing with the slice at length `N` on a `1 / 2 + 1 / s`
fraction gives, after fixing the ignored bits
(`Cslib.Circuits.Boolean.exists_complexity_le_of_agree_prefix`), a circuit of size `s + 2` with
the same agreement with the encoding, and the reconstruction
theorem turns it into a circuit for the slice of `L` at length `M b` with at most
`2 ^ 27 * M ^ 3 * b ^ 6 * 2 ^ (36 b + 5 σ) < 2 ^ (40 b) ≤ 2 ^ (γ M b)` gates, for large `b`
(`Cslib.Circuits.Boolean.isAverageCaseHard_encodedSlice_of`): a contradiction.

The hardness is eventual: it holds at all large lengths `N`, from worst-case hardness at all large
lengths `n`. Worst-case hardness at infinitely many lengths gives average-case hardness only at the
corresponding infinitely many encoded lengths, which is not what
`Cslib.Complexity.P_eq_BPP_of_isAverageCaseHard` assumes.

## Main definitions

* `Cslib.Circuits.Boolean.blockFactor`, `Cslib.Circuits.Boolean.hardnessDivisor`,
  `Cslib.Circuits.Boolean.blockLength`: the schedule.
* `Cslib.Circuits.Boolean.encodedSlice`: the encoded slice at length `N`.
* `Cslib.Circuits.Boolean.encodedLanguage`: the language of the encoded slices.

## Main results

* `Cslib.Circuits.Boolean.exists_complexity_le_of_agree_prefix`: fixing ignored input bits.
* `Cslib.Circuits.Boolean.isAverageCaseHard_encodedSlice_of`: hardness at one length.
* `Cslib.Circuits.Boolean.eventually_isAverageCaseHard_encodedSlice`: **exponential worst-case
  hardness gives exponential average-case hardness**.

## References

* [M. Sudan, L. Trevisan, S. Vadhan, *Pseudorandom generators without the XOR lemma*]
  [SudanTrevisanVadhan2001]
* [R. Impagliazzo, A. Wigderson, *P = BPP if E requires exponential circuits: Derandomizing the
  XOR lemma*][ImpagliazzoWigderson1997]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Finset Filter Cslib.Code

/-! ### The schedule -/

/-- The block factor `M = ⌈40 / γ⌉ + 1` for the hardness exponent `γ`. -/
noncomputable def blockFactor (γ : ℝ) : ℕ := ⌈40 / γ⌉₊ + 1

/-- The divisor `c = 200 (M + 1)` of the average-case hardness exponent. -/
noncomputable def hardnessDivisor (γ : ℝ) : ℕ := 200 * (blockFactor γ + 1)

/-- The block length `b = ⌊N / (4 (M + 1))⌋` at input length `N`. -/
def blockLength (M N : ℕ) : ℕ := N / (4 * (M + 1))

/-- The encoding at length `N` reads at most `N` input bits: `(M + 1) w ≤ N` for `w = 4 b`. -/
theorem encodedLength_le (M N : ℕ) : M * (4 * blockLength M N) + 4 * blockLength M N ≤ N := by
  have := Nat.div_mul_le_self N (4 * (M + 1))
  unfold blockLength
  nlinarith

/-- **The encoded slice at length `N`**: the encoding of the slice of `L` at length `M b` over the
explicit binary field of degree `w = 4 b`, read from the first `(M + 1) w` input bits, where
`b = blockLength M N`; constant when `b = 0`. -/
noncomputable def encodedSlice (L : Language Bool) (M N : ℕ) : BooleanFunction N :=
  if hb : blockLength M N = 0 then fun _ => false else
    fun y => hardnessEncode (BinaryField.equivBits (w := 4 * blockLength M N) (by omega))
      (BinaryField.embed (by omega) (by omega)) (L.slice (M * blockLength M N))
      (fun i => y (Fin.castLE (encodedLength_le M N) i))

/-- **The encoded language**: its slice at each length `N` is the encoded slice
`encodedSlice L M N`. -/
noncomputable def encodedLanguage (L : Language Bool) (M : ℕ) : Language Bool :=
  Language.ofSlices (encodedSlice L M)

/-- The slices of the encoded language are the encoded slices. -/
@[simp]
theorem slice_encodedLanguage (L : Language Bool) (M N : ℕ) :
    (encodedLanguage L M).slice N = encodedSlice L M N :=
  Language.slice_ofSlices _ N

/-! ### Fixing ignored input bits -/

/-- The input of `N` bits with prefix `x` and suffix `z`. -/
private def joinBits {N Ne : ℕ} (hle : Ne ≤ N) (x : BitString Ne) (z : BitString (N - Ne)) :
    BitString N :=
  fun k => if h : (k : ℕ) < Ne then x ⟨k, h⟩ else z ⟨k - Ne, by omega⟩

/-- **Fixing ignored input bits.** If `g` on `N` bits agrees with a function `E` of the first `Ne`
input bits on more than `δ * 2 ^ N` inputs, then fixing the remaining bits suitably gives a
function on `Ne` bits, of complexity at most two more, agreeing with `E` on more than
`δ * 2 ^ Ne` inputs. -/
theorem exists_complexity_le_of_agree_prefix {N Ne : ℕ} (hle : Ne ≤ N) (E : BooleanFunction Ne)
    (g : BooleanFunction N) {δ : ℝ}
    (hagree : δ * 2 ^ N < #{y | g y = E fun i => y (Fin.castLE hle i)}) :
    ∃ C : BooleanFunction Ne, complexity interpretation (single C) ≤
      complexity interpretation (single g) + 2 ∧ δ * 2 ^ Ne < #{x | C x = E x} := by
  classical
  -- the agreement splits over the suffixes
  have hsplit : #{y | g y = E fun i => y (Fin.castLE hle i)} =
      ∑ z : BitString (N - Ne), #{x | g (joinBits hle x z) = E x} := by
    rw [← card_sigma]
    refine card_nbij' (fun y => ⟨fun k : Fin (N - Ne) => y ⟨Ne + k, by omega⟩,
      fun i => y (Fin.castLE hle i)⟩) (fun p => joinBits hle p.2 p.1) (fun y hy => ?_)
      (fun p hp => ?_) (fun y _ => ?_) (fun p _ => ?_)
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, coe_sigma, Set.mem_sigma_iff,
        mem_coe] at hy ⊢
      have : joinBits hle (fun i => y (Fin.castLE hle i))
          (fun k : Fin (N - Ne) => y ⟨Ne + k, by omega⟩) = y := by
        funext k
        simp only [joinBits]
        split_ifs with h
        · rfl
        · congr 1
          ext
          simp only
          omega
      rw [this]
      exact hy
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, coe_sigma, Set.mem_sigma_iff,
        mem_coe] at hp ⊢
      have : (fun i => joinBits hle p.2 p.1 (Fin.castLE hle i)) = p.2 := by
        funext i
        simp [joinBits, i.2]
      rw [this]
      exact hp
    · funext k
      simp only [joinBits]
      split_ifs with h
      · rfl
      · congr 1
        ext
        simp only
        omega
    · obtain ⟨z, x⟩ := p
      simp only [Sigma.mk.injEq]
      refine ⟨?_, ?_⟩
      · funext k
        simp [joinBits]
      · refine heq_of_eq (funext fun i => ?_)
        simp [joinBits, i.2]
  -- some suffix carries at least the average agreement
  have hex : ∃ z : BitString (N - Ne), δ * 2 ^ Ne < #{x | g (joinBits hle x z) = E x} := by
    by_contra hall
    push Not at hall
    have hsum : (#{y | g y = E fun i => y (Fin.castLE hle i)} : ℝ) ≤
        ∑ _z : BitString (N - Ne), δ * 2 ^ Ne := by
      rw [hsplit, Nat.cast_sum]
      exact sum_le_sum fun z _ => hall z
    rw [sum_const, card_univ, nsmul_eq_mul] at hsum
    have hcard : (Fintype.card (BitString (N - Ne)) : ℝ) * (δ * 2 ^ Ne) = δ * 2 ^ N := by
      simp only [BitString, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
        Nat.cast_ofNat]
      rw [mul_left_comm, ← pow_add, Nat.sub_add_cancel hle]
    linarith
  obtain ⟨z, hz⟩ := hex
  -- the hardwiring substitution
  let ρ : Fin N → Fin Ne ⊕ Bool := fun k =>
    if h : (k : ℕ) < Ne then .inl ⟨k, h⟩ else .inr (z ⟨k - Ne, by omega⟩)
  have hsub : ∀ x, substitute ρ x = joinBits hle x z := fun x => by
    funext k
    simp only [substitute, ρ, joinBits]
    split_ifs <;> rfl
  refine ⟨fun x => g (substitute ρ x), complexity_substitute_le ρ g, ?_⟩
  simpa only [hsub] using hz

/-! ### The numeric hypotheses of the reconstruction -/

/-- `3 ^ (⌊log₂ x⌋ + 1) ≤ 3 x ^ 2` for `x > 0`. -/
private theorem three_pow_log_le {x : ℕ} (hx : 0 < x) : 3 ^ (Nat.log 2 x + 1) ≤ 3 * x ^ 2 := by
  have h1 : 3 ^ Nat.log 2 x ≤ 4 ^ Nat.log 2 x := Nat.pow_le_pow_left (by norm_num) _
  have h2 : 4 ^ Nat.log 2 x = (2 ^ Nat.log 2 x) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have h3 : 2 ^ Nat.log 2 x ≤ x := Nat.pow_log_le_self 2 hx.ne'
  rw [pow_succ]
  calc 3 ^ Nat.log 2 x * 3 ≤ (2 ^ Nat.log 2 x) ^ 2 * 3 := by rw [← h2]; gcongr
    _ ≤ x ^ 2 * 3 := by gcongr
    _ = 3 * x ^ 2 := by ring

/-- The polynomial bounds used by the schedule, from the single eventual inequality. -/
private theorem schedule_bounds {M b : ℕ} (hb : 1 ≤ b)
    (hev : (2 ^ 27 * M ^ 3 + 4608 * M + 128) * b ^ 6 ≤ 2 ^ (b / 4)) :
    2 * M ≤ 2 ^ (b / 2) ∧ 128 * b ≤ 2 ^ (b / 4) ∧ 4608 * M * b ≤ 2 ^ (b / 4) ∧
      36 * M ≤ 2 ^ (b / 4) ∧ 2 ^ 27 * M ^ 3 * b ^ 6 ≤ 2 ^ (b / 4) := by
  have hb6 : b ≤ b ^ 6 := Nat.le_self_pow (by norm_num) b
  have hP1 : 128 ≤ 2 ^ 27 * M ^ 3 + 4608 * M + 128 := Nat.le_add_left _ _
  have hP2 : 4608 * M ≤ 2 ^ 27 * M ^ 3 + 4608 * M + 128 :=
    (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  have hP3 : 2 ^ 27 * M ^ 3 ≤ 2 ^ 27 * M ^ 3 + 4608 * M + 128 :=
    (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  have hB : 128 * b ≤ 2 ^ (b / 4) := (Nat.mul_le_mul hP1 hb6).trans hev
  have hD : 4608 * M * b ≤ 2 ^ (b / 4) := (Nat.mul_le_mul hP2 hb6).trans hev
  have hF : 2 ^ 27 * M ^ 3 * b ^ 6 ≤ 2 ^ (b / 4) := (Nat.mul_le_mul_right _ hP3).trans hev
  have hE : 36 * M ≤ 2 ^ (b / 4) := by
    have : 4608 * M * 1 ≤ 4608 * M * b := Nat.mul_le_mul_left _ hb
    omega
  have hA : 2 * M ≤ 2 ^ (b / 2) :=
    calc 2 * M ≤ 2 ^ (b / 4) := by omega
      _ ≤ 2 ^ (b / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact ⟨hA, hB, hD, hE, hF⟩

/-- `2 ^ K = 4 ^ σ * 4 * 2 ^ ⌊log₂ (4 b)⌋` for the number of masks `K`. -/
private theorem two_pow_masks (σ b : ℕ) :
    2 ^ (2 * σ + Nat.log 2 (4 * b) + 2) = 4 ^ σ * 4 * 2 ^ Nat.log 2 (4 * b) := by
  rw [pow_add, pow_add, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
  ring

private theorem two_pow_masks_le (σ : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    2 ^ (2 * σ + Nat.log 2 (4 * b) + 2) ≤ 16 * b * 4 ^ σ := by
  rw [two_pow_masks]
  calc 4 ^ σ * 4 * 2 ^ Nat.log 2 (4 * b) ≤ 4 ^ σ * 4 * (4 * b) :=
        Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 (by omega))
    _ = 16 * b * 4 ^ σ := by ring

private theorem two_pow_masks_ge (σ b : ℕ) :
    2 * (4 * b) * 4 ^ σ + 1 ≤ 2 ^ (2 * σ + Nat.log 2 (4 * b) + 2) := by
  rw [two_pow_masks]
  have h : 4 * b < 2 ^ (Nat.log 2 (4 * b) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  rw [pow_succ] at h
  have h4 : 1 ≤ 4 ^ σ := Nat.one_le_pow _ _ (by norm_num)
  have h' : 2 * (4 * b) + 2 ≤ 4 * 2 ^ Nat.log 2 (4 * b) := by omega
  calc 2 * (4 * b) * 4 ^ σ + 1 ≤ 2 * (4 * b) * 4 ^ σ + 2 * 4 ^ σ := by omega
    _ = (2 * (4 * b) + 2) * 4 ^ σ := by ring
    _ ≤ 4 * 2 ^ Nat.log 2 (4 * b) * 4 ^ σ := Nat.mul_le_mul_right _ h'
    _ = 4 ^ σ * 4 * 2 ^ Nat.log 2 (4 * b) := by ring

/-- The hypothesis on the number of masks for Goldreich–Levin decoding. -/
private theorem masks_size {w σ K : ℕ} (hK : 2 * w * 4 ^ σ + 1 ≤ 2 ^ K) :
    (w : ℝ) ≤ 2 * (1 / ((2 ^ σ : ℕ) : ℝ) / 2) ^ 2 * ((2 ^ K - 1 : ℕ) : ℝ) := by
  have hcast : (2 * w * 4 ^ σ : ℝ) ≤ ((2 ^ K - 1 : ℕ) : ℝ) := by
    have : 2 * w * 4 ^ σ ≤ 2 ^ K - 1 := by omega
    exact_mod_cast this
  have hpos : (0 : ℝ) < 2 ^ σ := by positivity
  have h4 : (2 : ℝ) * (1 / ((2 ^ σ : ℕ) : ℝ) / 2) ^ 2 * (2 * w * 4 ^ σ) = w := by
    rw [show (4 : ℝ) ^ σ = (2 ^ σ) ^ 2 by rw [← pow_mul, mul_comm σ 2, pow_mul]; norm_num]
    push_cast
    field_simp
  calc (w : ℝ) = 2 * (1 / ((2 ^ σ : ℕ) : ℝ) / 2) ^ 2 * (2 * w * 4 ^ σ) := h4.symm
    _ ≤ 2 * (1 / ((2 ^ σ : ℕ) : ℝ) / 2) ^ 2 * ((2 ^ K - 1 : ℕ) : ℝ) := by gcongr

/-- The hypothesis that there are more monomials than field elements. -/
private theorem card_lt_card_monomials {M b : ℕ} (hM : 1 ≤ M) (hb : 1 ≤ b)
    (hA : 2 * M ≤ 2 ^ (b / 2)) :
    2 ^ (4 * b) < #(Sudan.monomials (M * (2 ^ b - 1)) (2 ^ (3 * b - b / 4))) := by
  have h2b : 2 ≤ 2 ^ b :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  set d := M * (2 ^ b - 1) with hd
  set D := 2 ^ (3 * b - b / 4) with hD
  have hd1 : 1 ≤ d := Nat.mul_pos (by omega) (by omega)
  have hdlt : d < M * 2 ^ b := mul_lt_mul_of_pos_left (by omega) (by omega)
  have hmon := Sudan.add_one_mul_add_two_le_two_mul_mul_card_monomials hd1 D
  have hDsq : 2 ^ (6 * b - b / 2) ≤ D * D := by
    rw [hD, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2dq : 2 * d * 2 ^ (4 * b) < 2 ^ (6 * b - b / 2) :=
    calc 2 * d * 2 ^ (4 * b) < 2 * (M * 2 ^ b) * 2 ^ (4 * b) :=
          mul_lt_mul_of_pos_right (by omega) (by positivity)
      _ = 2 * M * 2 ^ (b + 4 * b) := by rw [pow_add]; ring
      _ ≤ 2 ^ (b / 2) * 2 ^ (b + 4 * b) := Nat.mul_le_mul_right _ hA
      _ = 2 ^ (b / 2 + (b + 4 * b)) := (pow_add 2 (b / 2) (b + 4 * b)).symm
      _ ≤ 2 ^ (6 * b - b / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlt : 2 * d * 2 ^ (4 * b) < 2 * d * #(Sudan.monomials d D) :=
    calc 2 * d * 2 ^ (4 * b) < D * D := h2dq.trans_le hDsq
      _ ≤ (D + 1) * (D + 2) := Nat.mul_le_mul (by omega) (by omega)
      _ ≤ 2 * d * #(Sudan.monomials d D) := hmon
  exact lt_of_mul_lt_mul_left hlt (Nat.zero_le _)

/-- The agreement margin `2 ^ (K + 3) D ≤ q ε` of the line decoder. -/
private theorem margin_le {b σ : ℕ} (hb : 1 ≤ b) (hB : 128 * b ≤ 2 ^ (b / 4))
    (h3σ : 3 * σ ≤ b) :
    (2 : ℝ) ^ (2 * σ + Nat.log 2 (4 * b) + 2 + 3) * ((2 ^ (3 * b - b / 4) : ℕ) : ℝ) ≤
      ((2 ^ (4 * b) : ℕ) : ℝ) * (1 / ((2 ^ σ : ℕ) : ℝ)) := by
  have hnat : 2 ^ (2 * σ + Nat.log 2 (4 * b) + 2 + 3) * 2 ^ (3 * b - b / 4) * 2 ^ σ ≤
      2 ^ (4 * b) :=
    calc 2 ^ (2 * σ + Nat.log 2 (4 * b) + 2 + 3) * 2 ^ (3 * b - b / 4) * 2 ^ σ
        = 2 ^ (2 * σ + Nat.log 2 (4 * b) + 2) * 8 * 2 ^ (3 * b - b / 4) * 2 ^ σ := by
          rw [pow_add _ _ 3, show (2 : ℕ) ^ 3 = 8 by norm_num]
      _ ≤ 16 * b * 4 ^ σ * 8 * 2 ^ (3 * b - b / 4) * 2 ^ σ := by
          gcongr
          exact two_pow_masks_le σ hb
      _ = 128 * b * 2 ^ (3 * σ) * 2 ^ (3 * b - b / 4) := by
          rw [show 3 * σ = 2 * σ + σ by ring, pow_add, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
          ring
      _ ≤ 2 ^ (b / 4) * 2 ^ b * 2 ^ (3 * b - b / 4) := by
          gcongr
      _ = 2 ^ (4 * b) := by
          rw [← pow_add, ← pow_add]
          congr 1
          omega
  have hpos : (0 : ℝ) < ((2 ^ σ : ℕ) : ℝ) := by positivity
  rw [mul_one_div, le_div_iff₀ hpos]
  exact_mod_cast hnat

/-- The bound on the errors left for self-correction. -/
private theorem errors_le {M b σ : ℕ} (hM : 1 ≤ M) (hb : 1 ≤ b)
    (hD' : 4608 * M * b ≤ 2 ^ (b / 4)) (hE : 36 * M ≤ 2 ^ (b / 4)) (h3σ : 3 * σ ≤ b) :
    6 * (((M * (2 ^ b - 1) : ℕ) : ℝ) + 1) * (1 / ((2 ^ (4 * b) : ℕ) : ℝ) ^ M +
      2 ^ (2 * σ + Nat.log 2 (4 * b) + 2 + 4) /
        (((2 ^ (4 * b) : ℕ) : ℝ) * (1 / ((2 ^ σ : ℕ) : ℝ))) +
      ((2 ^ (3 * b - b / 4) : ℕ) : ℝ) / (((2 ^ (4 * b) : ℕ) : ℝ) - 1)) ≤ 1 := by
  have h2b : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hMle : M ≤ M * 2 ^ b := Nat.le_mul_of_pos_right _ (by positivity)
  set q := 2 ^ (4 * b) with hq
  set d := M * (2 ^ b - 1) with hd
  set K := 2 * σ + Nat.log 2 (4 * b) + 2 with hK
  set D := 2 ^ (3 * b - b / 4) with hD
  have hd1 : d + 1 ≤ M * 2 ^ b := by
    rw [hd, Nat.mul_sub_one]
    omega
  have hq18 : 18 * (d + 1) ≤ q := by
    have h18 : 18 * M ≤ 2 ^ (3 * b) :=
      calc 18 * M ≤ 2 ^ (b / 4) := by omega
        _ ≤ 2 ^ (3 * b) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 18 * (d + 1) ≤ 18 * (M * 2 ^ b) := Nat.mul_le_mul_left _ hd1
      _ = 18 * M * 2 ^ b := by ring
      _ ≤ 2 ^ (3 * b) * 2 ^ b := Nat.mul_le_mul_right _ h18
      _ = q := by rw [hq, ← pow_add]; congr 1; ring
  have hT1 : 18 * (d + 1) ≤ q ^ M := hq18.trans (Nat.le_self_pow (by omega) q)
  have hT2 : 18 * (d + 1) * 2 ^ (K + 4) * 2 ^ σ ≤ q :=
    calc 18 * (d + 1) * 2 ^ (K + 4) * 2 ^ σ
        ≤ 18 * (M * 2 ^ b) * (16 * b * 4 ^ σ * 16) * 2 ^ σ := by
          rw [pow_add _ K 4, show (2 : ℕ) ^ 4 = 16 by norm_num]
          gcongr
          exact two_pow_masks_le σ hb
      _ = 4608 * M * b * 2 ^ b * 2 ^ (3 * σ) := by
          rw [show 3 * σ = 2 * σ + σ by ring, pow_add, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
          ring
      _ ≤ 2 ^ (b / 4) * 2 ^ b * 2 ^ b := by
          gcongr
      _ = 2 ^ (b / 4 + b + b) := by rw [pow_add, pow_add]
      _ ≤ q := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hT3 : 18 * (d + 1) * D + 1 ≤ q := by
    have h1 : 18 * (d + 1) * D ≤ 18 * M * 2 ^ (4 * b - b / 4) :=
      calc 18 * (d + 1) * D ≤ 18 * (M * 2 ^ b) * D := by gcongr
        _ = 18 * M * 2 ^ (b + (3 * b - b / 4)) := by rw [hD, pow_add]; ring
        _ = 18 * M * 2 ^ (4 * b - b / 4) := by congr 2; omega
    have h2 : 36 * M * 2 ^ (4 * b - b / 4) ≤ q :=
      calc 36 * M * 2 ^ (4 * b - b / 4) ≤ 2 ^ (b / 4) * 2 ^ (4 * b - b / 4) := by gcongr
        _ = q := by rw [hq, ← pow_add]; congr 1; omega
    have h3 : 1 ≤ 18 * M * 2 ^ (4 * b - b / 4) := Nat.one_le_iff_ne_zero.2 (by positivity)
    linarith
  have hq1 : (1 : ℝ) < q := by
    have : 2 ≤ q :=
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (4 * b) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast this
  have hdpos : (0 : ℝ) < 18 * ((d : ℝ) + 1) := by positivity
  have e1 : 1 / (q : ℝ) ^ M ≤ 1 / (18 * ((d : ℝ) + 1)) := by
    apply one_div_le_one_div_of_le hdpos
    exact_mod_cast hT1
  have e2 : (2 : ℝ) ^ (K + 4) / ((q : ℝ) * (1 / ((2 ^ σ : ℕ) : ℝ))) ≤
      1 / (18 * ((d : ℝ) + 1)) := by
    rw [mul_one_div, div_div_eq_mul_div, div_le_div_iff₀ (by linarith) hdpos, one_mul]
    have : ((18 * (d + 1) * 2 ^ (K + 4) * 2 ^ σ : ℕ) : ℝ) ≤ q := by exact_mod_cast hT2
    push_cast at this ⊢
    linarith
  have e3 : (D : ℝ) / ((q : ℝ) - 1) ≤ 1 / (18 * ((d : ℝ) + 1)) := by
    rw [div_le_div_iff₀ (by linarith) hdpos, one_mul]
    have : ((18 * (d + 1) * D + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast hT3
    push_cast at this
    linarith
  have hsum : 1 / (q : ℝ) ^ M + 2 ^ (K + 4) / ((q : ℝ) * (1 / ((2 ^ σ : ℕ) : ℝ))) +
      (D : ℝ) / ((q : ℝ) - 1) ≤ 3 * (1 / (18 * ((d : ℝ) + 1))) := by
    linarith
  have hne : (d : ℝ) + 1 ≠ 0 := by positivity
  calc _ ≤ 6 * ((d : ℝ) + 1) * (3 * (1 / (18 * ((d : ℝ) + 1)))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := by field_simp; ring

/-- The final size bound `2 ^ 11 * 3 ^ L * M * w ^ 2 * q ^ 9 * 4 ^ K * (s + 3) < 2 ^ (40 b)`. -/
private theorem final_lt {M b σ : ℕ} (hM : 1 ≤ M) (hb : 1 ≤ b)
    (hF : 2 ^ 27 * M ^ 3 * b ^ 6 ≤ 2 ^ (b / 4)) (h5σ : 5 * σ ≤ b) :
    2 ^ 11 * 3 ^ (Nat.log 2 (M * b) + 1) * M * (4 * b) ^ 2 * (2 ^ (4 * b)) ^ 9 *
      4 ^ (2 * σ + Nat.log 2 (4 * b) + 2) * (2 ^ σ + 2 + 1) < 2 ^ (40 * b) := by
  have h3L := three_pow_log_le (show 0 < M * b by positivity)
  have h4K : 4 ^ (2 * σ + Nat.log 2 (4 * b) + 2) ≤ 256 * b ^ 2 * 16 ^ σ := by
    rw [show 4 ^ (2 * σ + Nat.log 2 (4 * b) + 2) = (2 ^ (2 * σ + Nat.log 2 (4 * b) + 2)) ^ 2 by
      rw [← pow_mul, mul_comm _ 2, pow_mul]; norm_num]
    calc (2 ^ (2 * σ + Nat.log 2 (4 * b) + 2)) ^ 2 ≤ (16 * b * 4 ^ σ) ^ 2 :=
          Nat.pow_le_pow_left (two_pow_masks_le σ hb) 2
      _ = 256 * b ^ 2 * 16 ^ σ := by
          rw [mul_pow, mul_pow, ← pow_mul, mul_comm σ 2, pow_mul]
          norm_num
  have hs : 2 ^ σ + 2 + 1 ≤ 4 * 2 ^ σ := by
    have : 1 ≤ 2 ^ σ := Nat.one_le_two_pow
    omega
  calc 2 ^ 11 * 3 ^ (Nat.log 2 (M * b) + 1) * M * (4 * b) ^ 2 * (2 ^ (4 * b)) ^ 9 *
        4 ^ (2 * σ + Nat.log 2 (4 * b) + 2) * (2 ^ σ + 2 + 1)
      ≤ 2 ^ 11 * (3 * (M * b) ^ 2) * M * (4 * b) ^ 2 * (2 ^ (4 * b)) ^ 9 *
          (256 * b ^ 2 * 16 ^ σ) * (4 * 2 ^ σ) := by gcongr
    _ = 3 * 2 ^ 25 * (M ^ 3 * b ^ 6) * 2 ^ (36 * b) * 2 ^ (5 * σ) := by
        rw [show 16 ^ σ = 2 ^ (4 * σ) by rw [pow_mul]; norm_num, show 5 * σ = 4 * σ + σ by ring,
          pow_add 2 (4 * σ) σ, ← pow_mul, show 4 * b * 9 = 36 * b by ring]
        ring
    _ ≤ 3 * 2 ^ 25 * (M ^ 3 * b ^ 6) * 2 ^ (36 * b) * 2 ^ b :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) h5σ)
    _ < 2 ^ 27 * M ^ 3 * b ^ 6 * 2 ^ (37 * b) := by
        rw [show 37 * b = 36 * b + b by ring, pow_add 2 (36 * b) b]
        have : 0 < M ^ 3 * b ^ 6 * 2 ^ (36 * b) * 2 ^ b := by positivity
        nlinarith
    _ ≤ 2 ^ (b / 4) * 2 ^ (37 * b) := Nat.mul_le_mul_right _ hF
    _ ≤ 2 ^ (40 * b) := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ### Hardness at one length -/

/-- **Hardness at one length.** Let `M ≥ 1` and let the block length `b` at length `N` be positive
with `(2 ^ 27 * M ^ 3 + 4608 * M + 128) * b ^ 6 ≤ 2 ^ ⌊b / 4⌋`. If `50 σ ≤ b + 1` and the slice of
`L` at length `M b` needs `2 ^ (40 b)` gates, then the encoded slice at length `N` is average-case
hard for size `2 ^ σ`. -/
theorem isAverageCaseHard_encodedSlice_of {L : Language Bool} {M N σ : ℕ} (hM : 1 ≤ M)
    (hb : 1 ≤ blockLength M N)
    (hev : (2 ^ 27 * M ^ 3 + 4608 * M + 128) * blockLength M N ^ 6 ≤ 2 ^ (blockLength M N / 4))
    (hσ : 50 * σ ≤ blockLength M N + 1)
    (hhard : 2 ^ (40 * blockLength M N) ≤
      complexity interpretation (single (L.slice (M * blockLength M N)))) :
    IsAverageCaseHard (encodedSlice L M N) (2 ^ σ) := by
  classical
  set b := blockLength M N with hb_def
  have hb0 : b ≠ 0 := by omega
  have hw0 : 4 * b ≠ 0 := by omega
  obtain ⟨hA, hB, hD', hE, hF⟩ := schedule_bounds hb hev
  have h3σ : 3 * σ ≤ b := by omega
  have h5σ : 5 * σ ≤ b := by omega
  have h2b : 2 ≤ 2 ^ b :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have hd1 : 1 ≤ M * (2 ^ b - 1) := Nat.mul_pos (by omega) (by omega)
  -- a circuit of high agreement
  intro g hg
  by_contra hcon
  push Not at hcon
  have hslice : encodedSlice L M N = fun y => hardnessEncode (BinaryField.equivBits hw0)
      (BinaryField.embed hw0 (by omega)) (L.slice (M * b))
      (fun i => y (Fin.castLE (encodedLength_le M N) i)) := by
    rw [encodedSlice, dite_eq_right hb0]
  rw [hslice, lt_div_iff₀ (by positivity)] at hcon
  obtain ⟨C, hC, hCagree⟩ := exists_complexity_le_of_agree_prefix (encodedLength_le M N) _ g hcon
  -- the reconstruction
  have hrec := complexity_le_pow_of_agree_hardnessEncode (BinaryField.equivBits hw0)
    (BinaryField.embed hw0 (by omega : b ≤ 4 * b)) (L.slice (M * b)) (C := C)
    (s := 2 ^ σ + 2) (hC.trans (by omega)) (ε := 1 / ((2 ^ σ : ℕ) : ℝ)) (by positivity)
    hCagree.le (K := 2 * σ + Nat.log 2 (4 * b) + 2) (D := 2 ^ (3 * b - b / 4))
    (L := Nat.log 2 (M * b) + 1) (by omega) (masks_size (two_pow_masks_ge σ b)) hd1
    (by rw [BinaryField.card_eq hw0]; exact card_lt_card_monomials hM hb hA)
    (by rw [BinaryField.card_eq hw0]; exact margin_le hb hB h3σ)
    (by rw [BinaryField.card_eq hw0]; exact errors_le hM hb hD' hE h3σ)
    (Nat.lt_pow_succ_log_self (by norm_num) (M * b)).le
  -- the bound contradicts the worst-case hardness
  rw [BinaryField.card_eq hw0] at hrec
  exact absurd hhard (not_le.2 (hrec.trans_lt (final_lt hM hb hF h5σ)))

/-! ### Hardness at all large lengths -/

/-- Polynomials are eventually below `2 ^ ⌊b / 4⌋`. -/
private theorem eventually_mul_pow_le (C k : ℕ) : ∀ᶠ b : ℕ in atTop, C * b ^ k ≤ 2 ^ (b / 4) := by
  -- first `C 4 ^ k (t + 1) ^ k ≤ 2 ^ t` for large `t`
  have h := (tendsto_pow_const_div_const_pow_of_one_lt k (r := 2) one_lt_two).comp
    (tendsto_add_atTop_nat 1)
  have hpos : (0 : ℝ) < 1 / (2 * C * 4 ^ k + 1) := by positivity
  have ht : ∀ᶠ t : ℕ in atTop, C * (4 * (t + 1)) ^ k ≤ 2 ^ t := by
    filter_upwards [h.eventually (gt_mem_nhds hpos)] with t ht
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one] at ht
    rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul, pow_succ] at ht
    have hX : (0 : ℝ) ≤ ((t : ℝ) + 1) ^ k := by positivity
    have hreal : (C : ℝ) * (4 * ((t : ℝ) + 1)) ^ k ≤ 2 ^ t := by
      rw [mul_pow]
      nlinarith
    exact_mod_cast hreal
  -- then `b ≤ 4 (⌊b / 4⌋ + 1)`
  have hdiv := (Nat.tendsto_div_const_atTop (n := 4) (by norm_num)).eventually ht
  filter_upwards [hdiv] with b hb
  calc C * b ^ k ≤ C * (4 * (b / 4 + 1)) ^ k := by
        gcongr
        omega
    _ ≤ 2 ^ (b / 4) := hb

/-- **Exponential worst-case hardness gives exponential average-case hardness**
[SudanTrevisanVadhan2001], [ImpagliazzoWigderson1997]. If the slices of `L` need De Morgan circuits
of size `2 ^ (γ n)` for all large `n`, for some `γ > 0`, then the encoded slices of `L` at all large
lengths `N` are average-case hard for size `2 ^ ⌊N / c⌋`, where `c = hardnessDivisor γ`. -/
theorem eventually_isAverageCaseHard_encodedSlice {L : Language Bool} {γ : ℝ} (hγ : 0 < γ)
    (hard : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ (γ * n) ≤ complexity interpretation (single (L.slice n))) :
    ∀ᶠ N in atTop, IsAverageCaseHard (encodedSlice L (blockFactor γ) N)
      (2 ^ (N / hardnessDivisor γ)) := by
  set M := blockFactor γ with hM_def
  have hM : 1 ≤ M := Nat.le_add_left 1 _
  have hγM : 40 ≤ γ * M := by
    have h := Nat.le_ceil (40 / γ)
    have : (M : ℝ) = ⌈40 / γ⌉₊ + 1 := by rw [hM_def, blockFactor]; push_cast; rfl
    rw [this]
    have h' : 40 / γ ≤ (⌈40 / γ⌉₊ : ℝ) + 1 := by linarith
    rw [div_le_iff₀ hγ] at h'
    linarith
  -- the block length tends to infinity
  have hblock : Tendsto (blockLength M) atTop atTop :=
    Nat.tendsto_div_const_atTop (by positivity)
  -- worst-case hardness at the lengths `M b`
  have hMb : Tendsto (fun b : ℕ => M * b) atTop atTop :=
    tendsto_id.const_mul_atTop' (by omega)
  have hhard : ∀ᶠ b : ℕ in atTop,
      2 ^ (40 * b) ≤ complexity interpretation (single (L.slice (M * b))) := by
    filter_upwards [hMb.eventually hard] with b hb
    have h1 : (2 : ℝ) ^ ((40 * b : ℕ) : ℝ) ≤ (2 : ℝ) ^ (γ * ((M * b : ℕ) : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      nlinarith
    rw [Real.rpow_natCast] at h1
    exact_mod_cast h1.trans hb
  have hev := eventually_mul_pow_le (2 ^ 27 * M ^ 3 + 4608 * M + 128) 6
  filter_upwards [hblock.eventually (hhard.and (hev.and (eventually_ge_atTop 1)))] with N hN
  obtain ⟨hNhard, hNev, hNb⟩ := hN
  refine isAverageCaseHard_encodedSlice_of hM hNb hNev ?_ hNhard
  -- `50 ⌊N / c⌋ ≤ b + 1`
  have h1 := Nat.div_mul_le_self N (hardnessDivisor γ)
  have h2 := Nat.lt_div_mul_add (a := N) (b := 4 * (M + 1)) (by positivity)
  simp only [hardnessDivisor, ← hM_def, blockLength] at h1 h2 ⊢
  nlinarith

end Cslib.Circuits.Boolean
