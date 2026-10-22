/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Approximation.Hastad.ExactThreeDistinct
public import Complexity.Foundations.BooleanAnalysis.Convolution
public import Complexity.Foundations.BooleanAnalysis.Hadamard
public import Complexity.Foundations.BooleanAnalysis.Noise
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.Chebyshev

/-!
# Håstad's 3-Bit Linear Test, Spectral Decoding Weights, and 4-Clause E3-CNF Gadget

This module formalizes Håstad's noisy 3-bit linear test on folded Long Code tables over a single
projection `π : β → γ`, its exact Walsh–Fourier expansion, the Cauchy–Schwarz and Parseval
soundness bound via low-degree spectral decoding weights, and the 4-clause E3-CNF gadget converting
3-bit XOR tests into exact 3-CNF clauses on distinct variables [Hastad2001].

## Main definitions

* `Cslib.PCP.Hastad.IsFolded`, `Cslib.PCP.Hastad.foldTable`: table folding over `(α → Bool) → Bool`
  (reusing `Cslib.BitString.longCode` for the Long Code).
* `Cslib.PCP.Hastad.projectSet`: mod-2 projection of a subset `T : Finset β` along `π : β → γ`.
* `Cslib.PCP.Hastad.hastadLinearCorr`, `Cslib.PCP.Hastad.hastadLinearProb`: correlation and
  acceptance probability of Håstad's 3-bit linear test on an edge `π : β → γ`.
* `Cslib.PCP.Hastad.spectralWeight`: low-degree Fourier decoding weights on `α`.
* `Cslib.PCP.Hastad.xorThreeCNF`: the 4-clause E3-CNF gadget for a 3-bit XOR equation.

## Main results

* `Cslib.PCP.Hastad.IsFolded.fourierCoeff_empty`,
  `Cslib.PCP.Hastad.IsFolded.fourierCoeff_of_even`: every even-degree Fourier coefficient of a
  folded table (and in particular at `∅`) vanishes.
* `Cslib.PCP.Hastad.hastadLinearCorr_longCode`, `Cslib.PCP.Hastad.hastadLinearProb_longCode`:
  completeness `1 - δ` for 3-bit linear tests on valid Long Code tables.
* `Cslib.PCP.Hastad.hastadLinearCorr_eq_sum`: exact Walsh–Fourier expansion of Håstad's 3-bit test
  correlation.
* `Cslib.PCP.Hastad.sum_spectralWeight_le_one`: Parseval bound showing that `spectralWeight k B` is
  a sub-probability distribution on `γ`.
* `Cslib.PCP.Hastad.hastadLinearCorr_sq_le`: single-edge Cauchy–Schwarz + Parseval soundness bound.

## References

* [J. Håstad, *Some optimal inapproximability results*][Hastad2001]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 22][AroraBarak09]
* [R. O'Donnell, *Analysis of Boolean Functions*, Chapter 7][ODonnell2014]
-/

@[expose] public section

open Finset
open scoped BigOperators symmDiff

namespace Cslib.PCP.Hastad

open Cslib.BitString Cslib.Logic.PL Cslib.Complexity

variable {α β γ : Type*}

/-! ### The Long Code and table folding -/

/-- In `±1` notation, the Long Code `Cslib.BitString.longCode x` is the singleton Walsh character
`chi ℝ {x}`. -/
theorem signVal_longCode (x : α) (f : α → Bool) :
    signVal (longCode x f) = chi ℝ {x} f :=
  (chi_singleton x f).symm

/-- A Long Code table `B : (α → Bool) → Bool` is **folded** when negating the input function
(`f + fun _ => true`) negates the output bit. -/
def IsFolded (B : (α → Bool) → Bool) : Prop :=
  ∀ f : α → Bool, B (f + fun _ => true) = !B f

/-- Every honest Long Code table `longCode x` is folded. -/
theorem isFolded_longCode (x : α) : IsFolded (longCode x) := fun f => by
  change (f x + true) = !(f x)
  cases f x <;> rfl

/-- **Folding a table** around coordinate `x₀ : α`: accesses `B f` when `f x₀ = false` and
`!B (f + fun _ => true)` when `f x₀ = true`. -/
def foldTable (x₀ : α) (B : (α → Bool) → Bool) (f : α → Bool) : Bool :=
  if f x₀ then !B (f + fun _ => true) else B f

/-- Folding any table produces a folded table. -/
theorem isFolded_foldTable (x₀ : α) (B : (α → Bool) → Bool) : IsFolded (foldTable x₀ B) := by
  intro f
  have h1 : (f + fun _ : α => true) x₀ = !f x₀ := by
    change (f x₀ + true) = !f x₀
    cases f x₀ <;> rfl
  have h2 : (f + fun _ : α => true) + (fun _ : α => true) = f := by
    funext x
    change (f x + true) + true = f x
    cases f x <;> rfl
  simp only [foldTable, h1, h2]
  cases f x₀ <;> simp

/-- Folding an already-folded table leaves it unchanged. -/
theorem IsFolded.foldTable_eq {B : (α → Bool) → Bool} (hB : IsFolded B) (x₀ : α) :
    foldTable x₀ B = B := by
  funext f
  simp only [foldTable, hB f, Bool.not_not, ite_self]

/-- **A folded table has zero empty Fourier coefficient**: its `±1` values cancel in pairs
`f` and `f + fun _ => true`. -/
theorem IsFolded.fourierCoeff_empty [Fintype α] [DecidableEq α] {B : (α → Bool) → Bool}
    (hB : IsFolded B) : fourierCoeff (fun f => signVal (B f)) ∅ = 0 := by
  rw [Cslib.BitString.fourierCoeff_empty]
  have h1 : (𝔼 f : α → Bool, signVal (B f)) =
      𝔼 f : α → Bool, signVal (B ((fun _ => true) + f)) :=
    (Fintype.expect_add_left (fun f : α → Bool => signVal (B f)) (fun _ => true)).symm
  have h2 (f : α → Bool) : signVal (B ((fun _ => true) + f)) = -signVal (B f) := by
    rw [add_comm (fun _ => true) f, hB f, signVal_not]
  simp only [h2, expect_neg_distrib] at h1
  linarith

/-- On a folded table, any character of even cardinality has Fourier coefficient `0`. -/
theorem IsFolded.fourierCoeff_of_even [Fintype α] [DecidableEq α] {B : (α → Bool) → Bool}
    (hB : IsFolded B) {S : Finset α} (hS : Even #S) :
    fourierCoeff (fun f => signVal (B f)) S = 0 := by
  rw [fourierCoeff]
  have hchi : chi ℝ S (fun _ : α => true) = 1 := by
    rw [chi_eq_prod_signVal, prod_const]
    obtain ⟨m, hm⟩ := hS
    rw [hm, pow_add, ← mul_pow]
    norm_num
  have h1 : (𝔼 f : α → Bool, signVal (B f) * chi ℝ S f) =
      𝔼 f : α → Bool, signVal (B ((fun _ => true) + f)) * chi ℝ S ((fun _ => true) + f) :=
    (Fintype.expect_add_left (fun f : α → Bool => signVal (B f) * chi ℝ S f)
      (fun _ => true)).symm
  have h2 (f : α → Bool) :
      signVal (B ((fun _ => true) + f)) * chi ℝ S ((fun _ => true) + f) =
        -(signVal (B f) * chi ℝ S f) := by
    rw [add_comm (fun _ => true) f, hB f, signVal_not, chi_add, hchi]
    ring
  simp only [h2, expect_neg_distrib] at h1
  linarith

/-! ### Mod-2 projection of subsets and character pullback -/

section Projection

variable [Fintype γ] [DecidableEq γ]

/-- The **mod-2 projection** `π₂(T)` of `T : Finset β` along `π : β → γ`: the set of `y : γ`
whose fiber in `T` under `π` has odd cardinality [Håstad][Hastad2001]. -/
def projectSet (π : β → γ) (T : Finset β) : Finset γ :=
  univ.filter fun y => Odd #{x ∈ T | π x = y}

@[simp]
theorem mem_projectSet {π : β → γ} {T : Finset β} {y : γ} :
    y ∈ projectSet π T ↔ Odd #{x ∈ T | π x = y} := by
  simp [projectSet]

@[simp]
theorem projectSet_empty (π : β → γ) : projectSet π ∅ = ∅ := by
  ext y
  simp [projectSet]

/-- Every element of `projectSet π T` lies in the image of `T` under `π`. -/
theorem exists_mem_of_mem_projectSet {π : β → γ} {T : Finset β} {y : γ}
    (hy : y ∈ projectSet π T) : ∃ x ∈ T, π x = y := by
  rw [mem_projectSet] at hy
  have hpos : 0 < #{x ∈ T | π x = y} := Nat.pos_of_ne_zero (by rintro h0; simp [h0] at hy)
  obtain ⟨x, hx⟩ := card_pos.1 hpos
  exact ⟨x, (mem_filter.1 hx).1, (mem_filter.1 hx).2⟩

theorem projectSet_subset_image (π : β → γ) (T : Finset β) :
    projectSet π T ⊆ T.image π := fun y hy => by
  obtain ⟨x, hx, rfl⟩ := exists_mem_of_mem_projectSet hy
  exact mem_image_of_mem π hx

/-- The mod-2 projection never increases cardinality: `#(projectSet π T) ≤ #T`. -/
theorem card_projectSet_le (π : β → γ) (T : Finset β) : #(projectSet π T) ≤ #T :=
  (card_le_card (projectSet_subset_image π T)).trans card_image_le

variable [DecidableEq β]

/-- Inserting `x ∉ T` toggles `π x` in `projectSet π T`. -/
theorem projectSet_insert (π : β → γ) {x : β} {T : Finset β} (hx : x ∉ T) :
    projectSet π (insert x T) = symmDiff (projectSet π T) {π x} := by
  ext y
  rw [mem_projectSet, mem_symmDiff, mem_projectSet, mem_singleton, filter_insert]
  by_cases hxy : π x = y
  · subst hxy
    have hx' : x ∉ {z ∈ T | π z = π x} := fun h => hx (mem_filter.1 h).1
    simp only [↓reduceIte, card_insert_of_notMem hx', Nat.odd_add_one, not_true_eq_false,
      and_false, true_and, false_or]
  · have hyx : y ≠ π x := Ne.symm hxy
    simp [hxy, hyx]

omit [DecidableEq β] in
/-- **Pulling a character back along `π` projects the frequency set by `projectSet π`**:
`chi ℝ T (f ∘ π) = chi ℝ (projectSet π T) f`. -/
theorem chi_comp_eq_chi_projectSet (π : β → γ) (T : Finset β) (f : γ → Bool) :
    chi ℝ T (f ∘ π) = chi ℝ (projectSet π T) f := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert x T hx ih =>
    rw [projectSet_insert π hx, ← chi_mul_chi, chi_singleton, ← ih, chi_eq_prod_signVal,
      prod_insert hx, ← chi_eq_prod_signVal, Function.comp_apply, mul_comm]

end Projection

/-! ### Håstad's 3-bit linear test and its Fourier expansion -/

section LinearTest

variable [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

/-- The **correlation** of Håstad's 3-bit linear test on a projection `π : β → γ` at noise rate `δ`
between tables `B : (γ → Bool) → Bool` and `A : (β → Bool) → Bool` [Håstad, Section 5][Hastad2001]:
the expected product of the `±1` signs of `B f`, `A g`, and `A ((f ∘ π) + g + μ)` over uniform
`f : γ → Bool`, uniform `g : β → Bool`, and `δ`-biased Bernoulli noise `μ : β → Bool`. -/
noncomputable def hastadLinearCorr (π : β → γ) (δ : ℝ) (B : (γ → Bool) → Bool)
    (A : (β → Bool) → Bool) : ℝ :=
  𝔼 f : γ → Bool, 𝔼 g : β → Bool,
    bernoulliAverage δ fun μ =>
      signVal (B f) * signVal (A g) * signVal (A ((f ∘ π) + g + μ))

/-- The **acceptance probability** of Håstad's 3-bit linear test: the probability that
`(B f ^^ A g ^^ A ((f ∘ π) + g + μ)) = false` under uniform `f, g` and `δ`-biased noise `μ`. -/
noncomputable def hastadLinearProb (π : β → γ) (δ : ℝ) (B : (γ → Bool) → Bool)
    (A : (β → Bool) → Bool) : ℝ :=
  𝔼 f : γ → Bool, 𝔼 g : β → Bool,
    bernoulliAverage δ fun μ =>
      if (B f ^^ A g ^^ A ((f ∘ π) + g + μ)) = false then 1 else 0

/-- The acceptance probability of Håstad's 3-bit linear test is
`1 / 2 + 1 / 2 * hastadLinearCorr π δ B A`. -/
theorem hastadLinearProb_eq_add_hastadLinearCorr (π : β → γ) (δ : ℝ)
    (B : (γ → Bool) → Bool) (A : (β → Bool) → Bool) :
    hastadLinearProb π δ B A = 1 / 2 + 1 / 2 * hastadLinearCorr π δ B A := by
  have h (b₁ b₂ b₃ : Bool) :
      (if (b₁ ^^ b₂ ^^ b₃) = false then (1 : ℝ) else 0) =
        1 / 2 + 1 / 2 * (signVal b₁ * signVal b₂ * signVal b₃) := by
    cases b₁ <;> cases b₂ <;> cases b₃ <;> simp only [signVal] <;> norm_num
  simp only [hastadLinearProb, hastadLinearCorr, h, bernoulliAverage_add, bernoulliAverage_const,
    bernoulliAverage_const_mul, expect_add_distrib, Fintype.expect_const, mul_expect]

/-- **Completeness of Håstad's 3-bit linear test (correlation)**: on matching Long Code tables
`longCode (π x)` and `longCode x`, the correlation is `1 - 2 * δ`. -/
theorem hastadLinearCorr_longCode (π : β → γ) (δ : ℝ) (x : β) :
    hastadLinearCorr π δ (longCode (π x)) (longCode x) = 1 - 2 * δ := by
  have hsign (f : γ → Bool) (g μ : β → Bool) :
      signVal (longCode (π x) f) * signVal (longCode x g) *
        signVal (longCode x ((f ∘ π) + g + μ)) = chi ℝ {x} μ := by
    rw [chi_singleton]
    change signVal (f (π x)) * signVal (g x) * signVal (f (π x) + g x + μ x) = signVal (μ x)
    cases f (π x) <;> cases g x <;> cases μ x <;> simp [signVal, Bool.add_eq_xor]
  simp only [hastadLinearCorr, hsign, bernoulliAverage_chi, card_singleton, pow_one,
    Fintype.expect_const]

/-- **Completeness of Håstad's 3-bit linear test (probability)**: matching Long Code tables
`longCode (π x)` and `longCode x` pass the test with probability `1 - δ`. -/
theorem hastadLinearProb_longCode (π : β → γ) (δ : ℝ) (x : β) :
    hastadLinearProb π δ (longCode (π x)) (longCode x) = 1 - δ := by
  rw [hastadLinearProb_eq_add_hastadLinearCorr, hastadLinearCorr_longCode]
  ring

/-- **Walsh–Fourier expansion of Håstad's 3-bit linear test** [Håstad, Lemma 5.1][Hastad2001]:
the correlation equals
`∑ T : Finset β, (1 - 2 * δ) ^ #T * fourierCoeff F_A T ^ 2 * fourierCoeff F_B (projectSet π T)`. -/
theorem hastadLinearCorr_eq_sum (π : β → γ) (δ : ℝ) (B : (γ → Bool) → Bool)
    (A : (β → Bool) → Bool) :
    hastadLinearCorr π δ B A =
      ∑ T : Finset β,
        (1 - 2 * δ) ^ #T * fourierCoeff (fun g => signVal (A g)) T ^ 2 *
          fourierCoeff (fun f => signVal (B f)) (projectSet π T) := by
  have hδ : (1 - (1 - 2 * δ)) / 2 = δ := by ring
  have hinner (f : γ → Bool) (g : β → Bool) :
      (bernoulliAverage δ fun μ =>
          signVal (B f) * signVal (A g) * signVal (A ((f ∘ π) + g + μ))) =
        signVal (B f) *
          (signVal (A g) * noiseOp (1 - 2 * δ) (fun h => signVal (A h)) ((f ∘ π) + g)) := by
    simp only [mul_assoc, bernoulliAverage_const_mul, noiseOp, hδ]
  have hconv (f : γ → Bool) :
      (𝔼 g : β → Bool,
          signVal (B f) *
            (signVal (A g) * noiseOp (1 - 2 * δ) (fun h => signVal (A h)) ((f ∘ π) + g))) =
        signVal (B f) * ∑ T : Finset β,
          (1 - 2 * δ) ^ #T * fourierCoeff (fun g => signVal (A g)) T ^ 2 *
            chi ℝ (projectSet π T) f := by
    rw [← mul_expect]
    congr 1
    change convolution (fun g => signVal (A g))
      (noiseOp (1 - 2 * δ) (fun h => signVal (A h))) (f ∘ π) = _
    rw [← sum_fourierCoeff_mul_chi
      (convolution (fun g => signVal (A g)) (noiseOp (1 - 2 * δ) (fun h => signVal (A h))))
      (f ∘ π)]
    refine sum_congr rfl fun T _ => ?_
    rw [fourierCoeff_convolution, fourierCoeff_noiseOp, chi_comp_eq_chi_projectSet]
    ring
  simp only [hastadLinearCorr, hinner, hconv, mul_sum]
  rw [expect_sum_comm]
  refine sum_congr rfl fun T _ => ?_
  have hterm (f : γ → Bool) :
      signVal (B f) *
          ((1 - 2 * δ) ^ #T * fourierCoeff (fun g => signVal (A g)) T ^ 2 *
            chi ℝ (projectSet π T) f) =
        ((1 - 2 * δ) ^ #T * fourierCoeff (fun g => signVal (A g)) T ^ 2) *
          (signVal (B f) * chi ℝ (projectSet π T) f) := by
    ring
  simp only [hterm, ← mul_expect]
  rfl

end LinearTest

/-! ### Spectral decoding weights and Cauchy–Schwarz soundness bound -/

section Soundness

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

@[deprecated (since := "2026-10-22")]
alias fourierCoeff_sq_signVal_le_one := Cslib.BitString.fourierCoeff_sq_signVal_le_one

/-- The **low-degree spectral decoding weight** of `x : α` for table `A : (α → Bool) → Bool` at
degree cutoff `k`: `∑_{T : #T < k, x ∈ T} fourierCoeff F_A T ^ 2 / #T`
[Håstad, Proof of Lemma 5.2][Hastad2001]. -/
noncomputable def spectralWeight (k : ℕ) (A : (α → Bool) → Bool) (x : α) : ℝ :=
  ∑ T ∈ univ.filter (fun T : Finset α => #T < k ∧ x ∈ T),
    fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T

theorem spectralWeight_nonneg (k : ℕ) (A : (α → Bool) → Bool) (x : α) :
    0 ≤ spectralWeight k A x :=
  sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- **By Parseval's identity, the spectral decoding weights form a sub-probability distribution**:
`∑ x, spectralWeight k A x ≤ 1`. -/
theorem sum_spectralWeight_le_one (k : ℕ) (A : (α → Bool) → Bool) :
    ∑ x : α, spectralWeight k A x ≤ 1 := by
  simp only [spectralWeight, sum_filter]
  rw [sum_comm]
  rw [← sum_fourierCoeff_sq_signVal A]
  refine sum_le_sum fun T _ => ?_
  by_cases hTk : #T < k
  · by_cases hT0 : T = ∅
    · subst hT0
      simp only [notMem_empty, and_false, ↓reduceIte, sum_const_zero]
      exact sq_nonneg _
    · have hpos : (0 : ℝ) < #T := by
        exact_mod_cast card_pos.2 (nonempty_iff_ne_empty.2 hT0)
      have hsum :
          (∑ x : α, if #T < k ∧ x ∈ T then
            fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T else 0) =
          ∑ x ∈ T, fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T := by
        rw [← sum_filter]
        refine sum_congr ?_ fun _ _ => rfl
        ext x
        simp [hTk]
      rw [hsum, sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hpos.ne']
  · simp only [hTk, false_and, ↓reduceIte, sum_const_zero]
    exact sq_nonneg _

/-- Low-degree terms in the Cauchy–Schwarz bound are controlled by the collision probability of the
spectral decoding distributions along `π`. -/
theorem sum_lowDegree_fourierCoeff_sq_le (π : β → γ) (k : ℕ)
    (B : (γ → Bool) → Bool) (A : (β → Bool) → Bool) :
    (∑ T ∈ univ.filter (fun T : Finset β => #T < k ∧ projectSet π T ≠ ∅),
      fourierCoeff (fun g => signVal (A g)) T ^ 2 *
        fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2) ≤
      (k : ℝ) ^ 2 * ∑ x : β, spectralWeight k A x * spectralWeight k B (π x) := by
  have hterm (T : Finset β) :
      (if #T < k ∧ projectSet π T ≠ ∅ then
        fourierCoeff (fun g => signVal (A g)) T ^ 2 *
          fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2
      else 0) ≤
        (k : ℝ) ^ 2 * ∑ x : β,
          (if #T < k ∧ x ∈ T then fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T else 0) *
            spectralWeight k B (π x) := by
    split_ifs with hT
    · obtain ⟨hTk, hne⟩ := hT
      obtain ⟨y, hy⟩ := nonempty_iff_ne_empty.2 hne
      obtain ⟨x₀, hx₀T, rfl⟩ := exists_mem_of_mem_projectSet hy
      have hcardT_pos : (0 : ℝ) < #T := by
        exact_mod_cast card_pos.2 ⟨x₀, hx₀T⟩
      have hcardT_le : (#T : ℝ) ≤ k := by exact_mod_cast hTk.le
      have hcardS_pos : (0 : ℝ) < #(projectSet π T) := by
        exact_mod_cast card_pos.2 ⟨π x₀, hy⟩
      have hcardS_lt : #(projectSet π T) < k := (card_projectSet_le π T).trans_lt hTk
      have hcardS_le : (#(projectSet π T) : ℝ) ≤ k := by exact_mod_cast hcardS_lt.le
      have hB_le :
          fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2 / #(projectSet π T) ≤
            spectralWeight k B (π x₀) := by
        rw [spectralWeight]
        refine single_le_sum
          (f := fun S : Finset γ => fourierCoeff (fun f => signVal (B f)) S ^ 2 / #S)
          (fun S _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) ?_
        simp [hcardS_lt, hy]
      have hB_le' :
          fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2 ≤
            (k : ℝ) * spectralWeight k B (π x₀) := by
        have h1 : fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2 =
            #(projectSet π T) *
              (fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2 / #(projectSet π T)) := by
          rw [mul_div_cancel₀ _ hcardS_pos.ne']
        conv_lhs => rw [h1]
        exact mul_le_mul hcardS_le hB_le (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
          (Nat.cast_nonneg k)
      have hA_le' :
          fourierCoeff (fun g => signVal (A g)) T ^ 2 ≤
            (k : ℝ) * (fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T) := by
        have h1 : fourierCoeff (fun g => signVal (A g)) T ^ 2 =
            #T * (fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T) := by
          rw [mul_div_cancel₀ _ hcardT_pos.ne']
        conv_lhs => rw [h1]
        exact mul_le_mul_of_nonneg_right hcardT_le (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      have hprod :
          fourierCoeff (fun g => signVal (A g)) T ^ 2 *
              fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2 ≤
            (k : ℝ) ^ 2 *
              ((fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T) *
                spectralWeight k B (π x₀)) := by
        calc fourierCoeff (fun g => signVal (A g)) T ^ 2 *
              fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2
          _ ≤ ((k : ℝ) * (fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T)) *
                ((k : ℝ) * spectralWeight k B (π x₀)) :=
            mul_le_mul hA_le' hB_le' (sq_nonneg _) (by positivity)
          _ = (k : ℝ) ^ 2 *
                ((fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T) *
                  spectralWeight k B (π x₀)) := by ring
      refine hprod.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
      have hsingle := single_le_sum
        (f := fun x : β =>
          (if #T < k ∧ x ∈ T then fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T else 0) *
            spectralWeight k B (π x))
        (fun x _ => by
          split_ifs
          · exact mul_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
              (spectralWeight_nonneg k B (π x))
          · simp)
        (mem_univ x₀)
      simpa [hTk, hx₀T] using hsingle
    · refine mul_nonneg (sq_nonneg _) (sum_nonneg fun x _ => ?_)
      split_ifs
      · exact mul_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
          (spectralWeight_nonneg k B (π x))
      · simp
  rw [sum_filter]
  calc (∑ T : Finset β,
        if #T < k ∧ projectSet π T ≠ ∅ then
          fourierCoeff (fun g => signVal (A g)) T ^ 2 *
            fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2
        else 0)
    _ ≤ ∑ T : Finset β, (k : ℝ) ^ 2 * ∑ x : β,
          (if #T < k ∧ x ∈ T then fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T else 0) *
            spectralWeight k B (π x) := sum_le_sum fun T _ => hterm T
    _ = (k : ℝ) ^ 2 * ∑ x : β, spectralWeight k A x * spectralWeight k B (π x) := by
      rw [← mul_sum, sum_comm]
      congr 1
      refine sum_congr rfl fun x _ => ?_
      rw [← sum_mul]
      congr 1
      rw [spectralWeight, sum_filter]

/-- **Cauchy–Schwarz and Parseval soundness bound for Håstad's 3-bit linear test**
[Håstad, Lemma 5.2][Hastad2001]: for any folded table `B`, any table `A`, noise rate
`0 ≤ δ ≤ 1 / 2`, and degree cutoff `k`, the squared correlation `hastadLinearCorr π δ B A ^ 2` is
at most `(1 - 2 * δ) ^ (2 * k) + k ^ 2 * ∑ x, spectralWeight k A x * spectralWeight k B (π x)`. -/
theorem hastadLinearCorr_sq_le (π : β → γ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (k : ℕ) {B : (γ → Bool) → Bool} (hB : IsFolded B) (A : (β → Bool) → Bool) :
    hastadLinearCorr π δ B A ^ 2 ≤
      (1 - 2 * δ) ^ (2 * k) +
        (k : ℝ) ^ 2 * ∑ x : β, spectralWeight k A x * spectralWeight k B (π x) := by
  have hcs :
      hastadLinearCorr π δ B A ^ 2 ≤
        ∑ T : Finset β,
          fourierCoeff (fun g => signVal (A g)) T ^ 2 *
            ((1 - 2 * δ) ^ #T * fourierCoeff (fun f => signVal (B f)) (projectSet π T)) ^ 2 := by
    rw [hastadLinearCorr_eq_sum]
    have hrewrite :
        (∑ T : Finset β,
          (1 - 2 * δ) ^ #T * fourierCoeff (fun g => signVal (A g)) T ^ 2 *
            fourierCoeff (fun f => signVal (B f)) (projectSet π T)) =
        ∑ T : Finset β,
          fourierCoeff (fun g => signVal (A g)) T *
            (fourierCoeff (fun g => signVal (A g)) T *
              ((1 - 2 * δ) ^ #T * fourierCoeff (fun f => signVal (B f)) (projectSet π T))) :=
      sum_congr rfl fun T _ => by ring
    rw [hrewrite]
    have h1 := sum_mul_sq_le_sq_mul_sq univ
      (fun T : Finset β => fourierCoeff (fun g => signVal (A g)) T)
      (fun T : Finset β =>
        fourierCoeff (fun g => signVal (A g)) T *
          ((1 - 2 * δ) ^ #T * fourierCoeff (fun f => signVal (B f)) (projectSet π T)))
    rw [sum_fourierCoeff_sq_signVal, one_mul] at h1
    refine h1.trans_eq (sum_congr rfl fun T _ => by ring)
  have hsplit :
      (∑ T : Finset β,
        fourierCoeff (fun g => signVal (A g)) T ^ 2 *
          ((1 - 2 * δ) ^ #T * fourierCoeff (fun f => signVal (B f)) (projectSet π T)) ^ 2) ≤
      (1 - 2 * δ) ^ (2 * k) * (∑ T : Finset β, fourierCoeff (fun g => signVal (A g)) T ^ 2) +
        ∑ T ∈ univ.filter (fun T : Finset β => #T < k ∧ projectSet π T ≠ ∅),
          fourierCoeff (fun g => signVal (A g)) T ^ 2 *
            fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2 := by
    rw [mul_sum, sum_filter, ← sum_add_distrib]
    refine sum_le_sum fun T _ => ?_
    have hρ0 : 0 ≤ 1 - 2 * δ := by linarith
    have hρ1 : 1 - 2 * δ ≤ 1 := by linarith
    by_cases hTk : #T < k
    · by_cases hne : projectSet π T ≠ ∅
      · simp only [hTk, hne, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
        have hpow : ((1 - 2 * δ) ^ #T) ^ 2 ≤ 1 := by
          rw [← pow_mul]
          exact pow_le_one₀ hρ0 hρ1
        have hnonneg : 0 ≤ (1 - 2 * δ) ^ (2 * k) * fourierCoeff (fun g => signVal (A g)) T ^ 2 :=
          mul_nonneg (pow_nonneg hρ0 _) (sq_nonneg _)
        have hle1 :
            fourierCoeff (fun g => signVal (A g)) T ^ 2 *
                ((1 - 2 * δ) ^ #T * fourierCoeff (fun f => signVal (B f)) (projectSet π T)) ^ 2 ≤
              fourierCoeff (fun g => signVal (A g)) T ^ 2 *
                fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2 := by
          rw [mul_pow, ← mul_assoc, mul_comm (fourierCoeff _ T ^ 2), mul_assoc]
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hpow (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        linarith
      · push Not at hne
        simp only [hTk, hne, ne_eq, not_true_eq_false, and_false, ↓reduceIte, add_zero,
          hB.fourierCoeff_empty, mul_zero, sq (0 : ℝ)]
        exact mul_nonneg (pow_nonneg hρ0 _) (sq_nonneg _)
    · simp only [hTk, false_and, ↓reduceIte, add_zero]
      have hkT : 2 * k ≤ #T * 2 := by omega
      have hpow : ((1 - 2 * δ) ^ #T) ^ 2 ≤ (1 - 2 * δ) ^ (2 * k) := by
        rw [← pow_mul]
        exact pow_le_pow_of_le_one hρ0 hρ1 hkT
      have hFB : fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2 ≤ 1 :=
        Cslib.BitString.fourierCoeff_sq_signVal_le_one B (projectSet π T)
      calc fourierCoeff (fun g => signVal (A g)) T ^ 2 *
            ((1 - 2 * δ) ^ #T * fourierCoeff (fun f => signVal (B f)) (projectSet π T)) ^ 2
        _ = fourierCoeff (fun g => signVal (A g)) T ^ 2 *
              (((1 - 2 * δ) ^ #T) ^ 2 *
                fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2) := by ring
        _ ≤ fourierCoeff (fun g => signVal (A g)) T ^ 2 * ((1 - 2 * δ) ^ (2 * k) * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          exact mul_le_mul hpow hFB (sq_nonneg _) (pow_nonneg hρ0 _)
        _ = (1 - 2 * δ) ^ (2 * k) * fourierCoeff (fun g => signVal (A g)) T ^ 2 := by ring
  rw [sum_fourierCoeff_sq_signVal, mul_one] at hsplit
  have hlow := sum_lowDegree_fourierCoeff_sq_le π k B A
  linarith

end Soundness

/-! ### Four-clause E3-CNF gadget for 3-bit XOR equations -/

section Gadget

variable {V : Type*}

/-- The **4-clause E3-CNF gadget** [Håstad, Section 2][Hastad2001] expressing the 3-bit linear
equation `(σ v₁ ^^ σ v₂) ^^ σ v₃ = b`: each of the four assignments to `(v₁, v₂, v₃)` with
`(σ v₁ ^^ σ v₂) ^^ σ v₃ = !b` is forbidden by a distinct 3-literal clause. -/
def xorThreeCNF (v₁ v₂ v₃ : V) (b : Bool) : CNF V :=
  [ [⟨v₁, true⟩, ⟨v₂, true⟩, ⟨v₃, b⟩],
    [⟨v₁, true⟩, ⟨v₂, false⟩, ⟨v₃, !b⟩],
    [⟨v₁, false⟩, ⟨v₂, true⟩, ⟨v₃, !b⟩],
    [⟨v₁, false⟩, ⟨v₂, false⟩, ⟨v₃, b⟩] ]

/-- The 4-clause XOR gadget has exactly 4 clauses. -/
@[simp]
theorem length_xorThreeCNF (v₁ v₂ v₃ : V) (b : Bool) :
    (xorThreeCNF v₁ v₂ v₃ b).length = 4 := rfl

/-- When `v₁, v₂, v₃` are distinct variables, every clause of `xorThreeCNF v₁ v₂ v₃ b` has
3 literals on 3 distinct variables (`CNF.IsExactThreeDistinct`). -/
theorem isExactThreeDistinct_xorThreeCNF {v₁ v₂ v₃ : V} (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ v₃)
    (h23 : v₂ ≠ v₃) (b : Bool) :
    (xorThreeCNF v₁ v₂ v₃ b).IsExactThreeDistinct := by
  intro C hC
  simp only [xorThreeCNF, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, by simp [List.nodup_cons, h12, h13, h23]⟩

/-- The 4-clause XOR gadget evaluates to `true` under `σ` iff `(σ v₁ ^^ σ v₂) ^^ σ v₃ = b`. -/
theorem eval_xorThreeCNF (v₁ v₂ v₃ : V) (b : Bool) (σ : V → Bool) :
    (xorThreeCNF v₁ v₂ v₃ b).eval σ = (((σ v₁ ^^ σ v₂) ^^ σ v₃) == b) := by
  simp only [xorThreeCNF, CNF.eval, List.all_cons, List.all_nil,
    Clause.eval, List.any_cons, List.any_nil, Literal.eval]
  cases σ v₁ <;> cases σ v₂ <;> cases σ v₃ <;> cases b <;> rfl

/-- **Exact clause-violation count of the 4-clause XOR gadget**: an assignment `σ` violates `0`
of the 4 clauses when `(σ v₁ ^^ σ v₂) ^^ σ v₃ = b` (all 4 clauses satisfied) and violates
exactly `1` of the 4 clauses when `(σ v₁ ^^ σ v₂) ^^ σ v₃ ≠ b` (3 of the 4 clauses satisfied). -/
theorem countUnsat_xorThreeCNF (v₁ v₂ v₃ : V) (b : Bool) (σ : V → Bool) :
    (xorThreeCNF v₁ v₂ v₃ b).countUnsat σ =
      if ((σ v₁ ^^ σ v₂) ^^ σ v₃) == b then 0 else 1 := by
  simp only [xorThreeCNF, CNF.countUnsat, List.countP_cons, List.countP_nil,
    Clause.eval, List.any_cons, List.any_nil, Literal.eval]
  obtain h1 | h1 := Bool.eq_false_or_eq_true (σ v₁) <;>
    obtain h2 | h2 := Bool.eq_false_or_eq_true (σ v₂) <;>
    obtain h3 | h3 := Bool.eq_false_or_eq_true (σ v₃) <;>
    cases b <;> simp [h1, h2, h3]

/-- The fraction of satisfied clauses in `xorThreeCNF v₁ v₂ v₃ false` is `1` (`4 / 4`) when
`(σ v₁ ^^ σ v₂) == σ v₃` and `3 / 4` otherwise:
`1 - countUnsat / 4 = 3 / 4 + 1 / 4 * (if (σ v₁ ^^ σ v₂) == σ v₃ then 1 else 0)`. -/
theorem one_sub_countUnsat_xorThreeCNF_div_four (v₁ v₂ v₃ : V) (σ : V → Bool) :
    1 - ((xorThreeCNF v₁ v₂ v₃ false).countUnsat σ : ℝ) / 4 =
      3 / 4 + 1 / 4 * (if (σ v₁ ^^ σ v₂) == σ v₃ then 1 else 0) := by
  rw [countUnsat_xorThreeCNF]
  obtain h1 | h1 := Bool.eq_false_or_eq_true (σ v₁) <;>
    obtain h2 | h2 := Bool.eq_false_or_eq_true (σ v₂) <;>
    obtain h3 | h3 := Bool.eq_false_or_eq_true (σ v₃) <;>
    simp only [h1, h2, h3] <;> norm_num

variable {β γ : Type*} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

/-- Bounding `hastadLinearCorr π δ B A ≤ 8 * ε` bounds the linear test acceptance by
`1 / 2 + 4 * ε`. -/
theorem hastadLinearProb_le_of_hastadLinearCorr_le (π : β → γ) (δ : ℝ)
    (B : (γ → Bool) → Bool) (A : (β → Bool) → Bool) {ε : ℝ}
    (h : hastadLinearCorr π δ B A ≤ 8 * ε) :
    hastadLinearProb π δ B A ≤ 1 / 2 + 4 * ε := by
  rw [hastadLinearProb_eq_add_hastadLinearCorr]
  linarith

end Gadget

end Cslib.PCP.Hastad
