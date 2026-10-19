/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.AffineDisperser.Moore
public import Mathlib.FieldTheory.Finite.Trace
import Mathlib

/-!
# Products of Moore determinants of independent subspaces

Let `F` be a finite field with `2 ^ n` elements in which every proper subfield has at most
`2 ^ s` elements. Given `𝔽₂`-subspaces `Yᵢ` of `F` of dimensions `dᵢ > s` and integers
`2 ≤ kᵢ < dᵢ` with `∑ᵢ (dᵢ - kᵢ) ≥ n + 1 - maxᵢ dᵢ`, every nonzero `𝔽₂`-linear functional
`z ↦ Tr (μ z)` is nonzero on some product `∏ᵢ Δ(uᵢ)` of Moore determinants of families
`uᵢ : Fin kᵢ → Yᵢ`. This is the algebraic heart of the disperser for independent affine sources
of Ben-Sasson and Kopparty [BenSassonKopparty2012, Theorem 6.1], with the hypothesis that no
`Yᵢ` lies in a multiple of a proper subfield replaced by `dᵢ > s`; for a field of prime degree
`s = 1`.

The proof follows [BenSassonKopparty2012]. Parametrize `Yᵢ` by its image-subspace polynomial
`Qᵢ`; then `w ↦ Tr (μ ∏ᵢ Δ(Qᵢ ∘ wᵢ))` is a reduced polynomial function whose coefficient at
`∏ᵢ ∏ₗ wᵢₗ ^ 2 ^ τᵢₗ` is `∑_ρ μ ^ 2 ^ ρ ∏ᵢ per(Mᵢ[τᵢ - ρ]) ^ 2 ^ ρ`, where
`Mᵢ[τ] = (aᵢ (τ l - m) ^ 2 ^ m)`. Using the zero pattern of the coefficients `aᵢ`
(`Cslib.FiniteField.CoeffPattern`) we choose `τ` so that every `Mᵢ[τᵢ]` is triangular with
nonzero diagonal while for every rotation `ρ ≠ 0` some `Mᵢ[τᵢ - ρ]` has a zero row
[BenSassonKopparty2012, Claims 6.2 and 6.3]. That coefficient is then `μ ∏ᵢ per(Mᵢ[τᵢ]) ≠ 0`,
and a reduced polynomial with a nonzero coefficient is a nonzero function.

## Main results

* `Cslib.AffineDisperser.eq_zero_of_forall_sum_mul_prod_pow_eq_zero`: distinct reduced monomial
  functions over a finite field are linearly independent.
* `Cslib.AffineDisperser.exists_trace_mul_prod_det_mooreMatrix_ne_zero`: the theorem above.

## References

* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
-/

@[expose] public section

universe u

namespace Cslib.AffineDisperser

open Module Cslib.FiniteField

variable {F : Type*} [Field F]

/-- `eq_zero_of_forall_sum_mul_prod_pow_eq_zero` with the variables in the universe of `F`. -/
private theorem eq_zero_of_forall_sum_mul_prod_pow_eq_zero_aux {F : Type u} [Field F] [Fintype F]
    {σ : Type u} {T : Type*} [Fintype σ] [Fintype T]
    (e : T → σ → ℕ) (he : Function.Injective e) (hlt : ∀ t v, e t v < Fintype.card F)
    (C : T → F) (h : ∀ x : σ → F, ∑ t, C t * ∏ v, x v ^ e t v = 0) (t : T) : C t = 0 := by
  classical
  let m : T → σ →₀ ℕ := fun t => Finsupp.equivFunOnFinite.symm (e t)
  have hm : Function.Injective m := fun t t' htt' =>
    he (by simpa [m] using congrArg (⇑) htt')
  let p : MvPolynomial σ F := ∑ t, MvPolynomial.monomial (m t) (C t)
  have heval : ∀ x, MvPolynomial.eval x p = ∑ t, C t * ∏ v, x v ^ e t v := fun x => by
    simp only [p, map_sum, MvPolynomial.eval_monomial]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finsupp.prod_fintype _ _ fun v => pow_zero _]
    rfl
  have hp : p = 0 := by
    refine MvPolynomial.eq_zero_of_eval_eq_zero σ F p (fun x => by rw [heval]; exact h x) ?_
    rw [MvPolynomial.mem_restrictDegree]
    intro s hs v
    obtain ⟨t', -, ht'⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hs)
    have := MvPolynomial.support_monomial_subset ht'
    rw [Finset.mem_singleton] at this
    subst this
    have := hlt t' v
    simp only [m, Finsupp.equivFunOnFinite_symm_apply_apply]
    omega
  have := congrArg (fun q : MvPolynomial σ F => q.coeff (m t)) hp
  simp only [p, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial] at this
  rw [Finset.sum_eq_single t] at this
  · simpa using this
  · intro t' _ ht'
    rw [ite_eq_right_iff]
    exact fun h => absurd (hm h) ht'
  · simp

/-- **Reduced monomials are independent**: over a finite field `F`, if a combination
`∑ₜ Cₜ ∏ᵥ xᵥ ^ eₜᵥ` of monomials with pairwise distinct exponent vectors, all exponents below
`|F|`, vanishes at every point, then all coefficients vanish. -/
theorem eq_zero_of_forall_sum_mul_prod_pow_eq_zero {F : Type u} [Field F] [Fintype F]
    {σ T : Type*} [Fintype σ] [Fintype T]
    (e : T → σ → ℕ) (he : Function.Injective e) (hlt : ∀ t v, e t v < Fintype.card F)
    (C : T → F) (h : ∀ x : σ → F, ∑ t, C t * ∏ v, x v ^ e t v = 0) (t : T) : C t = 0 := by
  let eσ : σ ≃ ULift.{u} (Fin (Fintype.card σ)) := (Fintype.equivFin σ).trans Equiv.ulift.symm
  refine eq_zero_of_forall_sum_mul_prod_pow_eq_zero_aux (fun t v => e t (eσ.symm v))
    (fun t t' htt' => he (funext fun v => by simpa using congrFun htt' (eσ v)))
    (fun t v => hlt t _) C (fun x => ?_) t
  have key : ∀ t, ∏ v, (x ∘ eσ) v ^ e t v = ∏ v, x v ^ e t (eσ.symm v) := fun t =>
    Fintype.prod_equiv eσ _ _ fun v => by simp
  have := h (x ∘ eσ)
  simp_rw [key] at this
  exact this

/-! ### Choosing the monomial -/

section Choice

variable {n : ℕ} [NeZero n] {d k : ℕ} {a : ZMod n → F}

/-- `τ` makes the matrix `(a (τ l - m) ^ 2 ^ m)_{l, m}` upper triangular with nonzero
diagonal. -/
private def IsTriangular (a : ZMod n → F) (τ : Fin k → ZMod n) : Prop :=
  (∀ l : Fin k, a (τ l - (l : ℕ)) ≠ 0) ∧ ∀ l m : Fin k, m < l → a (τ l - (m : ℕ)) = 0

/-- The rotation of `τ` by `ρ` gives the matrix `(a (τ l - ρ - m) ^ 2 ^ m)` a zero row. -/
private def Kills (a : ZMod n → F) (τ : Fin k → ZMod n) (ρ : ZMod n) : Prop :=
  ∃ l : Fin k, ∀ m : Fin k, a (τ l - ρ - (m : ℕ)) = 0

private theorem coeffPattern_neg_eq_zero (hp : CoeffPattern n d a) {x : ℕ} (hx1 : 1 ≤ x)
    (hxd : x < d) : a (-(x : ZMod n)) = 0 := by
  have hdn := hp.le
  have : -(x : ZMod n) = ((n - d + (d - x) : ℕ) : ZMod n) := by
    rw [show n - d + (d - x) = n - x by omega, Nat.cast_sub (by omega : x ≤ n), ZMod.natCast_self,
      zero_sub]
  rw [this]
  exact hp.canonical _ (by omega) (by omega)

/-- A row `τ l` kills the `d - k` rotations just above it. -/
private theorem kills_of_eq_add (hp : CoeffPattern n d a) (hkd : k < d) {τ : Fin k → ZMod n}
    (l : Fin k) {c : ℕ} (hc1 : 1 ≤ c) (hc : c ≤ d - k) {ρ : ZMod n} (hρ : ρ = τ l + c) :
    Kills a τ ρ := by
  refine ⟨l, fun m => ?_⟩
  have : τ l - ρ - ((m : ℕ) : ZMod n) = -((c + m : ℕ) : ZMod n) := by
    rw [hρ]
    push_cast
    ring
  rw [this]
  exact coeffPattern_neg_eq_zero hp (by omega) (by have := m.2; omega)

/-- The choice `(b, n - d + 1, …, n - d + k - 1)` [BenSassonKopparty2012, Claim 6.2, first
case]. -/
private theorem exists_tau_one (hp : CoeffPattern n d a) (hk : 2 ≤ k) (hkd : k < d) {b : ℕ}
    (hb : a b ≠ 0) :
    ∃ τ : Fin k → ZMod n, IsTriangular a τ ∧
      (∀ c, 1 ≤ c → c ≤ d - k → Kills a τ ((b + c : ℕ) : ZMod n)) ∧
      ∀ ρ : ℕ, n - d + 2 ≤ ρ → ρ < n → Kills a τ ρ := by
  have hdn := hp.le
  refine ⟨fun l => if (l : ℕ) = 0 then (b : ZMod n) else ((n - d + l : ℕ) : ZMod n),
    ⟨fun l => ?_, fun l m hml => ?_⟩, fun c hc1 hc => ?_, fun ρ hρ1 hρn => ?_⟩
  · by_cases hl : (l : ℕ) = 0
    · simp only [hl, ↓reduceIte, Nat.cast_zero, sub_zero]
      exact hb
    · simp only [hl, ↓reduceIte]
      rw [← Nat.cast_sub (by omega), show n - d + l - l = n - d by omega]
      exact hp.lead
  · have hml' : (m : ℕ) < l := hml
    have hl : (l : ℕ) ≠ 0 := by omega
    simp only [hl, ↓reduceIte]
    rw [← Nat.cast_sub (by omega), show n - d + l - m = n - d + (l - m) by omega]
    exact hp.canonical _ (by omega) (by have := l.2; omega)
  · refine kills_of_eq_add hp hkd ⟨0, by omega⟩ hc1 hc ?_
    simp
  · refine kills_of_eq_add hp hkd ⟨min (k - 1) (ρ - (n - d) - 1), by omega⟩
      (c := ρ - (n - d) - min (k - 1) (ρ - (n - d) - 1)) (by omega) (by omega) ?_
    have hl0 : min (k - 1) (ρ - (n - d) - 1) ≠ 0 := by omega
    simp only [hl0, ↓reduceIte]
    rw [← Nat.cast_add, show n - d + min (k - 1) (ρ - (n - d) - 1) +
      (ρ - (n - d) - min (k - 1) (ρ - (n - d) - 1)) = ρ by omega]

/-- **The choice of the rows of one block** [BenSassonKopparty2012, Claims 6.2 and 6.3]: for every
`ℓ ≤ n - d` some triangular `τ` kills the rotations `ℓ + 1, …, ℓ + (d - k)`. -/
private theorem exists_tau_window (hp : CoeffPattern n d a) (hk : 2 ≤ k) (hkd : k < d) {ℓ : ℕ}
    (hℓ : ℓ ≤ n - d) :
    ∃ τ : Fin k → ZMod n, IsTriangular a τ ∧
      ∀ ρ : ℕ, ℓ + 1 ≤ ρ → ρ ≤ ℓ + (d - k) → Kills a τ ρ := by
  classical
  have hdn := hp.le
  by_cases hℓ0 : a ℓ ≠ 0
  · obtain ⟨τ, hτ, hkill, -⟩ := exists_tau_one hp hk hkd hℓ0
    refine ⟨τ, hτ, fun ρ hρ1 hρ2 => ?_⟩
    have := hkill (ρ - ℓ) (by omega) (by omega)
    rwa [show ℓ + (ρ - ℓ) = ρ by omega] at this
  push Not at hℓ0
  have hℓlt : ℓ < n - d := lt_of_le_of_ne hℓ fun h => hp.lead (h ▸ hℓ0)
  -- `jh`: the last nonzero coefficient below `ℓ`
  set jh := Nat.findGreatest (fun j => a (j : ZMod n) ≠ 0) ℓ with hjh
  have hjh_ne : a jh ≠ 0 :=
    Nat.findGreatest_spec (P := fun j => a (j : ZMod n) ≠ 0) (Nat.zero_le ℓ)
      (by simpa using hp.zero_ne)
  have hjh_lt : jh < ℓ := lt_of_le_of_ne (Nat.findGreatest_le ℓ) fun h => hjh_ne (h ▸ hℓ0)
  have hjh_max : ∀ j, jh < j → j ≤ ℓ → a j = 0 := fun j h1 h2 => by
    by_contra h
    exact absurd (Nat.le_findGreatest h2 h) (not_le.2 h1)
  -- `js`: the first nonzero coefficient above `ℓ`
  have hex : ∃ j, ℓ < j ∧ a (j : ZMod n) ≠ 0 := ⟨n - d, hℓlt, hp.lead⟩
  set js := Nat.find hex with hjs
  have hjs_spec : ℓ < js ∧ a js ≠ 0 := Nat.find_spec hex
  have hjs_le : js ≤ n - d := Nat.find_min' hex ⟨hℓlt, hp.lead⟩
  have hgap : ∀ j, jh < j → j < js → a j = 0 := fun j h1 h2 => by
    rcases le_or_gt j ℓ with h | h
    · exact hjh_max j h1 h
    · by_contra hne
      exact Nat.find_min hex h2 ⟨h, hne⟩
  -- the gap is shorter than `d - 1` [BenSassonKopparty2012, Lemma 3.10]
  have hjs_bound : js ≤ jh + d - 1 := by
    obtain ⟨c, hc, hne⟩ := hp.gap (jh + 1) (by omega) (by omega)
    by_contra hcon
    exact hne (hgap _ (by omega) (by omega))
  set s := min (js - jh - 1) (k - 1) with hs
  refine ⟨fun l => if (l : ℕ) = 0 then (js : ZMod n)
      else if (l : ℕ) ≤ s then ((jh + l : ℕ) : ZMod n) else ((n - d + l : ℕ) : ZMod n),
    ⟨fun l => ?_, fun l m hml => ?_⟩, fun ρ hρ1 hρ2 => ?_⟩
  · by_cases hl0 : (l : ℕ) = 0
    · simp only [hl0, ↓reduceIte, Nat.cast_zero, sub_zero]
      exact hjs_spec.2
    · by_cases hls : (l : ℕ) ≤ s
      · simp only [hl0, hls, ↓reduceIte]
        rw [← Nat.cast_sub (by omega), show jh + l - l = jh by omega]
        exact hjh_ne
      · simp only [hl0, hls, ↓reduceIte]
        rw [← Nat.cast_sub (by omega), show n - d + l - l = n - d by omega]
        exact hp.lead
  · have hml' : (m : ℕ) < l := hml
    have hl0 : (l : ℕ) ≠ 0 := by omega
    by_cases hls : (l : ℕ) ≤ s
    · simp only [hl0, hls, ↓reduceIte]
      rw [← Nat.cast_sub (by omega)]
      exact hgap _ (by omega) (by omega)
    · simp only [hl0, hls, ↓reduceIte]
      rw [← Nat.cast_sub (by omega), show n - d + l - m = n - d + (l - m) by omega]
      exact hp.canonical _ (by omega) (by have := l.2; omega)
  · by_cases hρs : ρ ≤ jh + s + (d - k)
    · -- a row placed in the gap
      refine kills_of_eq_add hp hkd ⟨min s (ρ - jh - 1), by omega⟩
        (c := ρ - jh - min s (ρ - jh - 1)) (by omega) (by omega) ?_
      have hl0 : min s (ρ - jh - 1) ≠ 0 := by omega
      have hls : min s (ρ - jh - 1) ≤ s := min_le_left _ _
      simp only [hl0, hls, ↓reduceIte]
      rw [← Nat.cast_add, show jh + min s (ρ - jh - 1) + (ρ - jh - min s (ρ - jh - 1)) = ρ by
        omega]
    · -- the row `js`
      refine kills_of_eq_add hp hkd ⟨0, by omega⟩ (c := ρ - js) (by omega) (by omega) ?_
      simp only [↓reduceIte]
      rw [← Nat.cast_add, show js + (ρ - js) = ρ by omega]

/-- **The choice of the monomial** [BenSassonKopparty2012, Claims 6.2 and 6.3]: given coefficient
patterns of dimensions `dᵢ`, the largest at `i₁`, and `2 ≤ kᵢ < dᵢ` with
`n < d_{i₁} + ∑ᵢ (dᵢ - kᵢ)`, there are triangular `τᵢ` such that every nonzero rotation is killed
by some block. -/
private theorem exists_tau {ι : Type*} [Fintype ι] (a : ι → ZMod n → F) (d k : ι → ℕ)
    (hp : ∀ i, CoeffPattern n (d i) (a i)) (hk : ∀ i, 2 ≤ k i) (hkd : ∀ i, k i < d i)
    (i₁ : ι) (hmax : ∀ i, d i ≤ d i₁) (hsum : n < d i₁ + ∑ i, (d i - k i)) :
    ∃ τ : (i : ι) → Fin (k i) → ZMod n, (∀ i, IsTriangular (a i) (τ i)) ∧
      ∀ ρ : ZMod n, ρ ≠ 0 → ∃ i, Kills (a i) (τ i) ρ := by
  classical
  let T := Fintype.card ι
  let e : Fin T ≃ ι := (Fintype.equivFin ι).symm
  let δ : ι → ℕ := fun i => d i - k i
  let δ' : ℕ → ℕ := fun q => if h : q < T then (if e ⟨q, h⟩ ≠ i₁ then δ (e ⟨q, h⟩) else 0) else 0
  let ℓ : ℕ → ℕ := fun p => δ i₁ + ∑ q ∈ Finset.range p, δ' q
  have hℓsucc : ∀ p, ℓ (p + 1) = ℓ p + δ' p := fun p => by
    simp only [ℓ, Finset.sum_range_succ, add_assoc]
  have hℓT : ℓ T = ∑ i, δ i := by
    simp only [ℓ]
    rw [← Fin.sum_univ_eq_sum_range δ' T]
    have : ∀ q : Fin T, δ' q = if e q ≠ i₁ then δ (e q) else 0 := fun q => by simp [δ', q.2]
    simp_rw [this]
    rw [Equiv.sum_comp e (fun i => if i ≠ i₁ then δ i else 0), ← Finset.sum_filter,
      Finset.filter_ne', Finset.add_sum_erase _ _ (Finset.mem_univ i₁)]
  have hblock : ∀ i, ∃ τ : Fin (k i) → ZMod n, IsTriangular (a i) τ ∧
      (i = i₁ → ∀ ρ : ℕ, 1 ≤ ρ → ρ < n → (ρ ≤ δ i₁ ∨ n - d i₁ + 2 ≤ ρ) → Kills (a i) τ ρ) ∧
      (i ≠ i₁ → ℓ (e.symm i) ≤ n - d i₁ → ∀ ρ : ℕ, ℓ (e.symm i) + 1 ≤ ρ →
        ρ ≤ ℓ (e.symm i) + δ i → Kills (a i) τ ρ) := by
    intro i
    have h0 : a i ((0 : ℕ) : ZMod n) ≠ 0 := by simpa using (hp i).zero_ne
    by_cases hi : i = i₁
    · subst hi
      obtain ⟨τ, hτ, h1, h2⟩ := exists_tau_one (hp i) (hk i) (hkd i) h0
      refine ⟨τ, hτ, fun _ ρ hρ1 hρn hρ => ?_, fun h => absurd rfl h⟩
      rcases hρ with hρ | hρ
      · have := h1 ρ hρ1 hρ
        rwa [zero_add] at this
      · exact h2 ρ hρ hρn
    · by_cases hℓ : ℓ (e.symm i) ≤ n - d i₁
      · obtain ⟨τ, hτ, hkill⟩ := exists_tau_window (hp i) (hk i) (hkd i)
          (ℓ := ℓ (e.symm i)) (by have := hmax i; omega)
        exact ⟨τ, hτ, fun h => absurd h hi, fun _ _ => hkill⟩
      · obtain ⟨τ, hτ, -, -⟩ := exists_tau_one (hp i) (hk i) (hkd i) h0
        exact ⟨τ, hτ, fun h => absurd h hi, fun _ h => absurd h hℓ⟩
  choose τ hτ hτ₁ hτw using hblock
  refine ⟨τ, hτ, fun ρ hρ => ?_⟩
  have hρr : ρ = (ρ.val : ZMod n) := (ZMod.natCast_zmod_val ρ).symm
  have hr1 : 1 ≤ ρ.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero ρ).2 hρ)
  have hrn : ρ.val < n := ZMod.val_lt ρ
  rw [hρr]
  by_cases hr : ρ.val ≤ δ i₁ ∨ n - d i₁ + 2 ≤ ρ.val
  · exact ⟨i₁, hτ₁ i₁ rfl ρ.val hr1 hrn hr⟩
  push Not at hr
  obtain ⟨hrδ, hrd⟩ := hr
  have hdn := (hp i₁).le
  have hex : ∃ p, ρ.val ≤ ℓ (p + 1) := ⟨T, by rw [hℓsucc, hℓT]; simp only [δ] at hsum ⊢; omega⟩
  set p := Nat.find hex
  have hp1 : ρ.val ≤ ℓ (p + 1) := Nat.find_spec hex
  have hp0 : ℓ p < ρ.val := by
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h]
      simp only [ℓ, Finset.range_zero, Finset.sum_empty, add_zero]
      exact hrδ
    · have := Nat.find_min hex (show p - 1 < p by omega)
      rw [show p - 1 + 1 = p by omega] at this
      omega
  have hδ' : 0 < δ' p := by
    rw [hℓsucc] at hp1
    omega
  have hpT : p < T := by
    by_contra h
    simp [δ', h] at hδ'
  have hi : e ⟨p, hpT⟩ ≠ i₁ := by
    intro h
    simp [δ', hpT, h] at hδ'
  have hδ'i : δ' p = δ (e ⟨p, hpT⟩) := by simp [δ', hpT, hi]
  have hsymm : ((e.symm (e ⟨p, hpT⟩) : Fin T) : ℕ) = p := by rw [e.symm_apply_apply]
  refine ⟨e ⟨p, hpT⟩, hτw _ hi (by rw [hsymm]; omega) ρ.val (by rw [hsymm]; omega) ?_⟩
  rw [hsymm]
  rw [hℓsucc, hδ'i] at hp1
  exact hp1

end Choice

variable [Finite F] [Algebra (ZMod 2) F]

/-- **Moore products of independent sources** (after [BenSassonKopparty2012, Theorem 6.1]): in a
field with `2 ^ n` elements whose proper subfields have at most `2 ^ s` elements, let `Yᵢ` be
subspaces of dimensions `dᵢ > s`, and `2 ≤ kᵢ < dᵢ` with `n < d_{i₀} + ∑ᵢ (dᵢ - kᵢ)` for some
`i₀`. Then for every `μ ≠ 0` there are families `uᵢ : Fin kᵢ → Yᵢ` whose Moore determinants
satisfy `Tr (μ ∏ᵢ Δ(uᵢ)) ≠ 0`. -/
theorem exists_trace_mul_prod_det_mooreMatrix_ne_zero {ι : Type*} [Fintype ι] {n s : ℕ}
    (hn : finrank (ZMod 2) F = n) (hs : ∀ K : Subfield F, K ≠ ⊤ → Nat.card K ≤ 2 ^ s)
    (Y : ι → Submodule (ZMod 2) F) (k : ι → ℕ) (hk : ∀ i, 2 ≤ k i)
    (hkY : ∀ i, k i < finrank (ZMod 2) (Y i)) (hsY : ∀ i, s < finrank (ZMod 2) (Y i)) (i₀ : ι)
    (hsum : n < finrank (ZMod 2) (Y i₀) + ∑ i, (finrank (ZMod 2) (Y i) - k i))
    {μ : F} (hμ : μ ≠ 0) :
    ∃ u : (i : ι) → Fin (k i) → F, (∀ i l, u i l ∈ Y i) ∧
      Algebra.trace (ZMod 2) F (μ * ∏ i, (mooreMatrix (u i)).det) ≠ 0 := by
  sorry

end Cslib.AffineDisperser
