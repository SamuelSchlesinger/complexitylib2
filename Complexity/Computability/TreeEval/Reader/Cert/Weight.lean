/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Reader.Cert.Residue
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.GetD

/-!
# The weights of table entries within linear work space

The weight `Cslib.TreeEval.Reader.weight p ℓ k x y`, the product of `x j` or `1 - x j` over the low
bits of `k` and the same over its high bits for `y`, is tidily computable within work space
linear in the lengths of its encoded arguments and in `ℓ`. Its products are taken over a counter
rather than a list of indices, and they stay short: below `p`, or, for `p = 0`, no longer than the
registers together.

## Main results

* `Cslib.TreeEval.Reader.testBit_inSpace`: a bit of a binary natural.
* `Cslib.TreeEval.Reader.weight_inSpace`: the weight.
-/

@[expose] public section

namespace Cslib.TreeEval

namespace Reader

open Turing MultiTapeTM ComputableTidilyInSpace

/-- **A bit of a binary natural**, `k.testBit j` from `(k, j)`. -/
theorem testBit_inSpace :
    ComputableTidilyInSpace (fun q : ℕ × ℕ => q.1.testBit q.2) (encPair encNat encNat) encBool
      fun q => 32 * ((encPair encNat encNat q).length + 1) := by
  have hl : (fun q => (encPair encNat encNat q).length) ≼
      fun q => 8 * ((encPair encNat encNat q).length + 1) := .of_le fun _ => by omega
  have hbits : ComputableTidilyInSpace (fun q : ℕ × ℕ => q.1.bits) (encPair encNat encNat) encBits
      fun q => 8 * ((encPair encNat encNat q).length + 1) :=
    ((fst encNat encNat).weaken hl).of_enc_eq fun _ => rfl
  have htail : ComputableTidilyInSpace List.tail encBits encBits fun l => (encBits l).length :=
    of_inO (.of_linear (ListEncoding.tail encBool))
  have hlen (q : ℕ × ℕ) (i : ℕ) :
      (encBits (List.tail^[i] q.1.bits)).length ≤ (encNat q.1).length := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      simp only [encBits_apply, List.length_tail] at ih ⊢
      omega
  have h := iterate (n := fun q : ℕ × ℕ => q.2) ((snd encNat encNat).weaken hl) hbits htail
    (Q := fun q => (encNat q.1).length) (B := fun q => (encNat q.1).length)
    (fun q k _ => hlen q k) (fun q k _ => hlen q k)
  have hhead : ComputableTidilyInSpace (fun l : List Bool => l.headD false) encBits encBool
      fun l => (encBits l).length := of_inO (.of_linear (ListEncoding.headD false))
  refine (budget_comp_linear hhead h).mono_le (fun q => ?_) |>.of_enc_eq fun q => ?_
  · simp only [length_encPair]; omega
  · rw [List.tail_iterate, Nat.testBit_eq_inth]
    congr 1
    rw [List.headD_eq_head?_getD, List.head?_drop, List.getI_eq_getElem?_getD]
    rfl

/-! ### Half of a weight, over a counter -/

/-- A factor of half of a weight, on `((p, k, o), x)` and the counter and product `(j, a)`. -/
def halfStep (s : ((ℕ × ℕ × ℕ) × List ℕ) × ℕ × ℕ) : ((ℕ × ℕ × ℕ) × List ℕ) × ℕ × ℕ :=
  (s.1, s.2.1 + 1, mulMod s.1.1.1 s.2.2
    (chi s.1.1.1 (s.1.1.2.1.testBit (s.1.1.2.2 + s.2.1)) (s.1.2.getD s.2.1 0)))

theorem iterate_halfStep (p k o : ℕ) (x : List ℕ) (a : ℕ) (n : ℕ) :
    halfStep^[n] (((p, k, o), x), 0, a) = (((p, k, o), x), n, (List.range n).foldl
      (fun a j => mulMod p a (chi p (k.testBit (o + j)) (x.getD j 0))) a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, List.range_succ, List.foldl_append]
    rfl

theorem weight_eq (p ℓ k : ℕ) (x y : List ℕ) :
    weight p ℓ k x y = mulMod p (halfStep^[ℓ] (((p, k, 0), x), 0, 1 % p)).2.2
      (halfStep^[ℓ] (((p, k, ℓ), y), 0, 1 % p)).2.2 := by
  simp only [weight, iterate_halfStep, zero_add]

theorem length_chi_le (p : ℕ) (b : Bool) (x : ℕ) :
    (encNat (chi p b x)).length ≤ (encNat p).length + (encNat x).length + 1 := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · cases b
    · have : chi 0 false x = 1 := by simp [chi, addMod, negMod]
      rw [this]; simp
    · simp [chi]
  · have := ComputableTidilyInO.length_encNat_mono
      (show chi p b x ≤ p by cases b <;> exact (Nat.mod_lt _ hp).le)
    omega

theorem sum_length_getD_le (x : List ℕ) (j : ℕ) :
    ∑ i ∈ Finset.range j, (encNat (x.getD i 0)).length ≤ (encList encNat x).length := by
  induction x generalizing j with
  | nil => simp
  | cons a x ih =>
    rcases j with _ | j
    · simp
    · rw [Finset.sum_range_succ', length_encList]
      simp only [List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.sum_cons]
      have := ih j
      rw [length_encList] at this
      omega

/-- For `p = 0`, the products of half of a weight are no longer than their factors together. -/
theorem length_halfStep_zero_le (k o : ℕ) (x : List ℕ) (j : ℕ) :
    (encNat (halfStep^[j] (((0, k, o), x), 0, 1 % 0)).2.2).length ≤
      ∑ i ∈ Finset.range j, ((encNat (x.getD i 0)).length + 1) + 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Finset.sum_range_succ]
    have h₁ := length_encNat_mul_le (halfStep^[j] (((0, k, o), x), 0, 1 % 0)).2.2
      (chi 0 (k.testBit (o + j)) (x.getD j 0))
    have h₂ := length_chi_le 0 (k.testBit (o + j)) (x.getD j 0)
    rw [iterate_halfStep] at ih h₁ ⊢
    simp only [halfStep, mulMod, Nat.mod_zero] at ih h₁ ⊢
    have h₀ : (encNat 0).length = 0 := rfl
    omega

/-- **The products of half of a weight** are no longer than the prime, the register and the
counter together. -/
theorem length_halfStep_le (p k o : ℕ) (x : List ℕ) (j : ℕ) :
    (encNat (halfStep^[j] (((p, k, o), x), 0, 1 % p)).2.2).length ≤
      (encNat p).length + (encList encNat x).length + j + 1 := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have h₁ := length_halfStep_zero_le k o x j
    have h₂ := sum_length_getD_le x j
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at h₁
    omega
  · rcases j with _ | j
    · have := ComputableTidilyInO.length_encNat_mono (Nat.mod_le 1 p)
      simp only [Function.iterate_zero, id_eq]
      have h₁ : (encNat 1).length = 1 := rfl
      omega
    · have := ComputableTidilyInO.length_encNat_mono
        (show (halfStep^[j + 1] (((p, k, o), x), 0, 1 % p)).2.2 ≤ p by
          rw [Function.iterate_succ_apply', iterate_halfStep]
          simp only [halfStep, mulMod]
          exact (Nat.mod_lt _ hp).le)
      omega

theorem length_le_encList_getD (x : List ℕ) (j : ℕ) :
    (encNat (x.getD j 0)).length ≤ (encList encNat x).length := by
  by_cases h : j < x.length
  · rw [List.getD_eq_getElem _ _ h]; exact length_le_encList_of_mem encNat (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]; exact Nat.zero_le _

/-- The encoding of the states of `halfStep`. -/
abbrev encHalf : ((ℕ × ℕ × ℕ) × List ℕ) × ℕ × ℕ ↪ List Bool :=
  encPair (encPair encNat3 (encList encNat)) (encPair encNat encNat)

theorem halfStep_inSpace :
    ComputableTidilyInSpace halfStep encHalf encHalf fun s => (encHalf s).length + 1 := by
  have hl : (fun s => (encHalf s).length) ≼ fun s => (encHalf s).length + 1 :=
    .of_le fun _ => by omega
  have hpar := (fst (encPair encNat3 (encList encNat)) (encPair encNat encNat)).weaken hl
  have hja := (snd (encPair encNat3 (encList encNat)) (encPair encNat encNat)).weaken hl
  have hpko := fst' hpar
  have hx := snd' hpar
  have hp := fst' hpko
  have hk := fst' (snd' hpko)
  have ho := snd' (snd' hpko)
  have hj := fst' hja
  have ha := snd' hja
  have hsucc := budget_comp natSucc hj (.of_le_linear 2 2 fun s => by
    simp only [length_encPair]; omega)
  have hoj := budget_comp natAdd (budget_prod ho hj) (.of_le_linear 2 2 fun s => by
    simp only [length_encPair]; omega)
  have hbit := budget_comp testBit_inSpace (budget_prod hk hoj) (.of_le_linear 64 64 fun s => by
    have := length_encNat_add_le_add s.1.1.2.2 s.2.1
    simp only [length_encPair] at this ⊢; omega)
  have hxj := budget_comp getD (budget_prod hx hj) (.of_le_linear 64 64 fun s => by
    simp only [length_encPair]; omega)
  have hc := budget_comp chi_inSpace (budget_prod (budget_prod hp hxj) hbit)
    (.of_le_linear 64 64 fun s => by
      have := length_le_encList_getD s.1.2 s.2.1
      simp only [length_encPair, encBool_apply, List.length_singleton] at this ⊢; omega)
  have hm := budget_comp mulMod_inSpace (budget_prod hp (budget_prod ha hc))
    (.of_le_linear 64 64 fun s => by
      have h₁ := length_chi_le s.1.1.1 (s.1.1.2.1.testBit (s.1.1.2.2 + s.2.1)) (s.1.2.getD s.2.1 0)
      have h₂ := length_le_encList_getD s.1.2 s.2.1
      simp only [length_encPair] at h₁ h₂ ⊢; omega)
  exact budget_prod hpar (budget_prod hsucc hm)

/-- The encoding of the arguments of half of a weight. -/
abbrev encHalfIn : ((ℕ × ℕ × ℕ) × List ℕ) × ℕ ↪ List Bool :=
  encPair (encPair encNat3 (encList encNat)) encNat

/-- **Half of a weight**, from `(((p, k, o), x), n)`. -/
theorem half_inSpace :
    ComputableTidilyInSpace
      (fun h : ((ℕ × ℕ × ℕ) × List ℕ) × ℕ => (halfStep^[h.2] (h.1, 0, 1 % h.1.1.1)).2.2)
      encHalfIn encNat fun h => 256 * ((encHalfIn h).length + h.2 + 1) := by
  have hl : (fun h => (encHalfIn h).length) ≼ fun h => 64 * ((encHalfIn h).length + h.2 + 1) :=
    .of_le fun _ => by omega
  have hpar := (fst (encPair encNat3 (encList encNat)) encNat).weaken hl
  have hn := (snd (encPair encNat3 (encList encNat)) encNat).weaken hl
  have hp := fst' (fst' hpar)
  have hone := budget_comp natMod (budget_prod (budget_const (encB := encNat) 1 hl) hp)
    (.of_le_linear 64 64 fun h => by
      have h₁ : (encNat 1).length = 1 := rfl
      simp only [length_encPair]; omega)
  have hinit := budget_prod hpar (budget_prod (budget_const (encB := encNat) 0 hl) hone)
  have hlen (h : ((ℕ × ℕ × ℕ) × List ℕ) × ℕ) (j : ℕ) (hj : j ≤ h.2) :
      (encHalf (halfStep^[j] (h.1, 0, 1 % h.1.1.1))).length ≤
        4 * ((encHalfIn h).length + h.2 + 1) := by
    obtain ⟨⟨⟨p, k, o⟩, x⟩, n⟩ := h
    have h₁ := length_halfStep_le p k o x j
    have h₂ : (encNat j).length ≤ n := by
      have : (encNat j).length ≤ j := by
        rw [length_encNat_eq_size]; exact Nat.size_le.mpr Nat.lt_two_pow_self
      omega
    rw [iterate_halfStep] at h₁ ⊢
    simp only [length_encPair] at h₁ h₂ ⊢
    omega
  have h := iterate (n := fun h : ((ℕ × ℕ × ℕ) × List ℕ) × ℕ => h.2) hn hinit halfStep_inSpace
    (Q := fun h => 4 * ((encHalfIn h).length + h.2 + 1) + 1)
    (B := fun h => 4 * ((encHalfIn h).length + h.2 + 1))
    (fun h j hj => by have := hlen h j hj; dsimp only; omega) (fun h j hj => hlen h j hj)
  refine (snd' (snd' h)).mono_le fun h => ?_
  simp only [length_encPair] at *
  omega

/-- The encoding of the arguments of a weight. -/
abbrev encWeightIn : (ℕ × ℕ × ℕ) × List ℕ × List ℕ ↪ List Bool :=
  encPair encNat3 (encPair (encList encNat) (encList encNat))

/-- **The weight**, `weight p ℓ k x y` from `((p, ℓ, k), x, y)`. -/
theorem weight_inSpace :
    ComputableTidilyInSpace (fun w : (ℕ × ℕ × ℕ) × List ℕ × List ℕ =>
        weight w.1.1 w.1.2.1 w.1.2.2 w.2.1 w.2.2)
      encWeightIn encNat fun w => 64 * ((encWeightIn w).length + w.1.2.1 + 1) := by
  have hl : (fun w => (encWeightIn w).length) ≼ fun w => 64 * ((encWeightIn w).length + w.1.2.1 + 1)
    := .of_le fun _ => by omega
  have hpkl := (fst encNat3 (encPair (encList encNat) (encList encNat))).weaken hl
  have hxy := (snd encNat3 (encPair (encList encNat) (encList encNat))).weaken hl
  have hp := fst' hpkl
  have hℓ := fst' (snd' hpkl)
  have hk := snd' (snd' hpkl)
  have hx := fst' hxy
  have hy := snd' hxy
  have hS (o : (ℕ × ℕ × ℕ) × List ℕ × List ℕ → ℕ) (z : (ℕ × ℕ × ℕ) × List ℕ × List ℕ → List ℕ)
      (ho : (fun w => (encNat (o w)).length) ≼ fun w => 64 * ((encWeightIn w).length + w.1.2.1 + 1))
      (hz : (fun w => (encList encNat (z w)).length) ≼
        fun w => 64 * ((encWeightIn w).length + w.1.2.1 + 1)) :
      (fun w => 256 * ((encHalfIn (((w.1.1, w.1.2.2, o w), z w), w.1.2.1)).length +
        w.1.2.1 + 1)) ≼ fun w => 64 * ((encWeightIn w).length + w.1.2.1 + 1) := by
    obtain ⟨c₁, hc₁⟩ := ho
    obtain ⟨c₂, hc₂⟩ := hz
    refine ⟨2048 * (c₁ + c₂ + 1), fun w => ?_⟩
    have h₁ := hc₁ w
    have h₂ := hc₂ w
    dsimp only at h₁ h₂ ⊢
    generalize hW : 64 * ((encWeightIn w).length + w.1.2.1 + 1) = W at h₁ h₂ ⊢
    have h₃ : (encNat w.1.1).length + (encNat w.1.2.2).length + (encNat w.1.2.1).length +
        w.1.2.1 + 1 ≤ W := by
      rw [← hW]; simp only [length_encPair]; omega
    simp only [length_encPair]
    rw [show 2048 * (c₁ + c₂ + 1) * (W + 1) = 2048 * (c₁ * (W + 1)) + 2048 * (c₂ * (W + 1)) +
      2048 * (W + 1) by ring]
    omega
  have hzero : (fun w : (ℕ × ℕ × ℕ) × List ℕ × List ℕ => (encNat 0).length) ≼
      fun w => 64 * ((encWeightIn w).length + w.1.2.1 + 1) := .const _ _
  have hlo := budget_comp half_inSpace (budget_prod (budget_prod (budget_prod hp
    (budget_prod hk (budget_const (encB := encNat) 0 hl))) hx) hℓ)
    (hS (fun _ => 0) (fun w => w.2.1) hzero (.of_le fun w => by simp only [length_encPair]; omega))
  have hhi := budget_comp half_inSpace (budget_prod (budget_prod (budget_prod hp
    (budget_prod hk hℓ)) hy) hℓ)
    (hS (fun w => w.1.2.1) (fun w => w.2.2) (.of_le fun w => by simp only [length_encPair]; omega)
      (.of_le fun w => by simp only [length_encPair]; omega))
  refine (budget_comp mulMod_inSpace (budget_prod hp (budget_prod hlo hhi))
    (.of_le_linear 64 64 fun w => ?_)).of_enc_eq fun w => by rw [weight_eq]
  have h₁ := length_halfStep_le w.1.1 w.1.2.2 0 w.2.1 w.1.2.1
  have h₂ := length_halfStep_le w.1.1 w.1.2.2 w.1.2.1 w.2.2 w.1.2.1
  simp only [length_encPair] at h₁ h₂ ⊢
  omega

end Reader

end Cslib.TreeEval
