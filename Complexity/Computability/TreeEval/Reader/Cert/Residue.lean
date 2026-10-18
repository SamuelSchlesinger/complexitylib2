/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Reader.Defs
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib

/-!
# Residues within linear work space

The residue operations of `Cslib.TreeEval.Reader` are tidily computable within work space linear
in the lengths of their encoded arguments.

## Main results

* `Cslib.TreeEval.Reader.addMod_inSpace`, `.mulMod_inSpace`, `.negMod_inSpace`,
  `.powMod_inSpace`, `.chi_inSpace`: the residue operations.
-/

@[expose] public section

namespace Cslib.TreeEval

namespace Reader

open Turing MultiTapeTM ComputableTidilyInSpace

/-- The projections of a triple. -/
theorem proj3 :
    ComputableTidilyInSpace (fun q : ℕ × ℕ × ℕ => q.1) encNat3 encNat
      (fun q => (encNat3 q).length + 1) ∧
    ComputableTidilyInSpace (fun q : ℕ × ℕ × ℕ => q.2.1) encNat3 encNat
      (fun q => (encNat3 q).length + 1) ∧
    ComputableTidilyInSpace (fun q : ℕ × ℕ × ℕ => q.2.2) encNat3 encNat
      (fun q => (encNat3 q).length + 1) := by
  have hl : (fun q => (encNat3 q).length) ≼ fun q => (encNat3 q).length + 1 :=
    .of_le fun _ => by omega
  have h₂ := (snd encNat (encPair encNat encNat)).weaken hl
  exact ⟨(fst encNat (encPair encNat encNat)).weaken hl, fst' h₂, snd' h₂⟩

/-- The sum modulo `p`, from `(p, a, b)`. -/
theorem addMod_inSpace :
    ComputableTidilyInSpace (fun q : ℕ × ℕ × ℕ => addMod q.1 q.2.1 q.2.2) encNat3 encNat
      fun q => (encNat3 q).length + 1 := by
  obtain ⟨hp, ha, hb⟩ := proj3
  have hs := budget_comp natAdd (budget_prod ha hb) (.of_le_linear 2 2 fun q => by
    simp only [length_encPair]; omega)
  refine budget_comp natMod (budget_prod hs hp) (.of_le_linear 64 64 fun q => ?_) |>.of_enc_eq
    fun q => rfl
  have := length_encNat_add_le_add q.2.1 q.2.2
  simp only [length_encPair] at this ⊢
  omega

/-- The product modulo `p`, from `(p, a, b)`. -/
theorem mulMod_inSpace :
    ComputableTidilyInSpace (fun q : ℕ × ℕ × ℕ => mulMod q.1 q.2.1 q.2.2) encNat3 encNat
      fun q => (encNat3 q).length + 1 := by
  obtain ⟨hp, ha, hb⟩ := proj3
  have hs := budget_comp natMul (budget_prod ha hb) (.of_le_linear 64 64 fun q => by
    simp only [length_encPair]; omega)
  refine budget_comp natMod (budget_prod hs hp) (.of_le_linear 64 64 fun q => ?_) |>.of_enc_eq
    fun q => rfl
  have := length_encNat_mul_le q.2.1 q.2.2
  simp only [length_encPair] at this ⊢
  omega

/-- The negation modulo `p`, from `(p, a)`. -/
theorem negMod_inSpace :
    ComputableTidilyInSpace (fun q : ℕ × ℕ => negMod q.1 q.2) (encPair encNat encNat) encNat
      fun q => (encPair encNat encNat q).length + 1 := by
  have hl : (fun q => (encPair encNat encNat q).length) ≼
      fun q => (encPair encNat encNat q).length + 1 := .of_le fun _ => by omega
  have hp := (fst encNat encNat).weaken hl
  have ha := (snd encNat encNat).weaken hl
  have hm := budget_comp natMod (budget_prod ha hp) (.of_le_linear 64 64 fun q => by
    simp only [length_encPair]; omega)
  have hs := budget_comp natSub (budget_prod hm hp) (.of_le_linear 64 64 fun q => by
    have := ComputableTidilyInO.length_encNat_mono (Nat.mod_le q.2 q.1)
    simp only [length_encPair] at this ⊢; omega)
  refine budget_comp natMod (budget_prod hs hp) (.of_le_linear 64 64 fun q => ?_) |>.of_enc_eq
    fun q => rfl
  have := ComputableTidilyInO.length_encNat_mono (Nat.sub_le q.1 (q.2 % q.1))
  simp only [length_encPair] at this ⊢
  omega

/-- The residue of `x` or of `1 - x` modulo `p`, from `((p, x), b)`. -/
theorem chi_inSpace :
    ComputableTidilyInSpace (fun q : (ℕ × ℕ) × Bool => chi q.1.1 q.2 q.1.2)
      (encPair (encPair encNat encNat) encBool) encNat
      fun q => (encPair (encPair encNat encNat) encBool q).length + 1 := by
  have hl : (fun q => (encPair (encPair encNat encNat) encBool q).length) ≼
      fun q => (encPair (encPair encNat encNat) encBool q).length + 1 := .of_le fun _ => by omega
  have hpx := (fst (encPair encNat encNat) encBool).weaken hl
  have hb := (snd (encPair encNat encNat) encBool).weaken hl
  have hp := fst' hpx
  have hx := snd' hpx
  have hmod := budget_comp natMod (budget_prod hx hp) (.of_le_linear 64 64 fun q => by
    simp only [length_encPair]; omega)
  have hneg := budget_comp negMod_inSpace hpx (.of_le_linear 2 2 fun q => by
    simp only [length_encPair]; omega)
  have h₁ : ComputableTidilyInSpace (fun _ : (ℕ × ℕ) × Bool => 1)
      (encPair (encPair encNat encNat) encBool) encNat
      fun q => (encPair (encPair encNat encNat) encBool q).length + 1 := budget_const 1 hl
  have hadd := budget_comp addMod_inSpace (budget_prod hp (budget_prod h₁ hneg))
    (.of_le_linear 64 64 fun q => by
      have := ComputableTidilyInO.length_encNat_mono
        (show negMod q.1.1 q.1.2 ≤ q.1.1 from (Nat.mod_le _ _).trans (Nat.sub_le _ _))
      have h₁ : (encNat 1).length = 1 := rfl
      simp only [length_encPair] at this ⊢; omega)
  refine (budget_ite hb hmod hadd).of_enc_eq fun q => ?_
  simp only [chi]

/-- One factor of a power modulo `p`, on `(p, a, acc)`. -/
def powStep (q : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (q.1, q.2.1, mulMod q.1 q.2.2 q.2.1)

theorem iterate_powStep (p a n : ℕ) : powStep^[n] (p, a, 1 % p) = (p, a, powMod p a n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

theorem powMod_le {p a : ℕ} {k : ℕ} (hk : k ≤ p - 2) : powMod p a k ≤ p + 1 := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · obtain rfl : k = 0 := by omega
    simp [powMod]
  · cases k with
    | zero => exact (Nat.mod_le _ _).trans (by omega)
    | succ k => exact (Nat.mod_lt _ hp).le.trans (by omega)

/-- **The inverse of the unit of round `j`**, `unitInv p j` from `(p, j)`. -/
theorem unitInv_inSpace :
    ComputableTidilyInSpace (fun q : ℕ × ℕ => unitInv q.1 q.2) (encPair encNat encNat) encNat
      fun q => 64 * ((encPair encNat encNat q).length + 1) := by
  have hl : (fun q => (encPair encNat encNat q).length) ≼
      fun q => (encPair encNat encNat q).length + 1 := .of_le fun _ => by omega
  have hp := (fst encNat encNat).weaken hl
  have hj := (snd encNat encNat).weaken hl
  have hstep : ComputableTidilyInSpace powStep encNat3 encNat3
      fun q => (encNat3 q).length + 1 := by
    obtain ⟨hp, ha, hacc⟩ := proj3
    have hm := budget_comp mulMod_inSpace (budget_prod hp (budget_prod hacc ha))
      (.of_le_linear 2 2 fun q => by simp only [length_encPair]; omega)
    exact budget_prod hp (budget_prod ha hm)
  have hsucc := budget_comp natSucc hj (.of_le_linear 2 2 fun q => by
    simp only [length_encPair]; omega)
  have hone := budget_comp natMod (budget_prod (budget_const 1 hl) hp)
    (.of_le_linear 64 64 fun q => by
      have h₁ : (encNat 1).length = 1 := rfl
      simp only [length_encPair]; omega)
  have hinit := budget_prod hp (budget_prod hsucc hone)
  have hn := budget_comp natPred (budget_comp natPred hp (.of_le_linear 2 2 fun q => by
    simp only [length_encPair]; omega)) (.of_le_linear 4 4 fun q => by
      have := ComputableTidilyInO.length_encNat_mono (Nat.sub_le q.1 1)
      simp only [length_encPair] at this ⊢; omega)
  have hlen (q : ℕ × ℕ) (k : ℕ) (hk : k ≤ q.1 - 1 - 1) :
      (encNat3 (powStep^[k] (q.1, q.2 + 1, 1 % q.1))).length ≤
        4 * ((encPair encNat encNat q).length + 2) := by
    rw [iterate_powStep]
    have h₁ := ComputableTidilyInO.length_encNat_mono (powMod_le (p := q.1) (a := q.2 + 1)
      (k := k) (by omega))
    have h₂ := length_encNat_add_le_add q.1 1
    have h₃ := length_encNat_add_le_add q.2 1
    have h₄ : (encNat 1).length = 1 := rfl
    simp only [length_encPair] at h₁ h₂ h₃ ⊢
    omega
  have h := iterate (n := fun q : ℕ × ℕ => q.1 - 1 - 1) hn hinit hstep
    (Q := fun q => 4 * ((encPair encNat encNat q).length + 2) + 1)
    (B := fun q => 4 * ((encPair encNat encNat q).length + 2))
    (fun q k hk => by have := hlen q k hk; dsimp only; omega) (fun q k hk => hlen q k hk)
  refine (snd' (snd' h)).mono_le (fun q => ?_) |>.of_enc_eq fun q => ?_
  · have := ComputableTidilyInO.length_encNat_mono (show q.1 - 1 - 1 ≤ q.1 by omega)
    simp only [length_encPair] at this ⊢
    omega
  · rw [iterate_powStep]; rfl

end Reader

end Cslib.TreeEval
