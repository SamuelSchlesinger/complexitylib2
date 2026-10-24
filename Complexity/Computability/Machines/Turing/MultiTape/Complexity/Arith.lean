/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Mathlib.Data.Nat.Size
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Addition and multiplication with bounds of given degrees

Natural numbers are encoded in binary (`Turing.MultiTapeTM.encNat`). Addition is a left fold over
the digits of the first summand that keeps the carry, the rest of the digits of the second summand
and the digits of the sum so far; at the end the carry is added to the rest of the second summand.
Multiplication is a left fold over the digits of the first factor that keeps the product so far and
the second factor shifted by the digits read, adding the shifted factor for every digit `1`.

## Main results

* `Turing.MultiTapeTM.computableInDegree_add`: addition in quadratic time and space.
* `Turing.MultiTapeTM.computableInDegree_mul`: multiplication in cubic time and space.
-/

namespace Turing.MultiTapeTM

open NatSucc

namespace NatAdd

/-- The binary digits of `2 * n + b`, if they do not end in a zero. -/
lemma bits_bit (b : Bool) (n : ℕ) (h : n = 0 → b = true) :
    (2 * n + b.toNat).bits = b :: n.bits := by
  rw [← Nat.bit_val]
  exact Nat.bits_append_bit n b h

/-- The carry of adding three digits. -/
def carry (a b c : Bool) : Bool := a && b || c && (a ^^ b)

/-- Adds the digits `l` and `r` with the carry `c`, least significant first; `r` is padded with
zeros. -/
def addBits : Bool → List Bool → List Bool → List Bool
  | c, [], r => incr c r
  | c, a :: l, r => (a ^^ (r.headD false ^^ c)) :: addBits (carry a (r.headD false) c) l r.tail

lemma incr_bits (c : Bool) (n : ℕ) : incr c n.bits = (n + c.toNat).bits := by
  cases c
  · simp [incr]
  · exact (bits_succ n).symm

lemma addBits_bits (c : Bool) (m n : ℕ) : addBits c m.bits n.bits = (m + n + c.toNat).bits := by
  induction m using Nat.binaryRec' generalizing c n with
  | zero => simp [addBits, incr_bits]
  | bit a m hm ih =>
    rw [Nat.bits_append_bit _ _ hm, addBits]
    induction n using Nat.binaryRec' with
    | zero =>
      have h := ih (carry a false c) 0
      rw [Nat.zero_bits] at h
      rw [Nat.zero_bits, List.headD_nil, List.tail_nil, h, Nat.bit_val,
        show 2 * m + a.toNat + 0 + c.toNat = 2 * (m + 0 + (carry a false c).toNat) +
          (a ^^ (false ^^ c)).toNat by cases a <;> cases c <;> simp [carry]; omega,
        bits_bit]
      cases a <;> cases c <;> simp_all [carry]
    | bit b n hn _ =>
      rw [Nat.bits_append_bit _ _ hn, List.headD_cons, List.tail_cons, ih, Nat.bit_val,
        Nat.bit_val, show 2 * m + a.toNat + (2 * n + b.toNat) + c.toNat =
          2 * (m + n + (carry a b c).toNat) + (a ^^ (b ^^ c)).toNat by
          cases a <;> cases b <;> cases c <;> simp [carry] <;> omega, bits_bit]
      cases a <;> cases b <;> cases c <;> simp_all [carry]

/-- One round: add the digit `a`, the next digit of the rest `r` and the carry `c`. -/
def addStep (s : Bool × List Bool × List Bool) (a : Bool) : Bool × List Bool × List Bool :=
  (carry a (s.2.1.headD false) s.1, s.2.1.tail, s.2.2 ++ [a ^^ (s.2.1.headD false ^^ s.1)])

lemma foldl_addStep (l : List Bool) (c : Bool) (r out : List Bool) :
    let s := l.foldl addStep (c, r, out)
    out ++ addBits c l r = s.2.2 ++ incr s.1 s.2.1 := by
  induction l generalizing c r out with
  | nil => rfl
  | cons a l ih => simp [addBits, ← ih, addStep]

lemma length_foldl_addStep (l : List Bool) (s : Bool × List Bool × List Bool) :
    (l.foldl addStep s).2.1.length ≤ s.2.1.length ∧
      (l.foldl addStep s).2.2.length = s.2.2.length + l.length := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h₁, h₂⟩ := ih (addStep s a)
    exact ⟨h₁.trans (by simp [addStep]), h₂.trans (by simp [addStep]; omega)⟩

end NatAdd

open NatAdd ComputableInDegree

/-- **Addition is computable in quadratic time and space**, in the binary encoding. -/
public theorem computableInDegree_add :
    ComputableInDegree (fun p : ℕ × ℕ => p.1 + p.2) (encPair encNat encNat) encNat 2 1 := by
  let encS := encPair encBool (encPair encBits encBits)
  -- a round of the first fold
  have hstep : ComputableInDegree (fun p : _ × Bool => addStep p.1 p.2)
      (encPair encS encBool) encS 1 1 := by
    have hs := fst encS encBool
    have hr := hs.snd'.fst'
    have habc := (snd encS encBool).prod (((headD (enc₁ := encBool) false).comp hr).prod hs.fst')
    have hcarry := (of_finite (encIn := encPair encBool (encPair encBool encBool))
      (encMid := encBool) fun t : Bool × Bool × Bool => carry t.1 t.2.1 t.2.2).comp habc
    have hdigit := (of_finite (encIn := encPair encBool (encPair encBool encBool))
      (encMid := encBool) fun t : Bool × Bool × Bool => t.1 ^^ (t.2.1 ^^ t.2.2)).comp habc
    exact (hcarry.prod ((tail (enc₁ := encBool)).comp hr |>.prod
      (hs.snd'.snd'.append hdigit (encOut := encBits) fun _ => rfl))).mono
  have hsize : DegreeBounded (fun p : ℕ × ℕ => (encPair encNat encNat p).length)
      (fun p => 2 * (encPair encNat encNat p).length + 4) 1 :=
    (DegreeBounded.self.smul 2).add_const 4
  -- the first fold, over the digits of the first summand
  have hfold := foldl' (encL := encBits) (encB := encS)
    (list := fun p : ℕ × ℕ => p.1.bits) (init := fun p => (false, p.2.bits, []))
    (of_eq (encIn := encNat) (encMid := encBits) (f := Nat.bits) (fun _ => rfl) |>.comp
      (fst encNat encNat))
    ((const false).prod ((of_eq (encIn := encNat) (encMid := encBits) (f := Nat.bits)
      (fun _ => rfl) |>.comp (snd encNat encNat)).prod (const [])))
    hstep hsize ?_
  rotate_left
  · intro p i hi
    obtain ⟨h₁, h₂⟩ := length_foldl_addStep (p.1.bits.take i) (false, p.2.bits, [])
    simp only [encS, length_encPair, encBool_apply, List.length_singleton, encBits_apply,
      encNat_apply, List.length_take, List.length_nil] at h₁ h₂ ⊢
    omega
  -- the second fold adds the carry to the rest of the second summand
  have hfin : ComputableInDegree (fun s : Bool × List Bool × List Bool =>
      succFinish (s.2.1.foldl succStep (s.1, s.2.2))) encS encBits 2 1 := by
    have hs := of_eq (encIn := encS) (encMid := encS) (f := id) fun _ => rfl
    refine ((of_linear linear_succFinish).comp (foldl' (encL := encBits) (encB := encAcc)
      hs.snd'.fst' (hs.fst'.prod hs.snd'.snd')
      (of_linear linear_succStep) (B := fun s => (encS s).length + 3)
      (DegreeBounded.self.add_const 3) fun s i hi => ?_)).mono
    simp only [length_foldl_succStep, encS, length_encPair, encBool_apply, id_eq,
      List.length_singleton, encBits_apply, List.length_take]
    omega
  refine ((hfin.comp hfold).of_enc_eq fun p => ?_).mono
  simp only [Function.comp_apply, encBits_apply, encNat_apply]
  rw [succFinish_foldl, ← foldl_addStep, List.nil_append, addBits_bits]
  rfl

namespace NatMul

/-- One round: add the shifted factor `s.2` to the product `s.1` if the digit `a` is `1`, and shift
the factor. -/
def mulStep (s : ℕ × ℕ) (a : Bool) : ℕ × ℕ := (if a then s.1 + s.2 else s.1, s.2 + s.2)

lemma foldl_mulStep (m acc sh : ℕ) : (m.bits.foldl mulStep (acc, sh)).1 = acc + m * sh := by
  induction m using Nat.binaryRec' generalizing acc sh with
  | zero => simp
  | bit a m hm ih =>
    rw [Nat.bits_append_bit _ _ hm, List.foldl_cons, mulStep, ih, Nat.bit_val]
    cases a <;> simp <;> ring

lemma foldl_mulStep_le (l : List Bool) (acc sh : ℕ) :
    (l.foldl mulStep (acc, sh)).1 + sh ≤ acc + 2 ^ l.length * sh ∧
      (l.foldl mulStep (acc, sh)).2 = 2 ^ l.length * sh := by
  induction l generalizing acc sh with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h₁, h₂⟩ := ih (if a then acc + sh else acc) (sh + sh)
    have h : (if a then acc + sh else acc) ≤ acc + sh := by split <;> omega
    simp only [List.foldl_cons, mulStep, List.length_cons, pow_succ] at h₁ h₂ ⊢
    refine ⟨?_, by rw [h₂]; ring⟩
    nlinarith

lemma size_le_of_le {x n : ℕ} (i : ℕ) (h : x ≤ 2 ^ i * n) : x.size ≤ i + n.size :=
  Nat.size_le.2 (h.trans_lt (by
    rw [pow_add]; exact Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self n) (Nat.two_pow_pos i)))

end NatMul

open NatMul in
/-- **Multiplication is computable in cubic time and space**, in the binary encoding. -/
public theorem computableInDegree_mul :
    ComputableInDegree (fun p : ℕ × ℕ => p.1 * p.2) (encPair encNat encNat) encNat 3 1 := by
  let encS := encPair encNat encNat
  have hadd := computableInDegree_add
  -- a round of the fold
  have hstep : ComputableInDegree (fun p : (ℕ × ℕ) × Bool => mulStep p.1 p.2)
      (encPair encS encBool) encS 2 1 := by
    have hs := fst encS encBool
    exact (((snd encS encBool).ite ((hadd.comp hs).restrict _) (hs.fst'.restrict _)).prod
      (hadd.comp (hs.snd'.prod hs.snd'))).mono
  have hfold := foldl' (encL := encBits) (encB := encS)
    (list := fun p : ℕ × ℕ => p.1.bits) (init := fun p => (0, p.2))
    (of_eq (encIn := encNat) (encMid := encBits) (f := Nat.bits) (fun _ => rfl) |>.comp
      (fst encNat encNat))
    ((const 0).prod (snd encNat encNat)) hstep
    (B := fun p => 3 * (encPair encNat encNat p).length + 1)
    ((DegreeBounded.self.smul 3).add_const 1) fun p i hi => ?_
  · have h : ComputableInDegree (_ ∘ _) _ encNat 3 1 := ((fst encNat encNat).comp hfold).mono
    convert h using 1
    funext p
    simp [foldl_mulStep]
  · obtain ⟨h₁, h₂⟩ := foldl_mulStep_le (p.1.bits.take i) 0 p.2
    have hi' : (p.1.bits.take i).length ≤ p.1.size := by simp [← Nat.size_eq_bits_len]
    have hacc := size_le_of_le _ (by omega : (List.foldl mulStep (0, p.2) (p.1.bits.take i)).1 ≤
      2 ^ (p.1.bits.take i).length * p.2)
    have hsh := size_le_of_le _ h₂.le
    simp only [encS, length_encPair, encNat_apply, Nat.size_eq_bits_len] at hacc hsh hi' ⊢
    omega

end Turing.MultiTapeTM
