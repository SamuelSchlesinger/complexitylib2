/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Mathlib.Data.Nat.Bits
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Foldl
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
import all Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring

/-!
# The successor in binary

`encNat` encodes a natural number by its binary digits, least significant first (`Nat.bits`).
The successor is a left fold over the digits that keeps a carry and appends one digit per round,
followed by a final carry digit. Its tidy computability is derived from that of the fold
(`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl`) and of the parts of a round.

## Main definitions

* `Turing.MultiTapeTM.encNat`: natural numbers encoded by their binary digits.

## Main results

* `Turing.MultiTapeTM.computableTidilyInTimeAndSpace_succ`: the successor is tidily computable in
  quadratic time and linear space.
-/

namespace Turing.MultiTapeTM

/-- Natural numbers encoded by their binary digits, least significant first. -/
@[expose] public def encNat : ℕ ↪ List Bool :=
  ⟨Nat.bits, fun m n h => Nat.eq_of_testBit_eq fun i => by simp [Nat.testBit_eq_inth, h]⟩

@[simp]
public lemma encNat_apply (n : ℕ) : encNat n = n.bits := rfl

namespace NatSucc

/-- Adds the carry `c` to the binary digits `l`, least significant first. -/
@[expose] public def incr : Bool → List Bool → List Bool
  | false, l => l
  | true, [] => [true]
  | true, false :: l => true :: l
  | true, true :: l => false :: incr true l

public lemma bits_succ (n : ℕ) : (n + 1).bits = incr true n.bits := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · rfl
      · rw [Nat.bit1_bits, Nat.bit0_bits m (by omega), incr]
    · rw [Nat.bit1_bits, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, Nat.bit0_bits _ (by omega),
        ih m (by omega), incr]

/-- One round: add the carry to the digit `b`, append the resulting digit and keep the carry. -/
public def succStep (p : Bool × List Bool) (b : Bool) : Bool × List Bool :=
  (p.1 && b, p.2 ++ [p.1 ^^ b])

/-- Appends the final carry digit. -/
public def succFinish (p : Bool × List Bool) : List Bool := if p.1 then p.2 ++ [true] else p.2

public lemma succFinish_foldl (l : List Bool) (c : Bool) (out : List Bool) :
    succFinish (l.foldl succStep (c, out)) = out ++ incr c l := by
  induction l generalizing c out with
  | nil => cases c <;> simp [succFinish, incr]
  | cons b l ih => cases c <;> cases b <;> simp [succStep, ih, incr]

lemma bits_succ_eq_foldl (n : ℕ) :
    (n + 1).bits = succFinish (n.bits.foldl succStep (true, [])) := by
  rw [succFinish_foldl, bits_succ, List.nil_append]

public lemma length_foldl_succStep (l : List Bool) (p : Bool × List Bool) :
    (l.foldl succStep p).2.length = p.2.length + l.length := by
  induction l generalizing p <;> simp [*, succStep]; omega

/-- The encoding of the accumulator: the carry and the digits so far. -/
public abbrev encAcc : Bool × List Bool ↪ List Bool := encPair encBool encBits

public lemma length_encAcc (p : Bool × List Bool) : (encAcc p).length = p.2.length + 3 := by
  simp

open ComputableInLinearTimeAndSpace

/-- A round is tidily computable in linear time and space. -/
public lemma linear_succStep :
    ComputableInLinearTimeAndSpace (fun p => succStep p.1 p.2)
      (encPair encAcc encBool) encAcc := by
  have hacc : ComputableInLinearTimeAndSpace Prod.fst (encPair encAcc encBool) encAcc :=
    (PairEncoding.fst encBool)
  have hcarry : ComputableInLinearTimeAndSpace (fun p : (Bool × List Bool) × Bool => p.1.1)
      (encPair encAcc encBool) encBool :=
    (show ComputableInLinearTimeAndSpace _ _ _ from
      (PairEncoding.fst encBits)).comp hacc
  have hdigit : ComputableInLinearTimeAndSpace (fun p : (Bool × List Bool) × Bool => p.2)
      (encPair encAcc encBool) encBool :=
    (PairEncoding.snd encAcc)
  have hdigits : ComputableInLinearTimeAndSpace (fun p : (Bool × List Bool) × Bool => p.1.2)
      (encPair encAcc encBool) encBits :=
    (show ComputableInLinearTimeAndSpace _ _ _ from
      (PairEncoding.snd encBool)).comp hacc
  have hand : ComputableInLinearTimeAndSpace (fun p : (Bool × List Bool) × Bool =>
      p.1.1 && p.2) (encPair encAcc encBool) encBool := by
    convert hdigit.ite (hcarry.restrict _) ((const false).restrict _) using 1
    funext p
    cases p.2 <;> simp
  have hnot : ComputableInLinearTimeAndSpace (fun p : (Bool × List Bool) × Bool => !p.1.1)
      (encPair encAcc encBool) encBool := by
    convert hcarry.ite ((const false).restrict _) ((const true).restrict _) using 1
    funext p
    cases p.1.1 <;> rfl
  have hxor : ComputableInLinearTimeAndSpace (fun p : (Bool × List Bool) × Bool =>
      p.1.1 ^^ p.2) (encPair encAcc encBool) encBool := by
    convert hdigit.ite (hnot.restrict _) (hcarry.restrict _) using 1
    funext p
    cases p.2 <;> simp
  exact hand.pair (hdigits.append hxor (encOut := encBits) fun _ => rfl)

/-- The final carry digit is appended in linear time and space. -/
public lemma linear_succFinish :
    ComputableInLinearTimeAndSpace succFinish encAcc encBits := by
  have hdigits : ComputableInLinearTimeAndSpace Prod.snd encAcc encBits :=
    (PairEncoding.snd encBool)
  have happend : ComputableInLinearTimeAndSpace (fun p => p.2 ++ [true]) encAcc encBits :=
    hdigits.append (const (encMid := encBool) true) (encOut := encBits) fun _ => rfl
  have hcarry : ComputableInLinearTimeAndSpace Prod.fst encAcc encBool :=
    (PairEncoding.fst encBits)
  exact hcarry.ite (happend.restrict _) (hdigits.restrict _)

end NatSucc

open NatSucc in
/-- The successor is tidily computable in quadratic time and linear space, in the binary encoding
`encNat`. -/
public theorem computableTidilyInTimeAndSpace_succ :
    ∃ c, ComputableTidilyInTimeAndSpace (· + 1) encNat encNat
      (fun n => c * ((encNat n).length + 1) ^ 2) (fun n => c * ((encNat n).length + 1)) := by
  obtain ⟨cl, hlist⟩ := Internal.normalizeLinear
    (ComputableInLinearTimeAndSpace.of_eq (f := Nat.bits)
      (encIn := encNat) (encMid := encBits) fun _ => rfl)
  obtain ⟨ci, hinit⟩ := Internal.normalizeLinear
    (ComputableInLinearTimeAndSpace.const (encIn := encNat) (encMid := encAcc) (true, []))
  obtain ⟨cs, hstep⟩ := Internal.normalizeLinear linear_succStep
  -- the bounds of a round and of the state of the fold
  have hlen (n i : ℕ) : (((n.bits.take i).foldl succStep (true, [])).2).length ≤ n.bits.length := by
    rw [length_foldl_succStep]
    simp
  obtain ⟨cf, hfold⟩ := ComputableTidilyInTimeAndSpace.foldl (encA := encBool) (encL := encBits)
    (encBA := encPair encAcc encBool) (encS := encPair encBits encAcc)
    (encO := encOption (encPair encBits encAcc))
    (hlist.mono (t' := fun n => (cl + ci) * ((encNat n).length + 1))
      (s' := fun n => (cl + ci) * ((encNat n).length + 1))
      (fun n => by ring_nf; omega) (fun n => by ring_nf; omega))
    (hinit.mono (fun n => by ring_nf; omega) (fun n => by ring_nf; omega)) hstep
    (tMax := fun n => cs * (2 * (encNat n).length + 9))
    (sMax := fun n => cs * (2 * (encNat n).length + 9))
    (lMax := fun n => 2 * (encNat n).length + 4)
    (fun n i _ => Nat.mul_le_mul_left cs (by simp; have := hlen n i; omega))
    (fun n i _ => Nat.mul_le_mul_left cs (by simp; have := hlen n i; omega))
    (fun n i hi => by simp [length_foldl_succStep]; omega)
  obtain ⟨cg, hfinish⟩ := Internal.normalizeLinear linear_succFinish
  -- vendored: crei's `comp` is `comp_linear` here, as cslib #1111 restates `comp`
  obtain ⟨cc, h⟩ := ComputableTidilyInTimeAndSpace.comp_linear hfinish hfold
  obtain ⟨k, S, _, tm, htm⟩ := h
  refine ⟨cf * (cl + ci + 9 * cs + 5) + 4 * (cg + cc), k, S, inferInstance, tm, fun n => ?_⟩
  have hmid : (encAcc (n.bits.foldl succStep (true, []))).length = n.bits.length + 3 := by
    rw [length_encAcc, length_foldl_succStep]
    simp
  change tm.ComputesTidilyInTimeAndSpace _ (n + 1).bits _ _
  rw [bits_succ_eq_foldl]
  refine (htm n).mono ?_ ?_ <;>
  · simp only [hmid, encNat_apply]
    ring_nf
    omega

end Turing.MultiTapeTM
