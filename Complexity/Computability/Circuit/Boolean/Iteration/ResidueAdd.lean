/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Word

/-!
# Carry-safe addition and subtraction of reduced residues

Widen both operands before adding, then reduce and truncate. The extra bit prevents
wraparound before modular reduction; comparisons and selections are charged.
For modular subtraction of two already reduced residues, no widening or general
division is needed: three subtractions, one comparison, and one word selection suffice.

## Main definitions

* `addResidue a b r`: modulus `a`, initial residue `b`, and increment `r`;
  return `b` unchanged when `b ≥ a`.
* `subtractResidues a b d`: modular difference `(a - b) mod d` of reduced residues `a, b < d`.

## Main results

* `toNat_addResidue`: exact modular addition of two reduced residues.
* `synthesis_addResidue`: at most `100 * (k + 1)` gates.
* `toNat_subtractResidues`: exact modular subtraction of two reduced residues.
* `synthesis_subtractResidues`: at most `140 * (k + 1)` gates.

## References

* Adapted from `lean/Proofs/{CounterRemainders,ReducedResidue}.lean` at revision `c4cfa198` of
  [S. Schlesinger, *Square-root circuit bounds for iterated functions*]
  [Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

variable {k n : ℕ}

/-- Add reduced residues `b` and `r` modulo `a` (requiring `b < a` and `r < a` for
modular-addition correctness), retaining `b` when `b ≥ a`.
Retaining the carry bit is essential: two valid residues can overflow `k` bits. -/
def addResidue (a b r : BitVec k) : BitVec k :=
  let sum := b.setWidth (k + 1) + r.setWidth (k + 1)
  if b.ult a then
    (if sum.ult (a.setWidth (k + 1)) then sum else sum - a.setWidth (k + 1)).setWidth k
  else b

/-- Addition of reduced residues is exact even when their narrow-word sum overflows. -/
theorem toNat_addResidue (d a b : BitVec k)
    (ha : a.toNat < d.toNat) (hb : b.toNat < d.toNat) :
    (addResidue d a b).toNat = (a.toNat + b.toNat) % d.toNat := by
  have hwide (v : BitVec k) : (v.setWidth (k + 1)).toNat = v.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
      (v.isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ k)))]
  have hfit : a.toNat + b.toNat < 2 ^ (k + 1) := by
    rw [pow_succ]
    have := d.isLt
    lia
  have hsum : (a.setWidth (k + 1) + b.setWidth (k + 1)).toNat = a.toNat + b.toNat := by
    rw [BitVec.toNat_add, hwide, hwide, Nat.mod_eq_of_lt hfit]
  unfold addResidue
  simp only [BitVec.ult, ha, decide_true, ite_true, hsum, hwide, decide_eq_true_eq]
  split_ifs with hs
  · rw [BitVec.toNat_setWidth, hsum, Nat.mod_eq_of_lt hs,
      Nat.mod_eq_of_lt (hs.trans d.isLt)]
  · have hle : d.setWidth (k + 1) ≤ a.setWidth (k + 1) + b.setWidth (k + 1) := by
      change (d.setWidth (k + 1)).toNat ≤ _
      rw [hwide, hsum]
      lia
    have hsmall : a.toNat + b.toNat - d.toNat < d.toNat := by lia
    rw [BitVec.toNat_setWidth, BitVec.toNat_sub_of_le hle, hsum, hwide,
      Nat.mod_eq_sub_mod (show d.toNat ≤ a.toNat + b.toNat by lia),
      Nat.mod_eq_of_lt hsmall, Nat.mod_eq_of_lt (hsmall.trans d.isLt)]

/-- Linear arithmetic and two selections, with a shared zero for widening. -/
theorem synthesis_addResidue (s : Set (BitString n → Bool)) (a b r : BitString n → BitVec k)
    (ha : wordWires a ⊆ s) (hb : wordWires b ⊆ s) (hr : wordWires r ⊆ s) :
    Synthesis Boolean.interpretation s
      (wordWires fun x => addResidue (a x) (b x) (r x)) (100 * (k + 1)) := by
  let s0 := s ∪ {fun _ : BitString n => false}
  have hz : (fun _ : BitString n => false) ∈ s0 := Or.inr rfl
  have hw (v : BitString n → BitVec k) (hv : wordWires v ⊆ s) :=
    wordWires_setWidth_subset (v := k + 1) (s := s0) (value := v) (fun _ h => Or.inl (hv h)) hz
  let sum := fun x => (b x).setWidth (k + 1) + (r x).setWidth (k + 1)
  let aw := fun x => (a x).setWidth (k + 1)
  have hadd := Synthesis.word_add (s := s0) _ _
    (fun i => hw b hb ⟨i, rfl⟩) (fun i => hw r hr ⟨i, rfl⟩)
  let s1 := s0 ∪ wordWires sum
  have hsum (i : Fin (k + 1)) : (fun x => (sum x).getLsbD i.val) ∈ s1 := Or.inr ⟨i, rfl⟩
  have haw (i : Fin (k + 1)) : (fun x => (aw x).getLsbD i.val) ∈ s1 :=
    Or.inl (hw a ha ⟨i, rfl⟩)
  have hsub := Synthesis.word_sub (s := s1) sum aw hsum haw
  have hlt := Synthesis.word_ult (s := s1) sum aw hsum haw
  let s2 := s1 ∪ (wordWires (fun x => sum x - aw x) ∪ {fun x => (sum x).ult (aw x)})
  let reduced := fun x => if (sum x).ult (aw x) then sum x else sum x - aw x
  have hred := Synthesis.word_mux (s := s2) sum (fun x => sum x - aw x)
    (fun x => (sum x).ult (aw x)) (Or.inr (Or.inr rfl))
    (fun i => Or.inl (hsum i)) (fun i => Or.inr (Or.inl ⟨i, rfl⟩))
  let s3 := s2 ∪ wordWires reduced
  have hre := wordWires_setWidth_subset (v := k) (s := s3) (value := reduced) (fun _ h => Or.inr h)
    (Or.inl (Or.inl (Or.inl hz)))
  have hactive := Synthesis.word_ult (s := s3) b a
    (fun i => Or.inl (Or.inl (Or.inl (Or.inl (hb ⟨i, rfl⟩)))))
    (fun i => Or.inl (Or.inl (Or.inl (Or.inl (ha ⟨i, rfl⟩)))))
  have hout := Synthesis.word_mux (s := s3 ∪ {fun x => (b x).ult (a x)})
    (fun x => (reduced x).setWidth k) b (fun x => (b x).ult (a x)) (Or.inr rfl)
    (fun i => Or.inl (hre ⟨i, rfl⟩))
    (fun i => Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hb ⟨i, rfl⟩))))))
  exact ((Synthesis.const (s := s) false).trans
    (hadd.trans ((hsub.union hlt).trans (hred.trans (hactive.trans hout))))).mono
      Set.Subset.rfl Set.Subset.rfl (by lia)

/-- Subtract reduced residues `a` and `b` modulo `d` without general division when `a < d` and
`b < d`. -/
def subtractResidues (a b d : BitVec k) : BitVec k :=
  if a.ult b then d - (b - a) else a - b

/-- Modular subtraction of reduced residues is exact without widening. -/
theorem toNat_subtractResidues (a b d : BitVec k)
    (ha : a.toNat < d.toNat) (hb : b.toNat < d.toNat) :
    (subtractResidues a b d).toNat = (a.toNat + d.toNat - b.toNat % d.toNat) % d.toNat := by
  unfold subtractResidues
  rw [Nat.mod_eq_of_lt hb]
  by_cases h : a.toNat < b.toNat
  · have hba : a ≤ b := by change a.toNat ≤ b.toNat; lia
    have hsub : (b - a).toNat = b.toNat - a.toNat := BitVec.toNat_sub_of_le hba
    have hle : b - a ≤ d := by change (b - a).toNat ≤ d.toNat; rw [hsub]; lia
    simp only [BitVec.ult, h, decide_true, ite_true, BitVec.toNat_sub_of_le hle, hsub]
    rw [Nat.mod_eq_of_lt (by lia : a.toNat + d.toNat - b.toNat < d.toNat)]
    lia
  · have hle : b ≤ a := by change b.toNat ≤ a.toNat; lia
    simp only [BitVec.ult, h, decide_false, Bool.false_eq_true, ite_false,
      BitVec.toNat_sub_of_le hle]
    rw [show a.toNat + d.toNat - b.toNat = a.toNat - b.toNat + d.toNat by lia,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by lia : a.toNat - b.toNat < d.toNat)]

/-- Three shared-carry subtractions, a comparison, and one word selection. -/
theorem synthesis_subtractResidues (s : Set (BitString n → Bool))
    (a b d : BitString n → BitVec k)
    (ha : wordWires a ⊆ s) (hb : wordWires b ⊆ s) (hd : wordWires d ⊆ s) :
    Synthesis Boolean.interpretation s
      (wordWires fun x => subtractResidues (a x) (b x) (d x)) (140 * (k + 1)) := by
  have hba := Synthesis.word_sub (s := s) b a (fun i => hb ⟨i, rfl⟩) (fun i => ha ⟨i, rfl⟩)
  let s1 := s ∪ wordWires (fun x => b x - a x)
  have hwrap := Synthesis.word_sub (s := s1) d (fun x => b x - a x)
    (fun i => Or.inl (hd ⟨i, rfl⟩)) (fun i => Or.inr ⟨i, rfl⟩)
  have hab := Synthesis.word_sub (s := s) a b (fun i => ha ⟨i, rfl⟩) (fun i => hb ⟨i, rfl⟩)
  have hlt := Synthesis.word_ult (s := s) a b (fun i => ha ⟨i, rfl⟩) (fun i => hb ⟨i, rfl⟩)
  let src := s ∪ ((wordWires (fun x => d x - (b x - a x)) ∪
    wordWires (fun x => a x - b x)) ∪ {fun x => (a x).ult (b x)})
  have hout := Synthesis.word_mux (s := src) (fun x => d x - (b x - a x))
    (fun x => a x - b x) (fun x => (a x).ult (b x)) (Or.inr (Or.inr rfl))
    (fun i => Or.inr (Or.inl (Or.inl ⟨i, rfl⟩)))
    (fun i => Or.inr (Or.inl (Or.inr ⟨i, rfl⟩)))
  exact ((((hba.trans hwrap).union hab).union hlt).trans hout).mono
    Set.Subset.rfl Set.Subset.rfl (by lia)

end Cslib.Circuits.Boolean.Iteration
