/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Word

/-!
# Carry-safe addition of reduced residues

Widen both operands before adding, then reduce and truncate. The extra bit prevents
wraparound before modular reduction; comparisons and selections are charged.

## Main definitions

* `addResidue a b r`: modulus `a`, initial residue `b`, and increment `r`;
  return `b` unchanged when `b ≥ a`.

## Main results

* `toNat_addResidue`: exact modular addition of two reduced residues.
* `synthesis_addResidue`: at most `100 * (k + 1)` gates.

## References

* Adapted from `lean/Proofs/CounterRemainders.lean` at revision `c4cfa198` of
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

end Cslib.Circuits.Boolean.Iteration
