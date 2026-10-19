/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Arith
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Bitwise

/-!
# Polynomial-time arithmetic on binary naturals

Polynomial-time certificates for arithmetic on the binary encoding `Turing.MultiTapeTM.encNat`
(digits least significant first), as needed by the verifiers and reductions of the number problems
(`Cslib.Complexity.SubsetSum` and its relatives). Addition and multiplication are Christian
Reitwiessner's degree-bounded machines (`Turing.MultiTapeTM.computableTidilyInDegree_add`,
`Turing.MultiTapeTM.computableTidilyInDegree_mul`). A list is summed by a left fold whose
accumulator grows by at most one digit more than the length of the element added. Powers of two are
computed from a unary exponent by repeated doubling. Strict comparison scans bit positions: `m < n`
exactly when some position holds a one in `n` and a zero in `m` and all higher positions agree
(`Nat.lt_of_testBit`); the scan is quadratic in the number of digits.

## Main results

* `Nat.size_add_le`: a sum has at most one binary digit more than its summands together.
* `Nat.lt_iff_exists_testBit`: strict order through the highest differing bit.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_add`, `.binary_mul`: addition and
  multiplication.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_sum`: the sum of a list.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_two_pow`: `2 ^ k` in binary, from `k` in
  unary.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_lt`, `.binary_le`: comparisons.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_add'`, `.binary_lt'`, `.binary_le'`:
  composition rules for `fun_prop`.
-/

@[expose] public section

namespace Nat

/-- The binary length of a sum is at most the binary lengths of the summands together, plus one. -/
theorem size_add_le (m n : ℕ) : (m + n).size ≤ m.size + n.size + 1 := by
  refine Nat.size_le.2 ?_
  have hm := Nat.lt_size_self m
  have hn := Nat.lt_size_self n
  have h₁ : 2 ^ m.size ≤ 2 ^ (m.size + n.size) := Nat.pow_le_pow_right (by lia) (by lia)
  have h₂ : 2 ^ n.size ≤ 2 ^ (m.size + n.size) := Nat.pow_le_pow_right (by lia) (by lia)
  rw [Nat.pow_succ]
  lia

/-- `m < n` exactly when some bit position below the length of `n` holds a zero in `m` and a one
in `n`, and every higher position below the total length agrees. -/
theorem lt_iff_exists_testBit (m n : ℕ) :
    m < n ↔ ∃ i < n.size, m.testBit i = false ∧ n.testBit i = true ∧
      ∀ j < m.size + n.size, i < j → m.testBit j = n.testBit j := by
  have hbig {k j : ℕ} (hj : k.size ≤ j) : k.testBit j = false :=
    Nat.testBit_eq_false_of_lt ((Nat.lt_size_self k).trans_le (Nat.pow_le_pow_right (by lia) hj))
  constructor
  · intro hlt
    obtain ⟨i, hi, hhigh⟩ := Nat.exists_most_significant_bit
      (show m ^^^ n ≠ 0 from fun h => hlt.ne (Nat.eq_of_testBit_eq fun j => by
        have := Nat.testBit_xor m n j
        rw [h, Nat.zero_testBit] at this
        revert this
        cases m.testBit j <;> cases n.testBit j <;> simp))
    rw [Nat.testBit_xor] at hi
    have heq : ∀ j, i < j → m.testBit j = n.testBit j := fun j hj => by
      have := hhigh j hj
      rw [Nat.testBit_xor] at this
      revert this
      cases m.testBit j <;> cases n.testBit j <;> simp
    cases hmi : m.testBit i <;> cases hni : n.testBit i <;> rw [hmi, hni] at hi
    · simp at hi
    · refine ⟨i, ?_, hmi, hni, fun j _ hj => heq j hj⟩
      by_contra h
      rw [hbig (Nat.le_of_not_lt h)] at hni
      exact Bool.false_ne_true hni
    · exact absurd (Nat.lt_of_testBit i hni hmi fun j hj => (heq j hj).symm) (Nat.lt_asymm hlt)
    · simp at hi
  · rintro ⟨i, -, hm, hn, h⟩
    refine Nat.lt_of_testBit i hm hn fun j hj => ?_
    by_cases hj' : j < m.size + n.size
    · exact h j hj' hj
    · rw [hbig (by lia), hbig (by lia)]

end Nat

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- The binary digits of a natural number, as a raw bit string. -/
@[fun_prop]
theorem natBits : ComputableTidilyInPolyTime Nat.bits encNat encBits := of_eq fun _ => rfl

/-- Addition of binary naturals. -/
@[fun_prop]
theorem binary_add : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 + p.2)
    (encPair encNat encNat) encNat :=
  computableTidilyInDegree_add.computableTidilyInPolyTime

/-- Multiplication of binary naturals. -/
@[fun_prop]
theorem binary_mul : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 * p.2)
    (encPair encNat encNat) encNat :=
  computableTidilyInDegree_mul.computableTidilyInPolyTime

/-- Add computed binary values, fixing their intermediate encodings for proof search. -/
@[fun_prop]
theorem binary_add' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encNat)
    (hright : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun a => left a + right a) input encNat :=
  binary_add.comp (hleft.prod hright)

/-- The sum of a list of binary naturals, by a left fold of binary additions. -/
@[fun_prop]
theorem binary_sum : ComputableTidilyInPolyTime List.sum (encList encNat) encNat := by
  have hq := fst (encPair (encList encNat) encNat) encNat
  have h := foldlWith_of_bounded_growth (encA := encNat) (encL := encList encNat)
    (encB := encNat) (par := fun l : List ℕ => l) (list := fun l => l)
    (step := fun _ s a => s + a) id' id' (const 0) (binary_add.comp (hq.snd'.prod (snd _ _)))
    (growth := fun l => (encList encNat l).length + 1) (.add .self (.const 1))
    (fun l s a ha => by
      have := length_le_encList_of_mem encNat ha
      simp only [encNat_apply, Nat.size_eq_bits_len] at this ⊢
      have := Nat.size_add_le s a
      lia)
  simpa only [← List.sum_eq_foldl_nat] using h

/-- `2 ^ k` in binary, from `k` in unary, by doubling. -/
@[fun_prop]
theorem binary_two_pow : ComputableTidilyInPolyTime (fun k : ℕ => 2 ^ k) encUnary encNat := by
  have hfold (k : ℕ) : (List.replicate k true).foldl (fun n _ => n + n) 1 = 2 ^ k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ', List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
        Nat.pow_succ]
      lia
  have hq := fst encNat encBool
  have h := foldl_of_bounded_growth (encA := encBool) (encL := encBits) (encB := encNat)
    (list := fun k => List.replicate k true) (step := fun n _ => n + n)
    (of_eq (encIn := encUnary) (encMid := encBits) fun _ => rfl) (const 1)
    (binary_add.comp (hq.prod hq)) (growth := 1)
    (fun n _ => by
      simp only [encNat_apply, Nat.size_eq_bits_len]
      refine Nat.size_le.2 ?_
      have := Nat.lt_size_self n
      rw [Nat.pow_succ]
      lia)
  simpa only [hfold] using h

/-- Strict comparison of binary naturals by scanning bit positions. -/
@[fun_prop]
theorem binary_lt : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => decide (p.1 < p.2))
    (encPair encNat encNat) encBool := by
  have hscan : ComputableTidilyInPolyTime (fun p : ℕ × ℕ =>
      (List.range p.2.bits.length).any fun i =>
        !p.1.bits.getD i false && p.2.bits.getD i false &&
          (List.range (p.1.bits.length + p.2.bits.length)).all fun j =>
            decide (j ≤ i) || p.1.bits.getD j false == p.2.bits.getD j false)
      (encPair encNat encNat) encBool := by
    apply anyWithInput (by fun_prop)
    refine bool_and' (by fun_prop) ?_
    apply allWithInput (by fun_prop)
    fun_prop
  refine hscan.of_enc_eq fun p => congrArg encBool ?_
  have hbit (k i : ℕ) : k.bits.getD i false = k.testBit i := by
    rw [Nat.testBit_eq_inth, ← List.getD_default_eq_getI]
    rfl
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.lt_iff_exists_testBit]
  simp only [hbit, Nat.size_eq_bits_len, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    Bool.not_eq_true', List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine exists_congr fun i => and_congr_right fun _ => ?_
  rw [and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun j _ => ?_
  rw [← Nat.not_le, imp_iff_not_or, not_not]

/-- Comparison of binary naturals. -/
@[fun_prop]
theorem binary_le : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => decide (p.1 ≤ p.2))
    (encPair encNat encNat) encBool := by
  simpa only [Function.comp_def, ← decide_not, Nat.not_lt] using
    bool_not.comp (binary_lt.comp ((snd encNat encNat).prod (fst encNat encNat)))

/-- Strictly compare computed binary values, fixing their intermediate encodings. -/
@[fun_prop]
theorem binary_lt' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encNat)
    (hright : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun a => decide (left a < right a)) input encBool :=
  binary_lt.comp (hleft.prod hright)

/-- Compare computed binary values, fixing their intermediate encodings. -/
@[fun_prop]
theorem binary_le' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encNat)
    (hright : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun a => decide (left a ≤ right a)) input encBool :=
  binary_le.comp (hleft.prod hright)

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
