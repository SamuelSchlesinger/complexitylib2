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
(digits least significant first), the binary counterparts of the unary certificates in
`PolyTime/Nat.lean`. Addition and multiplication are Christian Reitwiessner's degree-bounded
machines (`Turing.MultiTapeTM.computableTidilyInDegree_add`,
`Turing.MultiTapeTM.computableTidilyInDegree_mul`). A list is summed by a left fold whose
accumulator grows by at most one digit more than the length of the element added. Powers of two are
computed from a unary exponent by repeated doubling. Strict comparison scans bit positions: `m < n`
exactly when some position holds a one in `n` and a zero in `m` and all higher positions agree
(`Nat.lt_of_testBit`); the scan is quadratic in the number of digits. Truncated subtraction is
schoolbook subtraction: a left fold over the digit pairs of both operands keeps a borrow and
appends one difference digit per position. A final borrow means that the difference is negative;
otherwise the digits are read back as a natural (`binary_foldr_bit`), dropping trailing zeros. The
verifiers and reductions of the number problems (`Cslib.Complexity.SubsetSum` and its relatives)
are built from these.

## Main definitions

* `Turing.MultiTapeTM.BinarySub.subStep`: one round of schoolbook subtraction with a borrow.

## Main results

* `Nat.size_add_le`: a sum has at most one binary digit more than its summands together.
* `Nat.lt_iff_exists_testBit`: strict order through the highest differing bit.
* `Nat.size_add_le_max`, `Nat.size_mul_le`, `Nat.size_pow_le`, `Nat.size_sum_le`: binary lengths
  of sums, products, powers and list sums.
* `Turing.MultiTapeTM.BinarySub.sub_eq`: truncated subtraction through the final borrow.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_add`, `.binary_mul`: addition and
  multiplication.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_sum`: the sum of a list.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_two_pow`: `2 ^ k` in binary, from `k` in
  unary.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_lt`, `.binary_le`: comparisons.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_sub`: truncated subtraction.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_pow`: a power to a unary exponent.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_foldr_bit`: a raw word of digits, read as
  a binary natural.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_add'`, `.binary_mul'`, `.binary_sub'`,
  `.binary_pow'`, `.binary_lt'`, `.binary_le'`: composition rules for `fun_prop`.
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

/-- The binary length of a sum is at most one more than the longer binary length of the
summands. -/
theorem size_add_le_max (m n : ℕ) : (m + n).size ≤ max m.size n.size + 1 := by
  refine Nat.size_le.2 ?_
  have hm := (Nat.lt_size_self m).trans_le
    (Nat.pow_le_pow_right (by lia) (le_max_left m.size n.size))
  have hn := (Nat.lt_size_self n).trans_le
    (Nat.pow_le_pow_right (by lia) (le_max_right m.size n.size))
  rw [Nat.pow_succ]
  lia

/-- The binary length of a product is at most the binary lengths of the factors together. -/
theorem size_mul_le (m n : ℕ) : (m * n).size ≤ m.size + n.size := by
  refine Nat.size_le.2 ?_
  rw [Nat.pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self m) (Nat.lt_size_self n)

/-- The binary length of a power is at most the exponent times the binary length of the base,
plus one for the zeroth power. -/
theorem size_pow_le (m k : ℕ) : (m ^ k).size ≤ k * m.size + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have := size_mul_le (m ^ k) m
    rw [Nat.pow_succ, Nat.succ_mul]
    lia

/-- A sum of naturals of binary length at most `b` has binary length at most `b` plus the binary
length of the number of summands. -/
theorem size_sum_le {l : List ℕ} {b : ℕ} (h : ∀ n ∈ l, n.size ≤ b) :
    l.sum.size ≤ b + l.length.size := by
  refine Nat.size_le.2 ?_
  have hsum : l.sum ≤ l.length * 2 ^ b := by
    simpa only [smul_eq_mul] using
      List.sum_le_length_nsmul l (2 ^ b) fun n hn => (Nat.size_le.1 (h n hn)).le
  rw [Nat.pow_add, Nat.mul_comm (2 ^ b)]
  exact hsum.trans_lt (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) (by positivity))

/-- A binary length is at most the number itself. -/
theorem size_le_self (n : ℕ) : n.size ≤ n :=
  Nat.size_le.2 Nat.lt_two_pow_self

end Nat

namespace Turing.MultiTapeTM.BinarySub

/-- The borrow out of a digit position: the minuend digit `x` minus the subtrahend digit `y` and
the incoming borrow `c` is negative. -/
def borrow (c x y : Bool) : Bool := !x && (y || c) || y && c

/-- One round of schoolbook subtraction, least significant digit first: append the difference
digit and pass on the borrow. -/
def subStep (s : Bool × List Bool) (d : Bool × Bool) : Bool × List Bool :=
  (borrow s.1 d.1 d.2, s.2 ++ [s.1 ^^ d.1 ^^ d.2])

/-- The digit pairs of two binary naturals at their first `size a + size b` positions. -/
def digitPairs (p : ℕ × ℕ) : List (Bool × Bool) :=
  (List.range (p.1.bits.length + p.2.bits.length)).map fun i =>
    (p.1.bits.getD i false, p.2.bits.getD i false)

lemma bits_getD (n i : ℕ) : n.bits.getD i false = n.testBit i := by
  rw [Nat.testBit_eq_inth, ← List.getD_default_eq_getI]
  rfl

lemma foldr_bit_lt (l : List Bool) : l.foldr Nat.bit 0 < 2 ^ l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldr_cons, Nat.bit_val, List.length_cons, Nat.pow_succ]
    cases b <;> simp only [Bool.toNat_true, Bool.toNat_false] <;> lia

lemma foldr_bit_testBit {n K : ℕ} (h : n.size ≤ K) :
    ((List.range K).map n.testBit).foldr Nat.bit 0 = n := by
  induction K generalizing n with
  | zero =>
    simp only [List.range_zero, List.map_nil, List.foldr_nil]
    exact (Nat.size_eq_zero.1 (Nat.le_zero.1 h)).symm
  | succ K ih =>
    have hn : (n / 2).size ≤ K := by
      have := Nat.size_le.1 h
      rw [Nat.pow_succ] at this
      exact Nat.size_le.2 (by lia)
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.foldr_cons]
    have hmap : n.testBit ∘ Nat.succ = (n / 2).testBit := funext fun i => Nat.testBit_succ n i
    rw [hmap, ih hn, ← Nat.shiftRight_one, Nat.bit_testBit_zero_shiftRight_one]

lemma foldl_subStep (ps : List (Bool × Bool)) (c : Bool) (out : List Bool) :
    ∃ ds, (ps.foldl subStep (c, out)).2 = out ++ ds ∧ ds.length = ps.length ∧
      ds.foldr Nat.bit 0 + (ps.map Prod.snd).foldr Nat.bit 0 + c.toNat =
        (ps.map Prod.fst).foldr Nat.bit 0 +
          (ps.foldl subStep (c, out)).1.toNat * 2 ^ ps.length := by
  induction ps generalizing c out with
  | nil => exact ⟨[], by simp⟩
  | cons d ps ih =>
    obtain ⟨x, y⟩ := d
    obtain ⟨ds, hds, hlen, hval⟩ := ih (borrow c x y) (out ++ [c ^^ x ^^ y])
    refine ⟨(c ^^ x ^^ y) :: ds, ?_, ?_, ?_⟩
    · simpa [subStep] using hds
    · simpa using hlen
    · simp only [List.foldl_cons, subStep] at hval ⊢
      simp only [List.map_cons, List.foldr_cons, Nat.bit_val, List.length_cons, Nat.pow_succ]
      cases c <;> cases x <;> cases y <;>
        simp only [borrow, Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false,
          Bool.or_true, Bool.or_false, Bool.true_xor, Bool.false_xor, Bool.toNat_true,
          Bool.toNat_false] at hval ⊢ <;> lia

/-- Truncated subtraction through the borrow of schoolbook subtraction: when the final borrow is
set the difference is negative, and otherwise the digits read off the difference. -/
lemma sub_eq (p : ℕ × ℕ) : p.1 - p.2 =
    if ((digitPairs p).foldl subStep (false, [])).1 then 0
    else ((digitPairs p).foldl subStep (false, [])).2.foldr Nat.bit 0 := by
  obtain ⟨ds, hds, hlen, hval⟩ := foldl_subStep (digitPairs p) false []
  have hfst : ((digitPairs p).map Prod.fst).foldr Nat.bit 0 = p.1 := by
    simp only [digitPairs, List.map_map, Function.comp_def, bits_getD]
    exact foldr_bit_testBit (by simp [Nat.size_eq_bits_len])
  have hsnd : ((digitPairs p).map Prod.snd).foldr Nat.bit 0 = p.2 := by
    simp only [digitPairs, List.map_map, Function.comp_def, bits_getD]
    exact foldr_bit_testBit (by simp [Nat.size_eq_bits_len])
  have hlt := foldr_bit_lt ds
  rw [hfst, hsnd, ← hlen] at hval
  rw [hds, List.nil_append]
  cases h : ((digitPairs p).foldl subStep (false, [])).1 <;>
    simp only [h, Bool.toNat_true, Bool.toNat_false, Bool.false_eq_true, ↓reduceIte] at hval ⊢ <;>
    lia

end Turing.MultiTapeTM.BinarySub

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

/-- Multiply computed binary values, fixing their intermediate encodings for proof search. -/
@[fun_prop]
theorem binary_mul' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encNat)
    (hright : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun a => left a * right a) input encNat :=
  binary_mul.comp (hleft.prod hright)

/-- A power of a binary natural to a unary exponent, by repeated multiplication. -/
@[fun_prop]
theorem binary_pow : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 ^ p.2)
    (encPair encNat encUnary) encNat := by
  have hfold (m k : ℕ) : (List.replicate k true).foldl (fun n _ => n * m) 1 = m ^ k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ', List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
        Nat.pow_succ]
  have hlist : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => List.replicate p.2 true)
      (encPair encNat encUnary) encBits :=
    (of_eq (encIn := encUnary) (encMid := encBits) fun _ => rfl).comp (snd encNat encUnary)
  have hq := fst (encPair encNat encNat) encBool
  have h := foldlWith_of_bounded_growth (encA := encBool) (encL := encBits) (encB := encNat)
    (par := fun p : ℕ × ℕ => p.1) (step := fun m n _ => n * m) (init := fun _ => 1)
    (fst encNat encUnary) hlist (const 1) (binary_mul.comp (hq.snd'.prod hq.fst'))
    (growth := fun p => (encPair encNat encUnary p).length) .self
    (fun p n _ _ => by
      have := Nat.size_mul_le n p.1
      have := length_le_encPair_left encNat encUnary p
      simp only [encNat_apply, Nat.size_eq_bits_len] at this ⊢
      lia)
  simpa only [hfold] using h

/-- Raise a computed binary value to a computed unary exponent, fixing the intermediate
encodings. -/
@[fun_prop]
theorem binary_pow' {α : Type} {input : α ↪ List Bool} {base exponent : α → ℕ}
    (hbase : ComputableTidilyInPolyTime base input encNat)
    (hexponent : ComputableTidilyInPolyTime exponent input encUnary) :
    ComputableTidilyInPolyTime (fun a => base a ^ exponent a) input encNat :=
  binary_pow.comp (hbase.prod hexponent)

/-- Read a raw bit string, least significant first, as a binary natural. Trailing zeros are
dropped, so any word of digits is accepted. -/
@[fun_prop]
theorem binary_foldr_bit :
    ComputableTidilyInPolyTime (fun l : List Bool => l.foldr Nat.bit 0) encBits encNat := by
  have hstep : ComputableTidilyInPolyTime (fun p : ℕ × Bool => Nat.bit p.2 p.1)
      (encPair encNat encBool) encNat := by
    have heq : (fun p : ℕ × Bool => Nat.bit p.2 p.1) =
        fun p => if p.2 then p.1 + p.1 + 1 else p.1 + p.1 := by
      funext ⟨n, b⟩
      cases b <;> simp only [Nat.bit_val, Bool.toNat_true, Bool.toNat_false, Bool.false_eq_true,
        ↓reduceIte] <;> lia
    rw [heq]
    fun_prop
  have h := foldl_of_bounded_growth (encA := encBool) (encL := encBits) (encB := encNat)
    (list := List.reverse) (init := fun _ => 0) (step := fun n b => Nat.bit b n)
    bitsReverse (const 0) hstep (growth := 1) (fun n b => by
      simp only [encNat_apply, Nat.size_eq_bits_len]
      by_cases hb : Nat.bit b n = 0
      · rw [hb]
        simp
      · exact (Nat.size_bit hb).le)
  simpa only [List.foldl_reverse] using h

/-- Truncated subtraction of binary naturals, by schoolbook subtraction with a borrow. -/
@[fun_prop]
theorem binary_sub : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 - p.2)
    (encPair encNat encNat) encNat := by
  have hpairs : ComputableTidilyInPolyTime BinarySub.digitPairs (encPair encNat encNat)
      (encList (encPair encBool encBool)) := by
    unfold BinarySub.digitPairs
    fun_prop
  have hstep : ComputableTidilyInPolyTime
      (fun p : (Bool × List Bool) × (Bool × Bool) => BinarySub.subStep p.1 p.2)
      (encPair (encPair encBool encBits) (encPair encBool encBool))
      (encPair encBool encBits) := by
    unfold BinarySub.subStep BinarySub.borrow
    fun_prop
  have hfold := foldl_of_bounded_growth (encA := encPair encBool encBool)
    (encL := encList (encPair encBool encBool)) (encB := encPair encBool encBits)
    (init := fun _ => (false, [])) hpairs (const _) hstep (growth := 1)
    (fun s d => by simp [BinarySub.subStep])
  have h := ((fst encBool encBits).comp hfold).ite' (const 0)
    (binary_foldr_bit.comp ((snd encBool encBits).comp hfold))
  convert h using 1
  funext p
  exact BinarySub.sub_eq p

/-- Subtract computed binary values, truncating at zero and fixing their intermediate
encodings. -/
@[fun_prop]
theorem binary_sub' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encNat)
    (hright : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun a => left a - right a) input encNat :=
  binary_sub.comp (hleft.prod hright)

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
