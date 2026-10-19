/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Synthesis
public import Init.Data.BitVec.Bitblast
public import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Linarith

/-!
# Bounded-word arithmetic and table selection

Words are Lean's `BitVec`s, stored least significant bit first. A word-valued function is
available when each of its coordinate functions is (`wordWires`). Addition, subtraction,
unsigned comparison, equality, complementation, constants and multiplexing are synthesized over
the De Morgan basis with explicit gate counts; their semantics are the `BitVec` operations, by
the bit-blasting identities of the core library. Selecting one of `R` records by a binary index
charges a comparison per record and every selected bit (`synthesis_selectBits`).

The bounds are deliberately loose where that keeps the proofs short: each output bit of a sum
recomputes its own carry chain.

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.word`: assemble a word from its bits.
* `Cslib.Circuits.Boolean.Iteration.wordWires`: the coordinate functions of a word.
* `Cslib.Circuits.Boolean.Iteration.selectBits`: select a record by its binary index.

## Main results

* `Cslib.Circuits.Synthesis.beq`, `Cslib.Circuits.Synthesis.mux`: equality of two available
  functions in five gates and a multiplexer in four.
* `Cslib.Circuits.Boolean.Iteration.synthesis_add`, `synthesis_sub`, `synthesis_ult`,
  `synthesis_word_eq`, `synthesis_word_mux`: word operations.
* `Cslib.Circuits.Boolean.Iteration.selectBits_eq`: in-range indices select exactly.
* `Cslib.Circuits.Boolean.Iteration.synthesis_selectBits`: the cost of table selection.

## References

* Adapted from `lean/Proofs/{Synthesis,Arithmetic,Words}.lean` in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits

namespace Synthesis

open Boolean

variable {n : ℕ} {s : Set (BooleanFunction n)} {f g a b : BooleanFunction n}

/-- Equality of two available functions costs five gates. -/
theorem beq (hf : f ∈ s) (hg : g ∈ s) :
    Synthesis interpretation s {fun x => decide (f x = g x)} 5 := by
  have h := ((of_mem hf).and (of_mem hg)).or ((of_mem hf).not.and (of_mem hg).not)
  convert h using 2
  funext x
  cases f x <;> cases g x <;> rfl

/-- One available control bit selects between two available functions in four gates. -/
theorem mux (hf : f ∈ s) (ha : a ∈ s) (hb : b ∈ s) :
    Synthesis interpretation s {fun x => if f x then a x else b x} 4 := by
  have h := ((of_mem hf).and (of_mem ha)).or ((of_mem hf).not.and (of_mem hb))
  convert h using 2
  funext x
  cases f x <;> simp

end Synthesis

namespace Boolean.Iteration

variable {n k w R : ℕ}

/-! ### Words -/

/-- Assemble a word from its coordinate bits, least significant first. -/
def word (bits : Fin w → Bool) : BitVec w :=
  (BitVec.ofBoolListLE (List.ofFn bits)).cast (by simp)

@[simp] theorem word_bit (bits : Fin w → Bool) (i : Fin w) :
    (word bits).getLsbD i.val = bits i := by
  rw [word, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD]
  simp

@[simp] theorem word_getElem (bits : Fin w → Bool) (i : ℕ) (hi : i < w) :
    (word bits)[i] = bits ⟨i, hi⟩ := word_bit bits ⟨i, hi⟩

@[simp] theorem word_bits (a : BitVec w) : word (fun i : Fin w => a.getLsbD i.val) = a :=
  BitVec.eq_of_getLsbD_eq fun i hi => word_bit _ ⟨i, hi⟩

/-- The coordinate functions of a word-valued function. -/
def wordWires (a : BitString n → BitVec w) : Set (BooleanFunction n) :=
  Set.range fun i : Fin w => fun x => (a x).getLsbD i.val

/-- Zero extension and truncation only rewire available bits and the false constant. -/
theorem wordWires_setWidth_subset {v : ℕ} {s : Set (BooleanFunction n)}
    {value : BitString n → BitVec w} (hv : wordWires value ⊆ s) (hz : (fun _ => false) ∈ s) :
    wordWires (fun x => (value x).setWidth v) ⊆ s := by
  rintro _ ⟨bit, rfl⟩
  simp only [BitVec.getLsbD_setWidth, bit.isLt, decide_true, Bool.true_and]
  by_cases hi : bit.val < w
  · exact hv ⟨⟨bit.val, hi⟩, rfl⟩
  · simpa only [BitVec.getLsbD_of_ge _ _ (by omega : w ≤ bit.val)] using hz

/-! ### Arithmetic -/

section Arithmetic

variable (s : Set (BooleanFunction n)) (a b : BitString n → BitVec w)
variable (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
variable (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s)

include ha hb

/-- A carry chain uses four gates per bit and its initial constant. -/
theorem synthesis_carry (c : Bool) (t : ℕ) (ht : t ≤ w) :
    Synthesis interpretation s {fun x => BitVec.carry t (a x) (b x) c} (4 * t + 1) := by
  induction t with
  | zero => simpa using Synthesis.const c
  | succ t ih =>
    have hc := ih (by omega)
    have hat := Synthesis.of_mem (I := interpretation) (ha ⟨t, by omega⟩)
    have hbt := Synthesis.of_mem (I := interpretation) (hb ⟨t, by omega⟩)
    have h := (hat.and hbt).or ((hat.or hbt).and hc)
    have heq : (fun x => (a x).getLsbD t && (b x).getLsbD t ||
        ((a x).getLsbD t || (b x).getLsbD t) && BitVec.carry t (a x) (b x) c) =
        (fun x => BitVec.carry (t + 1) (a x) (b x) c) := by
      funext x
      rw [BitVec.carry_succ]
      cases (a x).getLsbD t <;> cases (b x).getLsbD t <;>
        cases BitVec.carry t (a x) (b x) c <;> rfl
    convert h using 1
    · rw [heq]
    · omega

/-- Addition with an initial carry; each output bit recomputes its carry chain. -/
theorem synthesis_addCarry (c : Bool) :
    Synthesis interpretation s
      (wordWires fun x => a x + b x + BitVec.setWidth w (BitVec.ofBool c))
      (40 * (w + 1) ^ 2) := by
  have hs := Synthesis.family (I := interpretation) (s := s)
    (fun i : Fin w => fun x =>
      (a x + b x + BitVec.setWidth w (BitVec.ofBool c)).getLsbD i.val)
    (fun _ => 40 * (w + 1)) fun i => ?_
  · exact hs.mono Set.Subset.rfl Set.Subset.rfl (by simp; nlinarith)
  · have h := (Synthesis.of_mem (ha i)).xor
      ((Synthesis.of_mem (hb i)).xor (synthesis_carry s a b ha hb c i.val i.isLt.le))
    have heq : (fun x => (a x + b x + BitVec.setWidth w (BitVec.ofBool c)).getLsbD i.val) =
        fun x => (a x).getLsbD i.val ^^
          ((b x).getLsbD i.val ^^ BitVec.carry i.val (a x) (b x) c) :=
      funext fun x => BitVec.getLsbD_add_add_bool i.isLt (a x) (b x) c
    rw [heq]
    exact h.mono Set.Subset.rfl Set.Subset.rfl (by have := i.isLt; omega)

/-- Addition modulo the word width. -/
theorem synthesis_add :
    Synthesis interpretation s (wordWires fun x => a x + b x) (40 * (w + 1) ^ 2) := by
  simpa using synthesis_addCarry s a b ha hb false

omit ha hb in
/-- A hardwired word uses one constant gate per bit. -/
theorem synthesis_word_const (v : BitVec w) :
    Synthesis interpretation s (wordWires fun _ => v) w := by
  simpa [wordWires] using Synthesis.family (I := interpretation) (s := s)
    (fun i : Fin w => fun _ => v.getLsbD i.val) (fun _ => 1) fun _ => Synthesis.const _

omit ha in
/-- Bitwise complementation uses one gate per bit. -/
theorem synthesis_word_not : Synthesis interpretation s (wordWires fun x => ~~~b x) w := by
  have h := Synthesis.family (I := interpretation) (s := s)
    (fun i : Fin w => fun x => !(b x).getLsbD i.val) (fun _ => 1)
    fun i => (Synthesis.of_mem (hb i)).not
  simpa only [wordWires, BitVec.getLsbD_not, Fin.is_lt, decide_true, Bool.true_and,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, mul_one] using h

/-- Unsigned comparison by a complemented carry chain. -/
theorem synthesis_ult :
    Synthesis interpretation s {fun x => (a x).ult (b x)} (5 * w + 2) := by
  have hn := synthesis_word_not s b hb
  have hc := synthesis_carry (s ∪ wordWires fun x => ~~~b x)
    a (fun x => ~~~b x) (fun i => Or.inl (ha i)) (fun i => Or.inr ⟨i, rfl⟩) true w le_rfl
  have h := hn.trans hc.not
  simpa only [BitVec.ult_eq_not_carry, Nat.mul_succ, Nat.add_assoc,
    show w + (4 * w + 1 + 1) = 5 * w + 2 by omega] using h

/-- Subtraction modulo the word width. -/
theorem synthesis_sub :
    Synthesis interpretation s (wordWires fun x => a x - b x) (41 * (w + 1) ^ 2) := by
  have hn := synthesis_word_not s b hb
  have hc := synthesis_addCarry (s ∪ wordWires fun x => ~~~b x)
    a (fun x => ~~~b x) (fun i => Or.inl (ha i)) (fun i => Or.inr ⟨i, rfl⟩) true
  have h := hn.trans hc
  have heq (x : BitString n) :
      a x - b x = a x + ~~~b x + BitVec.setWidth w (BitVec.ofBool true) := by
    simp only [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, BitVec.add_assoc]
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth]
  simp only [← heq] at h
  exact h.mono Set.Subset.rfl Set.Subset.rfl (by nlinarith)

/-- Word equality uses six gates per bit and a constant. -/
theorem synthesis_word_eq :
    Synthesis interpretation s {fun x => decide (a x = b x)} (6 * w + 1) := by
  have h := Synthesis.forall_mem (s := s) Finset.univ
    (fun i : Fin w => fun x => decide ((a x).getLsbD i.val = (b x).getLsbD i.val))
    (fun _ => 5) fun i _ => Synthesis.beq (ha i) (hb i)
  have heq (x : BitString n) :
      (∀ i : Fin w, (a x).getLsbD i.val = (b x).getLsbD i.val) ↔ a x = b x :=
    ⟨fun h => BitVec.eq_of_getLsbD_eq fun i hi => h ⟨i, hi⟩, fun h => by simp only [h,
      implies_true]⟩
  simpa only [Finset.mem_univ, forall_true_left, decide_eq_true_eq, heq,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, Nat.mul_comm] using h

omit ha hb in
/-- A word multiplexer shares one available control bit across four gates per bit. -/
theorem synthesis_word_mux (flag : BooleanFunction n) (hf : flag ∈ s)
    (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s) :
    Synthesis interpretation s (wordWires fun x => if flag x then a x else b x) (4 * w) := by
  have h := Synthesis.family (I := interpretation) (s := s)
    (fun i : Fin w => fun x => if flag x then (a x).getLsbD i.val else (b x).getLsbD i.val)
    (fun _ => 4) fun i => Synthesis.mux hf (ha i) (hb i)
  have heq : (fun i : Fin w => fun x => (if flag x then a x else b x).getLsbD i.val) =
      fun i : Fin w => fun x => if flag x then (a x).getLsbD i.val else (b x).getLsbD i.val := by
    funext i x
    split <;> rfl
  rw [wordWires, heq]
  simpa [Nat.mul_comm] using h

end Arithmetic

/-! ### Table selection -/

/-- Testing a word against a constant needs one literal per bit and a conjunction. -/
theorem synthesis_word_eq_const (s : Set (BooleanFunction n)) (a : BitString n → BitVec k)
    (ha : ∀ i : Fin k, (fun x => (a x).getLsbD i.val) ∈ s) (v : BitVec k) :
    Synthesis interpretation s {fun x => decide (a x = v)} (2 * k + 1) := by
  have hlit (i : Fin k) : Synthesis interpretation s
      {fun x => decide ((a x).getLsbD i.val = v.getLsbD i.val)} 1 := by
    have h := Synthesis.of_mem (I := interpretation) (ha i)
    cases hv : v.getLsbD i.val
    · simpa only [hv, Bool.decide_eq_false] using h.not
    · simpa only [hv, Bool.decide_eq_true] using
        h.mono Set.Subset.rfl Set.Subset.rfl (by omega : 0 ≤ 1)
  have h := Synthesis.forall_mem (s := s) Finset.univ
    (fun i : Fin k => fun x => decide ((a x).getLsbD i.val = v.getLsbD i.val))
    (fun _ => 1) fun i _ => hlit i
  have heq (x : BitString n) : (∀ i : Fin k, (a x).getLsbD i.val = v.getLsbD i.val) ↔ a x = v :=
    ⟨fun h => BitVec.eq_of_getLsbD_eq fun i hi => h ⟨i, hi⟩,
      fun h i => congrArg (fun a => a.getLsbD i.val) h⟩
  simpa only [Finset.mem_univ, forall_true_left, decide_eq_true_eq, heq,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, Nat.mul_comm] using h

/-- Select a record by its binary index; an index matching no record selects all-false. -/
def selectBits (index : BitVec k) (values : Fin R → Fin w → Bool) : Fin w → Bool :=
  fun bit => decide (∃ j : Fin R, index = BitVec.ofNat k j.val ∧ values j bit = true)

/-- Indices below `2 ^ k` have distinct encodings. -/
theorem ofNat_index_injective (hR : R ≤ 2 ^ k) :
    Function.Injective fun j : Fin R => BitVec.ofNat k j.val := by
  intro i j hij
  apply Fin.ext
  have h := congrArg BitVec.toNat hij
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (i.isLt.trans_le hR),
    Nat.mod_eq_of_lt (j.isLt.trans_le hR)] using h

/-- An in-range index selects exactly its record. -/
theorem selectBits_eq (hR : R ≤ 2 ^ k) (values : Fin R → Fin w → Bool) (j : Fin R) :
    selectBits (BitVec.ofNat k j.val) values = values j := by
  funext bit
  apply Bool.eq_iff_iff.mpr
  simp [selectBits, (ofNat_index_injective hR).eq_iff]

theorem selectBits_toNat (index : BitVec k) (values : Fin R → Fin w → Bool)
    (hR : R ≤ 2 ^ k) (hi : index.toNat < R) :
    selectBits index values = values ⟨index.toNat, hi⟩ := by
  simpa using selectBits_eq hR values ⟨index.toNat, hi⟩

/-- Selecting among available records charges one comparison per record and output bit. -/
theorem synthesis_selectBits (s : Set (BooleanFunction n)) (index : BitString n → BitVec k)
    (values : Fin R → BitString n → Fin w → Bool)
    (hi : ∀ i : Fin k, (fun x => (index x).getLsbD i.val) ∈ s)
    (hv : ∀ j bit, (fun x => values j x bit) ∈ s) :
    Synthesis interpretation s
      (Set.range fun bit x => selectBits (index x) (fun j => values j x) bit)
      (w * (R * (2 * k + 3) + 1)) := by
  have hs := Synthesis.family (I := interpretation) (s := s)
    (fun bit x => selectBits (index x) (fun j => values j x) bit)
    (fun _ => R * (2 * k + 3) + 1) fun bit => ?_
  · simpa using hs
  · have h := Synthesis.exists_mem (s := s) Finset.univ
      (fun j : Fin R => fun x => decide (index x = BitVec.ofNat k j.val) && values j x bit)
      (fun _ => 2 * k + 2) fun j _ =>
        (synthesis_word_eq_const s index hi _).and (Synthesis.of_mem (hv j bit))
    simpa [selectBits, Nat.add_assoc] using h

end Boolean.Iteration

end Cslib.Circuits
