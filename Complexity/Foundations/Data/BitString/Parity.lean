/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Function.Const
public import Mathlib.Logic.Function.DependsOn
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# The parity function

`parityOn s x` says whether an odd number of the bits of `x` in `s` are true, and `parity n` is the
parity of all `n` bits.

Bits form the two-element Boolean ring (Mathlib's `BooleanRing Bool`), in which `a + b = (a ^^ b)`
and `a * b = (a && b)`, so bit strings form an additive group under coordinatewise exclusive or:
`(x + y) i = (x i ^^ y i)`. Throughout, bit strings are added with `+`, while single bits, such as
the values of Boolean functions, are combined with `^^`. In this ring the parity on `s` is the sum
of the bits in `s` (`parityOn_eq_sum`), so it splits over disjoint unions (`parityOn_union`) and is
additive (`parityOn_add`). Flipping one of the bits negates the parity (`parityOn_update_not`), so
the parity of a nonempty set of bits is not constant and depends on each of them.

## Main definitions

* `Cslib.parityOn`: the parity of the bits in a set.
* `Cslib.parity`: the parity of all bits.

## Main results

* `Cslib.BitString.add_self`: every bit string is its own negative.
* `Cslib.parityOn_eq_sum`: the parity is the sum of the bits in the Boolean ring.
* `Cslib.parityOn_union`, `Cslib.parityOn_biUnion`: the parity of a disjoint union.
* `Cslib.parityOn_add`: parities are linear.
* `Cslib.parity_update_not`: flipping any bit flips the parity.
* `Cslib.card_filter_parity_eq_true`: parity of `n ≥ 1` bits is true on `2 ^ (n - 1)` inputs.
-/

@[expose] public section

namespace Cslib

open Finset Function

variable {n : ℕ}

namespace BitString

/-- A bit string added to itself gives zero. -/
@[simp] protected theorem add_self (x : BitString n) : x + x = 0 :=
  funext fun i => Bool.xor_self (x i)

@[simp] protected theorem add_cancel_left (x y : BitString n) : x + (x + y) = y := by
  rw [← add_assoc, BitString.add_self, zero_add]

@[simp] protected theorem add_cancel_right (x y : BitString n) : x + y + y = x := by
  rw [add_assoc, BitString.add_self, add_zero]

end BitString

/-- The parity of the bits of `x` in `s`: whether an odd number of them are true. -/
def parityOn (s : Finset (Fin n)) (x : BitString n) : Bool :=
  decide (#{i ∈ s | x i = true} % 2 = 1)

/-- The parity function on `n` bits. -/
def parity (n : ℕ) : BooleanFunction n :=
  parityOn univ

variable {s t : Finset (Fin n)} {i : Fin n}

/-- A natural number, read in the Boolean ring, is its parity. -/
private theorem natCast_bool (k : ℕ) : (k : Bool) = decide (k % 2 = 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.cast_succ, ih, Bool.add_eq_xor]
    rcases Nat.mod_two_eq_zero_or_one k with h | h <;>
      simp [h, Nat.succ_mod_two_eq_one_iff, Bool.one_eq_true]

/-- **The parity is the sum of the bits** in the Boolean ring `Bool`. -/
theorem parityOn_eq_sum (s : Finset (Fin n)) (x : BitString n) : parityOn s x = ∑ i ∈ s, x i := by
  have h (b : Bool) : b = if b = true then 1 else 0 := by cases b <;> rfl
  rw [sum_congr rfl fun i _ => h (x i), sum_boole, natCast_bool]
  rfl

@[simp] theorem parityOn_empty (x : BitString n) : parityOn ∅ x = false := by
  rw [parityOn_eq_sum, sum_empty]
  rfl

/-- The parity on `s` only reads the bits in `s`. -/
theorem parityOn_congr {x y : BitString n} (h : ∀ j ∈ s, x j = y j) :
    parityOn s x = parityOn s y := by
  simp only [parityOn_eq_sum]
  exact sum_congr rfl h

theorem parityOn_insert (hi : i ∉ s) (x : BitString n) :
    parityOn (insert i s) x = (x i ^^ parityOn s x) := by
  simp only [parityOn_eq_sum]
  exact sum_insert hi

theorem parityOn_eq_xor_erase (hi : i ∈ s) (x : BitString n) :
    parityOn s x = (x i ^^ parityOn (s.erase i) x) := by
  simp only [parityOn_eq_sum]
  exact (add_sum_erase s x hi).symm

theorem parityOn_update_of_notMem (hi : i ∉ s) (x : BitString n) (b : Bool) :
    parityOn s (update x i b) = parityOn s x :=
  parityOn_congr fun _ hj => update_of_ne (ne_of_mem_of_not_mem hj hi) _ _

/-- The parity of a disjoint union is the exclusive or of the parities. -/
theorem parityOn_union (h : Disjoint s t) (x : BitString n) :
    parityOn (s ∪ t) x = (parityOn s x ^^ parityOn t x) := by
  simp only [parityOn_eq_sum]
  exact sum_union h

/-- The parity of a union of pairwise disjoint blocks is the parity of the parities of the
blocks. -/
theorem parityOn_biUnion {m : ℕ} {S : Finset (Fin m)} {B : Fin m → Finset (Fin n)}
    (hB : (S : Set (Fin m)).PairwiseDisjoint B) (x : BitString n) :
    parityOn (S.biUnion B) x = parityOn S fun j => parityOn (B j) x := by
  simp only [parityOn_eq_sum]
  exact sum_biUnion hB

/-- **Parities are linear**: the parity of a sum of bit strings is the exclusive or of the
parities. -/
theorem parityOn_add (S : Finset (Fin n)) (x y : BitString n) :
    parityOn S (x + y) = (parityOn S x ^^ parityOn S y) := by
  simp only [parityOn_eq_sum]
  exact sum_add_distrib

/-- Flipping one of the bits negates the parity. -/
theorem parityOn_update_not (hi : i ∈ s) (x : BitString n) :
    parityOn s (update x i !x i) = !parityOn s x := by
  rw [parityOn_eq_xor_erase hi, parityOn_eq_xor_erase hi, update_self,
    parityOn_update_of_notMem (notMem_erase i s)]
  cases x i <;> simp

/-- Flipping any bit flips the parity. -/
theorem parity_update_not (x : BitString n) (i : Fin n) :
    parity n (update x i !x i) = !parity n x :=
  parityOn_update_not (mem_univ i) x

/-- Parity of `n ≥ 1` bits is true on as many inputs as it is false: flipping the first bit
exchanges them. -/
theorem card_filter_parity_eq_true_eq (hn : 1 ≤ n) :
    #{x : BitString n | parity n x = true} = #{x : BitString n | parity n x = false} := by
  refine card_nbij' (fun x => update x ⟨0, hn⟩ !x ⟨0, hn⟩) (fun x => update x ⟨0, hn⟩ !x ⟨0, hn⟩)
    (fun x hx => ?_) (fun x hx => ?_) (fun x _ => by simp) (fun x _ => by simp)
  · simpa [parity_update_not] using hx
  · simpa [parity_update_not] using hx

/-- Parity of `n ≥ 1` bits is true on half of the inputs. -/
theorem card_filter_parity_eq_true (hn : 1 ≤ n) :
    #{x : BitString n | parity n x = true} = 2 ^ (n - 1) := by
  have htotal := card_filter_add_card_filter_not (s := (univ : Finset (BitString n)))
    (fun x => parity n x = true)
  simp only [Bool.not_eq_true, card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, ← card_filter_parity_eq_true_eq hn] at htotal
  have : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  omega

/-- Parity of `n ≥ 1` bits is false on half of the inputs. -/
theorem card_filter_parity_eq_false (hn : 1 ≤ n) :
    #{x : BitString n | parity n x = false} = 2 ^ (n - 1) := by
  rw [← card_filter_parity_eq_true_eq hn, card_filter_parity_eq_true hn]

/-- The parity, possibly negated, depends on each of its bits. -/
theorem not_dependsOn_parityOn (hi : i ∈ s) (c : Bool) :
    ¬DependsOn (fun x => c ^^ parityOn s x) {i}ᶜ := fun h => by
  have h' := h (x := update (fun _ => false) i true) (y := fun _ => false) fun j hj =>
    update_of_ne (by simpa using hj) _ _
  have := parityOn_update_not hi (fun _ => false)
  simp only [Bool.not_false] at this
  simp only [this] at h'
  cases parityOn s fun _ => false <;> cases c <;> simp at h'

/-- The parity of a nonempty set of bits, possibly negated, is not constant. -/
theorem not_isConst_parityOn (hs : s.Nonempty) (c : Bool) :
    ¬IsConst fun x => c ^^ parityOn s x := fun h => by
  obtain ⟨i, hi⟩ := hs
  exact not_dependsOn_parityOn hi c fun x y _ => h x y

end Cslib
