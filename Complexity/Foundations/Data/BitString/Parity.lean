/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Function.Const
public import Mathlib.Logic.Function.DependsOn
import Mathlib.Data.Fintype.BigOperators

/-!
# The parity function

`parityOn s x` says whether an odd number of the bits of `x` in `s` are true, and `parity n` is the
parity of all `n` bits. Fixing one bit of `s` leaves the parity of the others, possibly negated
(`parityOn_insert`), and flipping one of the bits negates the parity (`parityOn_update_not`), so
the parity of a nonempty set of bits is not constant and depends on each of them.

## Main definitions

* `Cslib.parityOn`: the parity of the bits in a set.
* `Cslib.parity`: the parity of all bits.

## Main results

* `Cslib.parityOn_union`, `Cslib.parityOn_biUnion`: the parity of a disjoint union.
* `Cslib.parityOn_xor`: parities are linear.
* `Cslib.parity_update_not`: flipping any bit flips the parity.
* `Cslib.card_filter_parity_eq_true`: parity of `n ≥ 1` bits is true on `2 ^ (n - 1)` inputs.
-/

@[expose] public section

namespace Cslib

open Finset Function

variable {n : ℕ}

/-- The parity of the bits of `x` in `s`: whether an odd number of them are true. -/
def parityOn (s : Finset (Fin n)) (x : BitString n) : Bool :=
  decide (#{i ∈ s | x i = true} % 2 = 1)

/-- The parity function on `n` bits. -/
def parity (n : ℕ) : BooleanFunction n :=
  parityOn univ

variable {s t : Finset (Fin n)} {i : Fin n}

@[simp] theorem parityOn_empty (x : BitString n) : parityOn ∅ x = false := by
  simp [parityOn]

/-- The parity on `s` only reads the bits in `s`. -/
theorem parityOn_congr {x y : BitString n} (h : ∀ j ∈ s, x j = y j) :
    parityOn s x = parityOn s y := by
  unfold parityOn
  rw [filter_congr fun j hj => by rw [h j hj]]

theorem parityOn_insert (hi : i ∉ s) (x : BitString n) :
    parityOn (insert i s) x = (x i ^^ parityOn s x) := by
  unfold parityOn
  rw [filter_insert]
  cases hx : x i
  · simp
  · simp only [ite_true, card_insert_of_notMem fun h => hi (mem_filter.1 h).1, Bool.true_xor]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
    omega

theorem parityOn_eq_xor_erase (hi : i ∈ s) (x : BitString n) :
    parityOn s x = (x i ^^ parityOn (s.erase i) x) := by
  conv_lhs => rw [← insert_erase hi]
  exact parityOn_insert (notMem_erase i s) x

theorem parityOn_update_of_notMem (hi : i ∉ s) (x : BitString n) (b : Bool) :
    parityOn s (update x i b) = parityOn s x :=
  parityOn_congr fun _ hj => update_of_ne (ne_of_mem_of_not_mem hj hi) _ _

/-- The parity of a disjoint union is the exclusive or of the parities. -/
theorem parityOn_union (h : Disjoint s t) (x : BitString n) :
    parityOn (s ∪ t) x = (parityOn s x ^^ parityOn t x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hit : i ∉ t := disjoint_left.1 h (mem_insert_self i s)
    rw [insert_union, parityOn_insert (by simp [hi, hit]), parityOn_insert hi,
      ih (disjoint_of_subset_left (subset_insert i s) h), Bool.xor_assoc]

/-- The parity of a union of pairwise disjoint blocks is the parity of the parities of the
blocks. -/
theorem parityOn_biUnion {m : ℕ} {S : Finset (Fin m)} {B : Fin m → Finset (Fin n)}
    (hB : (S : Set (Fin m)).PairwiseDisjoint B) (x : BitString n) :
    parityOn (S.biUnion B) x = parityOn S fun j => parityOn (B j) x := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    have hdisj : Disjoint (B j) (S.biUnion B) := (disjoint_biUnion_right _ _ _).2 fun j' hj' =>
      hB (mem_insert_self j S) (mem_insert_of_mem hj') fun h => hj (h ▸ hj')
    rw [biUnion_insert, parityOn_union hdisj, parityOn_insert hj,
      ih (hB.subset (by simp [Set.subset_insert]))]

/-- **Parities are linear**: the parity of a sum of bit strings is the exclusive or of the
parities. -/
theorem parityOn_xor (S : Finset (Fin n)) (x y : BitString n) :
    parityOn S (fun i => x i ^^ y i) = (parityOn S x ^^ parityOn S y) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [parityOn_insert hi, parityOn_insert hi, parityOn_insert hi, ih]
    simp only [Bool.xor_assoc, Bool.xor_left_comm (y i)]

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
