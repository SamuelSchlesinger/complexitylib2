/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Propagation
public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Bool.Basic
public import Mathlib.Order.PiLex
import Mathlib.Order.Fin.Tuple

/-!
# Broadcasting along sorted keys

Records are sorted lexicographically by key followed by a tag. False-tagged sources therefore
precede true-tagged destinations with the same key. Segmented propagation seeds each source's
value and carries it through equal-key links. Each destination receives the OR of every
matching source; no uniqueness assumption is needed for this characterization.

## Main results

* `Cslib.BitString.propagate_sorted_tagged_eq_true_iff`: the propagated value at a destination
  is true precisely when a matching source has a true value.

## References

* Adapts the sorted-broadcast argument in MassProduction/Nonuniform/BroadcastCorrectness.lean
  from [S. Schlesinger,
  *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.BitString

private theorem snoc_lt_of_lt {k : ℕ} {x y : BitString k} (a b : Bool)
    (h : toLex x < toLex y) :
    toLex (Fin.snoc (α := fun _ => Bool) x a) <
      toLex (Fin.snoc (α := fun _ => Bool) y b) := by
  obtain ⟨i, heq, hlt⟩ := h
  refine ⟨i.castSucc, ?_, ?_⟩
  · intro j hj
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last
      (ne_of_lt (hj.trans (Fin.castSucc_lt_last i)))
    simpa using heq j (by simpa using hj)
  · simpa using hlt

private theorem prefix_le_of_snoc_le {k : ℕ} {x y : BitString k} {a b : Bool}
    (h : toLex (Fin.snoc (α := fun _ => Bool) x a) ≤
      toLex (Fin.snoc (α := fun _ => Bool) y b)) : toLex x ≤ toLex y := by
  by_contra hn
  exact (not_lt_of_ge h) (snoc_lt_of_lt b a (lt_of_not_ge hn))

private theorem false_lt_true {k : ℕ} (key : BitString k) :
    toLex (Fin.snoc (α := fun _ => Bool) key false) <
      toLex (Fin.snoc (α := fun _ => Bool) key true) := by
  refine ⟨Fin.last k, ?_, ?_⟩
  · intro i hi
    obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (ne_of_lt hi)
    simp
  · simp

/-- At a destination in key/tag order, propagation is the OR of all matching source values.
False tags mark sources and true tags mark destinations. Sources and destinations may repeat,
and sortedness is required only within the indicated prefix. -/
theorem propagate_sorted_tagged_eq_true_iff {k n d : ℕ} (key : ℕ → BitString k)
    (tag payload : ℕ → Bool) (hd : d < n) (htag : tag d = true)
    (sorted : MonotoneOn (fun i => toLex (Fin.snoc (α := fun _ => Bool) (key i) (tag i)))
      (Set.Iio n)) :
    propagate (fun i => !tag i && payload i)
      (keyLinks (fun i => toLex (key i))) (d + 1) = true ↔
        ∃ s, s < n ∧ key s = key d ∧ tag s = false ∧ payload s = true := by
  have monoKey : MonotoneOn (fun i => toLex (key i)) (Set.Iio (d + 1)) := by
    intro a ha b hb hab
    apply prefix_le_of_snoc_le
    exact sorted (Nat.lt_of_le_of_lt (Nat.le_of_lt_succ ha) hd)
      (Nat.lt_of_le_of_lt (Nat.le_of_lt_succ hb) hd) hab
  rw [propagate_sorted_eq_true_iff (fun i => toLex (key i))
    (fun i => !tag i && payload i) (d + 1) monoKey]
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.add_sub_cancel_right, toLex_inj]
  constructor
  · rintro ⟨s, hs, ⟨htag, hpayload⟩, hkey⟩
    exact ⟨s, by lia, hkey, htag, hpayload⟩
  · rintro ⟨s, hs, hkey, hsource, hpayload⟩
    have hsd : s < d := by
      apply sorted.reflect_lt hs hd
      rw [hsource, htag, hkey]
      exact false_lt_true _
    exact ⟨s, by lia, ⟨hsource, hpayload⟩, hkey⟩

end Cslib.BitString
