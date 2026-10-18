/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.List.ProdSigma
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Enumerating list occurrences

`List.Enumeration xs f` identifies the positions of `xs` with an index type, with `f` giving
the value at each index. Values need not be distinct: mapping a list retains every occurrence.

## Main definitions

* `List.Enumeration`: an equivalence of positions together with its lookup law.
* `List.Enumeration.map`, `List.Enumeration.prod`, `List.Enumeration.append`: compositional
  ordered enumerations.
* `List.Enumeration.reindex`: rename indices without changing the list.

## Main results

* `List.Enumeration.get_eq`: lookup at a position equals evaluation at its corresponding index.
-/

@[expose] public section

namespace List

variable {α β ι κ : Type*}

/-- The positions in a list product, with the right coordinate varying fastest. -/
def productIndexEquiv (left : List α) (right : List β) :
    Fin (left ×ˢ right).length ≃ Fin left.length × Fin right.length :=
  (finCongr (length_product left right)).trans finProdFinEquiv.symm

private theorem get_productIndexEquiv_symm (left : List α) (right : List β)
    (i : Fin left.length) (j : Fin right.length) :
    (left ×ˢ right).get ((productIndexEquiv left right).symm (i, j)) =
      (left.get i, right.get j) := by
  induction left with
  | nil => exact Fin.elim0 i
  | cons a left ih =>
    have bound (i : Fin (a :: left).length) :
        j.val + right.length * i.val < ((a :: left) ×ˢ right).length := by
      rw [length_product]
      exact (finProdFinEquiv (i, j)).isLt
    refine Fin.cases ?_ (fun i => ?_) i
    · change ((a :: left) ×ˢ right)[j.val]'(by simpa using bound 0) = (a, right[j.val])
      have hj : j.val < (right.map fun b => (a, b)).length := by
        simpa only [length_map] using j.isLt
      simp only [product_cons, getElem_append_left hj, getElem_map]
    · change ((a :: left) ×ˢ right)[j.val + right.length * (i.val + 1)]'(bound i.succ) =
        (left[i.val], right[j.val])
      have hbound : j.val + right.length * i.val < (left ×ˢ right).length := by
        rw [length_product]
        exact (finProdFinEquiv (i, j)).isLt
      have h := ih i
      change (left ×ˢ right)[j.val + right.length * i.val]'hbound = _ at h
      have hoff : (right.map (fun b => (a, b))).length ≤
          j.val + right.length * (i.val + 1) := by
        simp only [length_map, Nat.mul_add, Nat.mul_one]
        omega
      simp only [product_cons]
      rw [getElem_append_right hoff]
      simpa only [length_map, Nat.mul_add, Nat.mul_one, ← Nat.add_assoc,
        Nat.add_sub_cancel, get_eq_getElem] using h

/-- An ordered enumeration of occurrences, allowing different indices to have the same value. -/
structure Enumeration (xs : List α) (f : ι → α) where
  /-- The index assigned to each list position. -/
  equiv : Fin xs.length ≃ ι
  /-- The value at a position is given by its assigned index. -/
  get_eq (i : Fin xs.length) : xs.get i = f (equiv i)

namespace Enumeration

/-- A complete duplicate-free list enumerates the type of its values. -/
def ofNodup [DecidableEq α] (xs : List α) (hxs : xs.Nodup) (hmem : ∀ x, x ∈ xs) :
    Enumeration xs id :=
  ⟨hxs.getEquivOfForallMemList xs hmem, fun _ => rfl⟩

/-- The numerical range enumerates its bounded indices in order. -/
def range (n : ℕ) : Enumeration (List.range n) (Fin.val (n := n)) where
  equiv := finCongr length_range
  get_eq _ := by simp [get_eq_getElem]

/-- A singleton has one occurrence, indexed by `Unit`. -/
def singleton (a : α) : Enumeration [a] (fun _ : Unit => a) where
  equiv := finOneEquiv
  get_eq i := by simp [get_eq_getElem]

/-- Rename the occurrence indices without changing the list. -/
def reindex {xs : List α} {f : ι → α} (e : Enumeration xs f) (number : ι ≃ κ) :
    Enumeration xs (f ∘ number.symm) where
  equiv := e.equiv.trans number
  get_eq i := by simpa using e.get_eq i

/-- Mapping changes values but retains each occurrence and its index. -/
def map {xs : List α} {f : ι → α} (e : Enumeration xs f) (g : α → β) :
    Enumeration (xs.map g) (g ∘ f) where
  equiv := (finCongr (length_map (f := g))).trans e.equiv
  get_eq i := by
    simpa only [get_eq_getElem, getElem_map, Function.comp_apply, Equiv.trans_apply,
      finCongr_apply, Fin.val_cast] using
      congrArg g (e.get_eq (finCongr (length_map (f := g)) i))

/-- Products enumerate the right list for each successive occurrence of the left list. -/
def prod {xs : List α} {ys : List β} {f : ι → α} {g : κ → β}
    (left : Enumeration xs f) (right : Enumeration ys g) :
    Enumeration (xs ×ˢ ys) (fun p : ι × κ => (f p.1, g p.2)) where
  equiv := (productIndexEquiv xs ys).trans (Equiv.prodCongr left.equiv right.equiv)
  get_eq i := by
    obtain ⟨⟨a, b⟩, rfl⟩ := (productIndexEquiv xs ys).symm.surjective i
    simp only [get_productIndexEquiv_symm, Equiv.trans_apply, Equiv.apply_symm_apply,
      Equiv.prodCongr_apply, Prod.map_apply, left.get_eq, right.get_eq]

/-- Appending keeps every left occurrence before every right occurrence. -/
def append {xs ys : List α} {f : ι → α} {g : κ → α}
    (left : Enumeration xs f) (right : Enumeration ys g) :
    Enumeration (xs ++ ys) (Sum.elim f g) where
  equiv := ((finCongr length_append).trans finSumFinEquiv.symm).trans
    (Equiv.sumCongr left.equiv right.equiv)
  get_eq i := by
    obtain ⟨j, rfl⟩ := ((finCongr
      (show (xs ++ ys).length = xs.length + ys.length from length_append)).trans
        finSumFinEquiv.symm).symm.surjective i
    cases j with
    | inl j => simpa [get_eq_getElem, finSumFinEquiv] using left.get_eq j
    | inr j => simpa [get_eq_getElem, finSumFinEquiv] using right.get_eq j

end Enumeration

end List
