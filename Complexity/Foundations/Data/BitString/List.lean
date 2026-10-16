/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Block
public import Mathlib.Data.List.OfFn

/-!
# Bit strings represented by lists

Fixed-width views of ordinary lists pad missing bits with `false`. A flat list can also be read
as a specified number of fixed-width rows. The representation uses the existing `blocksEquiv`;
row extraction is ordinary dropping, padding and taking, including on short or empty lists.

## Main definitions

* `Cslib.BitString.ofList`: a fixed-width view of a list.
* `Cslib.BitString.listRow`, `Cslib.BitString.listRows`: fixed-width rows of a flat list.

## Main results

* `Cslib.BitString.ofList_ofFn`, `Cslib.BitString.ofFn_ofList`: representation round trips.
* `Cslib.BitString.listRows_eq_ofFn`: agreement with the finite block representation.
* `Cslib.BitString.ofFn_blocksEquiv_symm`: packing fixed-width rows is list concatenation.

## References

Adapted from `Probability/WordBits.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, reusing the shared bit-string block equivalence.
-/

@[expose] public section

namespace Cslib.BitString

/-- View a list as `n` bits, padding missing bits with `false`. -/
def ofList (n : ℕ) (word : List Bool) : BitString n := fun i => word.getD i.val false

@[simp] theorem ofList_ofFn {n : ℕ} (bits : BitString n) :
    ofList n (List.ofFn bits) = bits := by
  funext i
  simp [ofList]

/-- A list of the declared width loses no data through the finite representation. -/
theorem ofFn_ofList {n : ℕ} {word : List Bool} (hlen : word.length = n) :
    List.ofFn (ofList n word) = word := by
  subst n
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp [ofList, List.getD, List.getElem?_eq_getElem hi']

/-- Packing fixed-width rows in the block representation is ordinary list concatenation. -/
theorem ofFn_blocksEquiv_symm {count width : ℕ} (rows : Fin count → BitString width) :
    List.ofFn (blocksEquiv.symm rows) =
      (List.ofFn (fun i => List.ofFn (rows i))).flatten := by
  have h := congrArg (fun values => (List.ofFn fun i => List.ofFn (values i)).flatten)
    (blocksEquiv.apply_symm_apply rows)
  change (List.ofFn fun i => List.ofFn fun j =>
    blocksEquiv.symm rows (finProdFinEquiv (i, j))).flatten = _ at h
  simpa only [List.ofFn_mul, finProdFinEquiv, Equiv.coe_fn_mk,
    Nat.mul_comm, Nat.add_comm] using h

/-- Read one fixed-width row, using `false` beyond the end of the supplied list. -/
def listRow (width row : ℕ) (word : List Bool) : List Bool :=
  (word.drop (row * width) ++ List.replicate width false).take width

@[simp] theorem length_listRow (width row : ℕ) (word : List Bool) :
    (listRow width row word).length = width := by
  simp [listRow]

/-- List slicing agrees with the finite block representation, even on short input lists. -/
theorem listRow_eq_ofFn {count : ℕ} (width : ℕ) (row : Fin count) (word : List Bool) :
    listRow width row.val word = List.ofFn (block (ofList (count * width) word) row) := by
  apply List.ext_getElem (by simp)
  intro column hleft hright
  simp only [length_listRow] at hleft
  by_cases h : column + width * row.val < word.length <;>
    simp [listRow, ofList, block, List.getElem_take, List.getElem_append,
      List.getElem_drop, List.getD, Nat.lt_sub_iff_add_lt,
      Nat.add_comm, Nat.mul_comm, h]

/-- Read a specified number of rows, retaining empty rows when the width is zero. -/
def listRows (count width : ℕ) (word : List Bool) : List (List Bool) :=
  (List.range count).map (fun row => listRow width row word)

@[simp] theorem length_listRows (count width : ℕ) (word : List Bool) :
    (listRows count width word).length = count := by
  simp [listRows]

/-- Every extracted row has the declared width. -/
theorem length_of_mem_listRows {count width : ℕ} {word row : List Bool}
    (hrow : row ∈ listRows count width word) : row.length = width := by
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp hrow
  simp

/-- Extracting rows gives the list representation of the existing finite block view. -/
theorem listRows_eq_ofFn (count width : ℕ) (word : List Bool) :
    listRows count width word =
      List.ofFn (fun row => List.ofFn (block (ofList (count * width) word) row)) := by
  apply List.ext_getElem (by simp)
  intro row hleft hright
  simpa only [listRows, List.getElem_map, List.getElem_range, List.getElem_ofFn] using
    listRow_eq_ofFn width ⟨row, by simpa using hright⟩ word

end Cslib.BitString
