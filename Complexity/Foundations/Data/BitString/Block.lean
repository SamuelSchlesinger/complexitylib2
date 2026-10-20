/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Blocks of bit strings

A string of `m * k` bits is read as `m` consecutive blocks of `k` bits through `finProdFinEquiv`:
bit `j` of block `i` is bit `finProdFinEquiv (i, j)` of the string (`BitString.block`). Cutting a
string into its blocks is an equivalence `BitString (m * k) ≃ (Fin m → BitString k)`
(`BitString.blocksEquiv`). The positions of the blocks (`BitString.blockBits`) are pairwise
disjoint, and gluing two strings along the positions of one block takes that block from the first
string and every other block from the second (`BitString.block_piecewise`).

## Main definitions

* `Cslib.BitString.block`: the `i`-th block of `k` bits of a string of `m * k` bits.
* `Cslib.BitString.blocksEquiv`: cutting a string into its blocks; its inverse reads bit `p` of
  the string in its block (`BitString.blocksEquiv_symm_apply`).
* `Cslib.BitString.blockBits`: the positions of the bits of a block.
* `Cslib.BitString.listBlock`: a block of a bit list (`BitString.listBlock_ofFn`).

## Main results

* `Cslib.BitString.pairwiseDisjoint_blockBits`: blocks occupy disjoint positions.
* `Cslib.BitString.block_piecewise`: gluing two strings along one block.
-/

@[expose] public section

namespace Cslib.BitString

open Finset

variable {m k : ℕ}

/-- The `i`-th block of `k` consecutive bits of a string of `m` blocks. -/
def block (x : BitString (m * k)) (i : Fin m) : BitString k :=
  fun j => x (finProdFinEquiv (i, j))

@[simp] theorem block_apply (x : BitString (m * k)) (i : Fin m) (j : Fin k) :
    block x i j = x (finProdFinEquiv (i, j)) :=
  rfl

/-- Cutting a string of `m * k` bits into its `m` blocks of `k` bits. -/
@[simps symm_apply]
def blocksEquiv : BitString (m * k) ≃ (Fin m → BitString k) where
  toFun := block
  invFun y p := y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
  left_inv x := funext fun p => by
    change x (finProdFinEquiv ((finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2)) = x p
    rw [Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv y := funext fun i => funext fun j => by
    change y (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = y i j
    rw [Equiv.symm_apply_apply]

@[simp] theorem blocksEquiv_apply (x : BitString (m * k)) : blocksEquiv x = block x :=
  rfl

/-- Cutting the concatenation of blocks into its blocks recovers them. -/
@[simp] theorem block_blocksEquiv_symm (z : Fin m → BitString k) :
    block (blocksEquiv.symm z) = z :=
  blocksEquiv.apply_symm_apply z

/-- The positions of the bits of the `i`-th block of `k` bits. -/
def blockBits (k : ℕ) (i : Fin m) : Finset (Fin (m * k)) :=
  univ.filter fun p => (finProdFinEquiv.symm p).1 = i

theorem mem_blockBits {i : Fin m} {p : Fin (m * k)} :
    p ∈ blockBits k i ↔ (finProdFinEquiv.symm p).1 = i := by
  simp [blockBits]

/-- Distinct blocks occupy disjoint positions. -/
theorem pairwiseDisjoint_blockBits (k : ℕ) :
    ((univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint (blockBits k) :=
  fun _ _ _ _ hij => disjoint_left.2 fun _ hi hj =>
    hij ((mem_filter.1 hi).2.symm.trans (mem_filter.1 hj).2)

/-- Gluing `x` and `z` along the positions of block `i` takes block `i` from `x` and the other
blocks from `z`. -/
theorem block_piecewise (i : Fin m) (x z : BitString (m * k)) (j : Fin m) :
    block ((blockBits k i).piecewise x z) j = if j = i then block x j else block z j := by
  funext b
  have hmem : finProdFinEquiv (j, b) ∈ blockBits k j := by simp [mem_blockBits]
  by_cases hj : j = i
  · subst hj
    simp only [block, ↓reduceIte, Finset.piecewise_eq_of_mem _ _ _ hmem]
  · have hmem' : finProdFinEquiv (j, b) ∉ blockBits k i := by simp [mem_blockBits, hj]
    simp only [block, hj, ↓reduceIte, Finset.piecewise_eq_of_notMem _ _ _ hmem']

/-- Block `i` of `k` bits of a bit list: the `k` bits from position `i * k` on. -/
def listBlock (k : ℕ) (z : List Bool) (i : ℕ) : List Bool := (z.drop (i * k)).take k

/-- Block `i` of the list of a bit string is the list of its block `i`. -/
theorem listBlock_ofFn (z : BitString (m * k)) (i : Fin m) :
    listBlock k (List.ofFn z) i = List.ofFn (block z i) := by
  have hi : (i + 1) * k ≤ m * k := Nat.mul_le_mul_right _ i.2
  refine List.ext_getElem (by
    simp only [listBlock, List.length_take, List.length_drop, List.length_ofFn]
    rw [Nat.add_mul] at hi
    omega) fun j h₁ h₂ => ?_
  simp only [listBlock, List.getElem_take, List.getElem_drop, List.getElem_ofFn, block_apply]
  congr 1
  ext
  simp only [finProdFinEquiv_apply_val]
  rw [Nat.mul_comm, Nat.add_comm]

end Cslib.BitString
