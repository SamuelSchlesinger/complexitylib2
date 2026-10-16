/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Foundations.Data.StackTape

/-!
# Indexed observations of finite stack tapes

These additions give Bolton Bailey's upstream `StackTape` an indexed view that reads blank
outside its stored list. The existing representation and operations are unchanged.

## Main definitions

* `Cslib.Turing.StackTape.read`: observe the tape at a natural-number displacement.

## Main results

* `Cslib.Turing.StackTape.read_eq_getElem?`: agreement with padded list lookup.
* `Cslib.Turing.StackTape.read_mapSome`: loading a word preserves its indexed symbols.

## References

Ports the additions to `Foundations/Data/StackTape.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, retaining the upstream tape representation.
-/

@[expose] public section

namespace Cslib.Turing.StackTape

variable {Symbol : Type*}

/-- Equality of stored lists determines equality of stack tapes. -/
@[ext] theorem ext {left right : StackTape Symbol} (h : left.toList = right.toList) :
    left = right := by
  cases left
  cases right
  cases h
  rfl

@[simp] lemma tail_toList (tape : StackTape Symbol) : tape.tail.toList = tape.toList.tail := by
  cases tape with | mk values h => cases values <;> rfl

/-- Read a cell, treating every position beyond the finite representation as blank. -/
def read : StackTape Symbol → ℕ → Option Symbol
  | tape, 0 => tape.head
  | tape, position + 1 => tape.tail.read position

@[simp] lemma read_zero (tape : StackTape Symbol) : tape.read 0 = tape.head := rfl

@[simp] lemma read_succ (tape : StackTape Symbol) (position : ℕ) :
    tape.read (position + 1) = tape.tail.read position := rfl

@[simp] lemma read_nil (position : ℕ) : (nil : StackTape Symbol).read position = none := by
  induction position <;> simp_all [read, head, tail, nil]

/-- The indexed view agrees with the stored list, with absent cells read as blanks. -/
lemma read_eq_getElem? (tape : StackTape Symbol) (position : ℕ) :
    tape.read position = tape.toList[position]?.join := by
  induction position generalizing tape with
  | zero => cases tape with | mk values h => cases values <;> rfl
  | succ position ih =>
    rw [read_succ, ih]
    cases tape with | mk values h => cases values <;> simp [tail, nil]

@[simp] lemma read_mapSome (values : List Symbol) (position : ℕ) :
    (mapSome values).read position = values[position]? := by
  simp only [read_eq_getElem?, mapSome, List.getElem?_map]
  cases values[position]? <;> rfl

end Cslib.Turing.StackTape
