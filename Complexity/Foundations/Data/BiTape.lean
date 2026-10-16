/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Foundations.Data.BiTape
public import Complexity.Foundations.Data.StackTape
public import Mathlib.Basic.Sign.Defs
public import Mathlib.Algebra.Ring.Int.Defs

/-!
# Indexed observations and native actions on bidirectional tapes

Bolton Bailey's upstream `BiTape` stores finite data relative to the current head. Its integer
view includes blank gaps and negative displacements. The representation relation allows a native
integer-indexed tape to have any absolute head position.

## Main definitions

* `Cslib.Turing.BiTape.read`: observe the tape at an integer displacement.
* `Cslib.Turing.BiTape.step`: an optional write followed by a signed move.
* `Cslib.Turing.BiTape.Represents`: agreement with a native tape and its head position.

## Main results

* `Cslib.Turing.BiTape.Represents.step`: native actions preserve the represented tape.
* `Cslib.Turing.BiTape.spaceUsed_step_le`: each action adds at most one stored cell.

## References

Ports the additions to `Foundations/Data/BiTape.lean` and the tape action laws from
`Computability/Machines/Turing/MultiTape/FiniteTape.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Turing.BiTape

variable {Symbol : Type*}

/-- A tape is determined by its current symbol and two stored sides. -/
@[ext] theorem ext {left right : BiTape Symbol} (head : left.head = right.head)
    (before : left.left = right.left) (after : left.right = right.right) : left = right := by
  cases left
  cases right
  cases head
  cases before
  cases after
  rfl

/-- Read a cell at an integer displacement from the current head. Negative positions lie to
the left; cells outside the finite stored contents are blank. -/
def read (tape : BiTape Symbol) : ℤ → Option Symbol
  | .ofNat 0 => tape.head
  | .ofNat (position + 1) => tape.right.read position
  | .negSucc position => tape.left.read position

@[simp] lemma read_zero (tape : BiTape Symbol) : tape.read 0 = tape.head := rfl

@[simp] lemma read_nil (position : ℤ) : (nil : BiTape Symbol).read position = none := by
  cases position with
  | ofNat position => cases position <;> simp [read, nil]
  | negSucc position => simp [read, nil]

/-- Loading a word puts its first symbol under the head and leaves all negative cells blank. -/
lemma read_mk₁ (values : List Symbol) (position : ℤ) :
    (mk₁ values).read position = if 0 ≤ position then values[position.toNat]? else none := by
  cases values with
  | nil => simp [mk₁]
  | cons value values =>
    cases position with
    | ofNat position =>
      cases position <;> simp [read, mk₁, add_nonneg]
    | negSucc position => simp [read, mk₁]

/-- Moving the head right shifts the relative reading coordinates by one cell. -/
lemma read_moveRight (tape : BiTape Symbol) (position : ℤ) :
    tape.moveRight.read position = tape.read (position + 1) := by
  cases position with
  | ofNat position => cases position <;> rfl
  | negSucc position =>
    cases position with
    | zero => simp [read, moveRight]
    | succ position =>
      have h : Int.negSucc (position + 1) + 1 = Int.negSucc position := by lia
      simp [read, moveRight, h]

/-- Moving the head left shifts the relative reading coordinates by one cell. -/
lemma read_moveLeft (tape : BiTape Symbol) (position : ℤ) :
    tape.moveLeft.read position = tape.read (position - 1) := by
  have h := read_moveRight tape.moveLeft (position - 1)
  simpa using h.symm

/-- A write changes exactly the current cell in the integer-indexed view. -/
lemma read_write (tape : BiTape Symbol) (symbol : Option Symbol) (position : ℤ) :
    (tape.write symbol).read position = if position = 0 then symbol else tape.read position := by
  cases position with
  | ofNat position =>
    cases position <;> simp [read, write, add_eq_zero_iff_eq_neg]
  | negSucc position => simp [read, write]

/-- Apply the work-tape component of a native multi-tape action. -/
def step (tape : BiTape Symbol) (action : Option (Option Symbol) × SignType) : BiTape Symbol :=
  let written := action.1.elim tape tape.write
  match action.2 with
  | .neg => written.moveLeft
  | .zero => written
  | .pos => written.moveRight

/-- The finite representation agrees with the native tape at every displacement from its head. -/
def Represents (tape : BiTape Symbol) (contents : ℤ → Option Symbol) (head : ℤ) : Prop :=
  ∀ position, tape.read position = contents (head + position)

/-- Blank finite storage represents the native initial work tape. -/
theorem represents_nil (head : ℤ) : (nil : BiTape Symbol).Represents (fun _ => none) head := by
  intro position
  simp

/-- Related tapes present the same symbol to the machine's transition table. -/
theorem Represents.head {tape : BiTape Symbol} {contents : ℤ → Option Symbol} {head : ℤ}
    (h : tape.Represents contents head) : tape.head = contents head := by
  simpa using h 0

/-- Finite tape updates realize precisely the native write and movement, with no restriction
on the head position or on blank gaps within the stored contents. -/
theorem Represents.step {tape : BiTape Symbol} {contents : ℤ → Option Symbol} {head : ℤ}
    (h : tape.Represents contents head) (action : Option (Option Symbol) × SignType) :
    (tape.step action).Represents
      (action.1.elim contents (fun symbol => Function.update contents head symbol))
      (head + action.2) := by
  unfold Represents at h
  intro position
  rcases action with ⟨write, move⟩
  cases write with
  | none =>
    cases move <;> simp [BiTape.step, read_moveLeft, read_moveRight, h,
      sub_eq_add_neg, add_left_comm, add_comm]
  | some symbol =>
    cases move <;>
      simp only [BiTape.step, Option.elim_some, read_moveLeft, read_moveRight, read_write,
        SignType.cast]
    all_goals
      simp only [Function.update_apply]
      split_ifs <;> first | rfl | lia | (rw [h]; congr 1; lia)

/-- A work-tape action increases the finite representation by at most one cell. -/
theorem spaceUsed_step_le (tape : BiTape Symbol) (action : Option (Option Symbol) × SignType) :
    (tape.step action).spaceUsed ≤ tape.spaceUsed + 1 := by
  rcases action with ⟨write, move⟩
  cases write <;> cases move <;>
    simp only [step, Option.elim_none, Option.elim_some]
  all_goals first
    | exact spaceUsed_move _ .left
    | exact spaceUsed_move _ .right
    | simp

end Cslib.Turing.BiTape
