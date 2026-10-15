/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (after crei/tidy-universal lands)

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List

/-!
# Lengths of encoded lists

The framed encoding of a list (`Turing.MultiTapeTM.encList`) spends `2 * |enc a| + 1` symbols on
each element `a`. In particular a list is no longer than its encoding, and neither is the sum of
the lengths of its encoded elements. Such bounds are what a reduction needs to bound the size of
its output, or a verifier the length of a certificate, in terms of the input.

## Main results

* `Turing.MultiTapeTM.length_encList`: the exact length.
* `Turing.MultiTapeTM.length_le_length_encList`,
  `Turing.MultiTapeTM.sum_length_le_length_encList`: the two bounds.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α : Type*} (enc : α ↪ List Bool)

theorem length_encList (l : List α) :
    (encList enc l).length = (l.map fun a => 2 * (enc a).length + 1).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- A list is no longer than its encoding. -/
theorem length_le_length_encList (l : List α) : l.length ≤ (encList enc l).length := by
  rw [length_encList]
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

/-- The encoded elements of a list are no longer, in total, than the encoded list. -/
theorem sum_length_le_length_encList (l : List α) :
    (l.map fun a => (enc a).length).sum ≤ (encList enc l).length := by
  rw [length_encList]
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; omega

end Turing.MultiTapeTM
