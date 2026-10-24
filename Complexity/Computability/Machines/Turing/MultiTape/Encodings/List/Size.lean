/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List

/-! # Size bounds for readable list encodings

The pure interface and instances are moved unchanged from the quantitative fold provider.
-/

namespace Turing.MultiTapeTM

/-- A list encoding whose encoded lists are at least as long as their elements, their suffixes and
their lengths. -/
public class SizedListEncoding {α : Type*} (encA : α ↪ List Bool) (encL : List α ↪ List Bool) :
    Prop where
  length_le (l : List α) : l.length ≤ (encL l).length
  length_elem_le (l : List α) : ∀ a ∈ l, (encA a).length ≤ (encL l).length
  length_drop_le (l : List α) (i : ℕ) : (encL (l.drop i)).length ≤ (encL l).length

public instance {α : Type*} (enc : α ↪ List Bool) : SizedListEncoding enc (encList enc) where
  length_le l := by induction l <;> grind [encList_cons, length_frame]
  length_elem_le l a ha := by induction l <;> grind [encList_cons, length_frame]
  length_drop_le l i := ((List.drop_sublist i l).flatMap (frame ∘ enc)).length_le

public instance : SizedListEncoding encBool encBits where
  length_le l := by simp
  length_elem_le l a ha := by
    simp only [encBool_apply, List.length_singleton, encBits_apply]
    exact List.length_pos_of_mem ha
  length_drop_le l i := by simp

end Turing.MultiTapeTM
