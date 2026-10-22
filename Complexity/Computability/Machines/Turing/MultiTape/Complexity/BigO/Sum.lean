/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative

/-!
# Linear resource bounds for tagged sum constructors

Prepending the fixed Boolean tag bit to the payload encoding costs linear time and space in the
encoded input length, without any finite-domain or inhabitance assumption on either summand.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInO.inl`, `.inr`: linear-time and linear-space tagged sum
  injections.

## References

Uses Christian Reitwiessner's native tidy degree/resource calculus (`ComputableTidilyInO.append`).
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInO

variable {α β : Type}

/-- A left sum tag has a direct native linear implementation. -/
@[fun_prop]
theorem inl (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableTidilyInO (Sum.inl (α := α) (β := β)) left (encSum left right)
      (fun a => (left a).length) (fun a => (left a).length) := by
  have hid : ComputableTidilyInO (fun a : α => a) left left
      (fun a => (left a).length) (fun a => (left a).length) :=
    ComputableTidilyInDegree.id'.inO_one
  exact ((ComputableTidilyInO.const (encMid := encBool) false).append hid
    (fun _ => rfl)).mono 2 (fun _ => by omega) (fun _ => by omega)

/-- A right sum tag has a direct native linear implementation. -/
@[fun_prop]
theorem inr (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableTidilyInO (Sum.inr (α := α) (β := β)) right (encSum left right)
      (fun a => (right a).length) (fun a => (right a).length) := by
  have hid : ComputableTidilyInO (fun a : β => a) right right
      (fun a => (right a).length) (fun a => (right a).length) :=
    ComputableTidilyInDegree.id'.inO_one
  exact ((ComputableTidilyInO.const (encMid := encBool) true).append hid
    (fun _ => rfl)).mono 2 (fun _ => by omega) (fun _ => by omega)

end Turing.MultiTapeTM.ComputableTidilyInO
