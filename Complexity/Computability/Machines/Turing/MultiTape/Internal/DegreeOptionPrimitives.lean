/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Primitives
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option

/-!
# Direct degree certificates for option encoding machines

Construction and fixed-default elimination unpack the existing encoding capability's machine
witness. The temporary raw-linear encoding fields supply machine constructors only; no higher
tidy degree, polynomial-time, or linear closure rule is used.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInDegree

variable {β : Type*} {enc₁ : β ↪ List Bool}

/-- Construct an optional value in an encoding with the option capability. -/
theorem optionSome {enc : Option β ↪ List Bool} [OptionEncoding enc₁ enc] :
    ComputableInDegree some enc₁ enc 1 1 := by
  obtain ⟨c, k, Q, hfin, tm, htm⟩ := OptionEncoding.some (enc₁ := enc₁) (enc := enc)
  refine ⟨⟨_, _, ⟨c, fun _ => by simp⟩, ⟨c, fun _ => by simp⟩,
    k, Q, hfin, tm, fun a => (htm a).computesInTimeAndSpace⟩,
    ⟨c, fun a => ?_⟩⟩
  simpa using (htm a).length_output_le

/-- Eliminate an optional value using a fixed default, without a nonempty-type assumption. -/
theorem getD {enc : Option β ↪ List Bool} [OptionEncoding enc₁ enc] (d : β) :
    ComputableInDegree (fun o => o.getD d) enc enc₁ 1 1 := by
  obtain ⟨c, k, Q, hfin, tm, htm⟩ := OptionEncoding.getD (enc₁ := enc₁) (enc := enc) d
  refine ⟨⟨_, _, ⟨c, fun _ => by simp⟩, ⟨c, fun _ => by simp⟩,
    k, Q, hfin, tm, fun a => (htm a).computesInTimeAndSpace⟩,
    ⟨c, fun a => ?_⟩⟩
  simpa using (htm a).length_output_le

end Turing.MultiTapeTM.ComputableInDegree
