/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import all Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id

/-! Private normalization keeps the original quantitative contracts, including degree zero and
uncharged output under independent BigO bounds. These examples add no public tidy interface. -/

open Turing.MultiTapeTM

universe u v

example {α : Type u} {β : Type v} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {d e : ℕ} :
    ComputableInDegree f encIn encOut d e ↔ ComputableTidilyInDegree f encIn encOut d e :=
  ⟨Internal.normalizeDegree, Internal.forgetDegree⟩

example {α : Type u} {β : Type v} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {e : ℕ} :
    ComputableInDegree f encIn encOut 0 e ↔ ComputableTidilyInDegree f encIn encOut 0 e :=
  ⟨Internal.normalizeDegree, Internal.forgetDegree⟩

example {α : Type u} {β : Type v} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} :
    ComputableInLinearTimeAndSpace f encIn encOut ↔
      (∃ c, ComputableTidilyInTimeAndSpace f encIn encOut
        (fun a => c * ((encIn a).length + 1)) (fun a => c * ((encIn a).length + 1))) :=
  ⟨Internal.normalizeLinear, Internal.forgetLinear⟩

example {α : Type u} {β : Type v} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {T S : α → ℕ} :
    ComputableInBigO f encIn encOut T S ↔ ComputableTidilyInBigO f encIn encOut T S :=
  ⟨Internal.normalizeBigO, Internal.forgetBigO⟩

-- Constant output on the infinite word domain realizes both degree-zero bounds.
example : ComputableInDegree (fun _ : List Bool => false) encBits encBool 0 0 := by
  obtain ⟨c, hc⟩ := computableInTimeAndSpace_of_const (encIn := encBits) (encOut := encBool) false
  exact ⟨⟨fun _ => c, fun _ => 0, DegreeBounded.const c, DegreeBounded.const 0, hc⟩,
    DegreeBounded.const (encBool false).length⟩

-- The uncharged convention permits long output in constant work space.
example : ComputableInBigO (id : List Bool → List Bool) encBits encBits
    List.length (fun _ => 0) := by
  refine ⟨1, computableInTimeAndSpace_id.mono ?_ ?_⟩
  · intro a
    simp [encBits]
  · intro a
    simp

-- This is intentionally different from the value-charged convention.
example : ¬ ComputableInO (id : List Bool → List Bool) encBits encBits
    List.length (fun _ => 0) := by
  rintro ⟨c, _, hlen⟩
  have h := hlen (List.replicate (c + 1) false)
  simp only [id_eq, encBits_apply, List.length_replicate, Nat.zero_add, Nat.mul_one] at h
  omega
