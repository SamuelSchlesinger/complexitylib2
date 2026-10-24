/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-! Original Core/Basic imports provide plain composition, guards, folds and degree extraction. -/

open Turing.MultiTapeTM

example {α : Type} {input : α ↪ List Bool} {left right : α → Bool}
    (hl : ComputableInPolyTime left input encBool)
    (hr : ComputableInPolyTime right input encBool) :
    ComputableInPolyTime (fun a => left a && !right a) input encBool := by fun_prop

example {α : Type} [DecidableEq α] (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : α × α => decide (p.1 = p.2))
      (encPair enc enc) encBool := by fun_prop

example : ComputableInPolyTime (fun n : ℕ => n + 1) encNat encNat := by fun_prop

example : ∃ d e, ComputableInDegree (fun _ : List Bool => false) encBits encBool d e :=
  (ComputableInPolyTime.const false).exists_degree

example : ComputableInPolyTime (fun l : List Bool => l.foldl (fun _ bit => bit) false)
    encBits encBool := by
  apply ComputableInPolyTime.foldl (encA := encBool) (encL := encBits)
    (encBA := encPair encBool encBool) (encS := encPair encBits encBool)
    (encO := encOption (encPair encBits encBool))
    ComputableInPolyTime.id' (ComputableInPolyTime.const false)
    (ComputableInPolyTime.snd encBool encBool)
    (lMax := fun l => 2 * l.length + 2) (aMax := fun _ => 4)
    (((PolyBounded.const 2).mul .self).add (.const 2)) (.const 4) .self
  · intro l i hi
    simp
  · intro l i hi
    simp only [length_encPair, encBits_apply, encBool_apply, List.length_singleton,
      List.length_drop]
    omega

-- A concrete degree-zero certificate on an infinite input type uses no tidy interface.
example : ComputableInPolyTime (fun _ : List Bool => false) encBits encBool := by
  obtain ⟨c, h⟩ := computableInTimeAndSpace_of_const (encIn := encBits) (encOut := encBool) false
  have hzero : ComputableInDegree (fun _ : List Bool => false) encBits encBool 0 0 :=
    ⟨⟨_, _, ⟨c, fun _ => by simp⟩, ⟨0, fun _ => by simp⟩, h⟩, ⟨1, fun _ => by simp⟩⟩
  exact hzero.computableInPolyTime

run_meta do
  for name in [`Turing.MultiTapeTM.ComputableTidilyInPolyTime.comp,
      `Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldl,
      `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bool_and,
      `Turing.MultiTapeTM.ComputableTidilyInPolyTime.exists_degree,
      `Turing.MultiTapeTM.computableTidilyInPolyTime_succ] do
    if (← Lean.getEnv).contains name then
      throwError "the superseded source export {name} remains"
