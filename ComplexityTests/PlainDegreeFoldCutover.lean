/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Fold

/-! Degree-bounded raw-bit folds preserve a constant output bound, including a captured
parameter. -/

open Turing.MultiTapeTM

example : ComputableInDegree (fun l : List Bool => l.foldl Bool.xor false)
    encBits encBool 2 0 := by
  have hl : ComputableInDegree (fun l : List Bool => l) encBits encBits 1 1 :=
    .of_eq (fun _ => rfl)
  have hi : ComputableInDegree (fun _ : List Bool => false) encBits encBool 1 0 := .const false
  have hs : ComputableInDegree (fun p : Bool × Bool => p.1 ^^ p.2)
      (encPair encBool encBool) encBool 1 0 := .of_finite _
  exact ComputableInDegree.foldl' (encA := encBool) (b := 0) hl hi hs
    (B := fun _ => 1) ⟨1, fun _ => by simp⟩ (fun _ _ _ => by simp)

example : ComputableInDegree
    (fun p : Bool × List Bool => p.2.foldl (fun acc b => acc ^^ b ^^ p.1) false)
    (encPair encBool encBits) encBool 2 0 := by
  have hp := ComputableInDegree.fst encBool encBits
  have hl := ComputableInDegree.snd encBool encBits
  have hi : ComputableInDegree (fun _ : Bool × List Bool => false)
      (encPair encBool encBits) encBool 1 0 := .const false
  have hs : ComputableInDegree
      (fun p : (Bool × Bool) × Bool => p.1.2 ^^ p.2 ^^ p.1.1)
      (encPair (encPair encBool encBool) encBool) encBool 1 0 := .of_finite _
  exact ComputableInDegree.foldlWith (encA := encBool) (b := 0)
    (step := fun p acc b => acc ^^ b ^^ p) hp hl hi hs
    (B := fun _ => 1) ⟨1, fun _ => by simp⟩ (fun _ _ _ => by simp)

run_cmd do
  let env ← Lean.getEnv
  for suffix in ["foldl'", "foldlWith"] do
    let oldName := Lean.Name.str `Turing.MultiTapeTM.ComputableTidilyInDegree suffix
    let plainName := Lean.Name.str `Turing.MultiTapeTM.ComputableInDegree suffix
    if env.contains oldName then throwError "retired degree fold remains public: {oldName}"
    unless env.contains plainName do throwError "plain degree fold missing: {plainName}"
