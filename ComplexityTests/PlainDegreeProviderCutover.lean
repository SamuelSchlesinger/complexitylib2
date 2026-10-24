/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree

/-! Original degree-provider imports expose plain rules with independent cost and output degrees. -/

open Turing.MultiTapeTM

universe u v w

example {α : Type u} {β : Type v} {γ : Type w} {f : β → γ} {g : α → β}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {d₁ e₁ d₂ e₂ : ℕ}
    (hf : ComputableInDegree f encB encC d₂ e₂)
    (hg : ComputableInDegree g encA encB d₁ e₁) :
    ComputableInDegree (f ∘ g) encA encC (max d₁ (e₁ * d₂)) (e₁ * e₂) :=
  ComputableInDegree.comp (hf := hf) (hg := hg)

-- A real constant machine on an infinite input type has zero cost and output degrees.
example : ComputableInDegree (fun _ : List Bool => false) encBits encBool 0 0 := by
  obtain ⟨c, h⟩ := computableInTimeAndSpace_of_const (encIn := encBits) (encOut := encBool) false
  exact .of_bounds ⟨c, fun _ => by simp⟩ ⟨0, fun _ => by simp⟩ h

example : ComputableInDegree (fun p : List Bool × Bool => (p.1, false))
    (encPair encBits encBool) (encPair encBits encBool) 1 1 := by
  exact (ComputableInDegree.fst encBits encBool).prod (ComputableInDegree.const false)

example : ComputableInDegree (fun p : List Bool × Bool => p.1)
    (encPair encBits encBool) encBits 1 1 :=
  ComputableInDegree.fst encBits encBool

run_cmd do
  let env ← Lean.getEnv
  for suffix in ["mono", "of_bounds", "of_linear", "comp", "restrict", "ite", "const",
      "of_eq", "append", "of_enc_eq", "pair", "prod", "fst", "snd", "fst'", "snd'",
      "of_finite", "optionSome", "getD", "headD", "tail", "isEmpty"] do
    let oldName := Lean.Name.str `Turing.MultiTapeTM.ComputableTidilyInDegree suffix
    let plainName := Lean.Name.str `Turing.MultiTapeTM.ComputableInDegree suffix
    if env.contains oldName then
      throwError "retired degree provider remains public: {oldName}"
    unless env.contains plainName do
      throwError "canonical degree provider missing: {plainName}"
