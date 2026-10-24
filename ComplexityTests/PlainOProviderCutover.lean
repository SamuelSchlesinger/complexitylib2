/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Option

/-! Ordinary charged-bound providers retain independent time and workspace and output accounting. -/

open Turing.MultiTapeTM

universe u v

example {α : Type u} {β : Type v} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s T S : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s) (ht : t ≼ T) (hs : s ≼ S)
    (hl : (fun a => (encOut (f a)).length) ≼ S) :
    ComputableInO f encIn encOut T S := .of_bigO h ht hs hl

example {α β γ : Type} {f : β → γ} {g : α → β}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {T₁ S₁ : α → ℕ} {T₂ S₂ : β → ℕ}
    (hf : ComputableInO f encB encC T₂ S₂) (hg : ComputableInO g encA encB T₁ S₁) :
    ComputableInO (f ∘ g) encA encC (fun a => T₁ a + T₂ (g a))
      (fun a => S₁ a + S₂ (g a)) := .comp hf hg

-- The output degree need not be bounded by the cost degree, even at zero cost degree.
example {α : Type u} {β : Type v} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (h : ComputableInDegree f encIn encOut 0 7) :
    ComputableInO f encIn encOut (fun _ => 1) (fun _ => 1) := by
  simpa using h.inO

example : ∃ T S, ComputableInO
    (fun p : Bool × List Bool => p.2.find? fun b => p.1 == b)
    (encPair encBool (encList encBool)) (encOption encBool) T S := by
  have ht := (ComputableInDegree.of_finite (encIn := encPair encBool encBool)
    (encMid := encBool) (fun p : Bool × Bool => p.1 == p.2)).inO_one
  have hp := (ComputableInDegree.fst encBool (encList encBool)).inO_one
  have hl := (ComputableInDegree.snd encBool (encList encBool)).inO_one
  exact ⟨_, _, ComputableInO.findWith ht hp hl⟩

-- An uncharged independent-bound witness needs no encoded-output premise.
example {α : Type u} {β : Type v} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s T S : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s) (ht : t ≼ T) (hs : s ≼ S) :
    ComputableInBigO f encIn encOut T S := .of_bounds h ht hs

run_cmd do
  let env ← Lean.getEnv
  for suffix in ["append", "comp", "comp_linear", "const", "eq", "eqWords", "filterWith",
      "findWith", "foldl", "foldlWith", "fst", "fst'", "ite", "length_le", "length_le_time",
      "mapWith", "mono", "mono_le", "of_encIn_eq", "of_enc_eq", "of_equiv", "pair", "prod",
      "snd", "snd'", "to_equiv", "weaken"] do
    let oldName := Lean.Name.str `Turing.MultiTapeTM.ComputableTidilyInO suffix
    let plainName := Lean.Name.str `Turing.MultiTapeTM.ComputableInO suffix
    if env.contains oldName then throwError "retired bound provider remains public: {oldName}"
    unless env.contains plainName do throwError "canonical bound provider missing: {plainName}"

-- The table has a fixed index type but stores values whose encoded width grows with the input.
example : ∃ T S, ComputableInO (fun n : ℕ => fun b : Bool => if b then n else 0)
    encUnary (encPi encUnary) T S := by
  have h : ∀ b : Bool, ComputableInDegree (fun n : ℕ => if b then n else 0)
      encUnary encUnary 1 1 := by
    intro b
    cases b
    · exact (ComputableInDegree.const (encIn := encUnary) (encMid := encUnary) 0).mono
    · exact .of_eq (fun _ => rfl)
  exact ⟨_, _, ComputableInO.pi (fun b => (h b).inO_one)⟩

example : ∃ T S, ComputableInO (fun n : ℕ => some n) encUnary (encOption encUnary) T S := by
  have h := (ComputableInO.getLeft? encUnary encBool).comp
    (ComputableInO.inl encUnary encBool)
  exact ⟨_, _, by simpa [Function.comp_def] using h⟩

example : ∃ T S, ComputableInO (fun o : Option ℕ => o.elim 0 id)
    (encOption encUnary) encUnary T S := by
  have hv := (ComputableInDegree.id' (enc := encOption encUnary)).inO_one
  have hf := ComputableInO.const (encIn := encOption encUnary) (encMid := encUnary) 0
  have hb := ComputableInO.snd (encOption encUnary) encUnary
  exact ⟨_, _, ComputableInO.optionElimWithInput hv hf hb⟩

run_cmd do
  let env ← Lean.getEnv
  for suffix in ["ofFn", "pi", "pi_apply", "pi_gather", "pi_update", "inl", "inr",
      "getLeft?", "getRight?", "optionElimWithInput"] do
    let oldName := Lean.Name.str `Turing.MultiTapeTM.ComputableTidilyInO suffix
    let plainName := Lean.Name.str `Turing.MultiTapeTM.ComputableInO suffix
    if env.contains oldName then throwError "retired provider remains public: {oldName}"
    unless env.contains plainName do throwError "plain provider missing: {plainName}"
