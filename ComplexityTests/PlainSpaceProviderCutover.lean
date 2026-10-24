/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Bit

/-! Plain space providers retain the encoded-output charge, arbitrary time and runtime inputs. -/

open Turing.MultiTapeTM

universe u v

example {α : Type u} {β : Type v} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {S : α → ℕ}
    (h : ComputableInSpace f encIn encOut S) : ∃ T, ComputableInO f encIn encOut T S :=
  h.exists_inO

example : ComputableInSpace (id : List Bool → List Bool) encBits encBits List.length :=
  .of_inO (ComputableInDegree.of_eq (encIn := encBits) (encMid := encBits) (fun _ => rfl)).inO_one

-- Zero work space alone does not suffice: this notion also charges the encoded output.
example : ¬ComputableInSpace (id : List Bool → List Bool) encBits encBits (fun _ => 0) := by
  rintro ⟨t, c, -, hl⟩
  simpa [encBits] using hl (List.replicate (c + 1) true)

example : ComputableInSpace (fun q : ℕ × ℕ => q.1.testBit q.2)
    (encPair encNat encNat) encBool
    (fun q => 32 * ((encPair encNat encNat q).length + 1)) := .natTestBit

example : ComputableInSpace (fun q : ℕ × ℕ => q.1 / q.2)
    (encPair encNat encNat) encNat
    (fun q => 16 * ((encPair encNat encNat q).length + 1)) := .natDiv

-- Both the list length and the width of its captured addend vary with the input.
example : ∃ S, ComputableInSpace (fun p : ℕ × List ℕ => p.2.map (fun n => p.1 + n))
    (encPair encNat (encList encNat)) (encList encNat) S := by
  have hp := ComputableInSpace.fst encNat (encList encNat)
  have hl := ComputableInSpace.snd encNat (encList encNat)
  exact ⟨_, ComputableInSpace.mapWith (f := fun p : ℕ × ℕ => p.1 + p.2)
    ComputableInSpace.natAdd hp hl⟩

-- The state type is fixed; the binary iteration count remains an unbounded runtime input.
example : ∃ S, ComputableInSpace (fun p : ℕ × Bool => Bool.not^[p.1] p.2)
    (encPair encNat encBool) encBool S := by
  have hn := ComputableInSpace.fst encNat encBool
  have hi := ComputableInSpace.snd encNat encBool
  have hs := ComputableInSpace.of_finite (encIn := encBool) (encB := encBool) Bool.not
  exact ⟨_, ComputableInSpace.iterate hn hi hs (Q := fun _ => 1) (B := fun _ => 1)
    (fun _ _ _ => by change 1 ≤ 1; omega) (fun _ _ _ => by change 1 ≤ 1; omega)⟩

run_cmd do
  let env ← Lean.getEnv
  for suffix in [
      "append", "budget_comp", "budget_comp_lin", "budget_comp_linear", "budget_cons",
      "budget_const", "budget_finMod", "budget_finite", "budget_headD", "budget_isEmpty",
      "budget_ite", "budget_iterate", "budget_length", "budget_natAdd", "budget_natDiv",
      "budget_natEq", "budget_natIsZero", "budget_natLt", "budget_natMod", "budget_natMul",
      "budget_natPow", "budget_natPred", "budget_natSub", "budget_natSucc", "budget_optionSome",
      "budget_prod", "budget_tail", "comp", "const", "dispatch",
      "foldl", "fst", "fst'", "getD", "ite",
      "iterate", "length", "length_le", "mapWith", "mono_le",
      "natAdd", "natDiv", "natDivMod", "natEq", "natIsZero",
      "natLt", "natMod", "natMul", "natPred", "natSub",
      "natSucc", "natTestBit", "of_encIn_eq", "of_enc_eq", "of_finite",
      "of_inO", "prod", "replicate", "set", "snd",
      "snd'", "weaken"
      ] do
    let oldName := Lean.Name.str `Turing.MultiTapeTM.ComputableTidilyInSpace suffix
    let plainName := Lean.Name.str `Turing.MultiTapeTM.ComputableInSpace suffix
    if env.contains oldName then throwError "retired space provider remains public: {oldName}"
    unless env.contains plainName do throwError "plain space provider missing: {plainName}"
