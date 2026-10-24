/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
/-! Plain fixed-finite tables, genuinely dependent values, and tagged sums. -/

open Turing.MultiTapeTM
namespace ComplexityTests.PlainFunctionFamilyCutover
abbrev Value : Bool → Type | false => Bool | true => ℕ
def encValue : (i : Bool) → Value i ↪ List Bool | false => encBool | true => encUnary
def family (p : ℕ × Bool) : (i : Bool) → Value i | false => p.2 | true => p.1
example : ComputableInPolyTime family (encPair encUnary encBool) (encDPi encValue) := by
  apply ComputableInPolyTime.dpi
  intro i
  cases i
  · exact ComputableInPolyTime.snd encUnary encBool
  · exact ComputableInPolyTime.fst encUnary encBool
example : ComputableInPolyTime (fun p : ℕ × Bool => Function.update (family p) true 7)
    (encPair encUnary encBool) (encDPi encValue) := by
  apply ComputableInPolyTime.dpi_update
  · apply ComputableInPolyTime.dpi
    intro i
    cases i
    · exact ComputableInPolyTime.snd encUnary encBool
    · exact ComputableInPolyTime.fst encUnary encBool
  · exact ComputableInPolyTime.const 7
example : ComputableInPolyTime
    (fun p : ℕ × Bool => (fun i : Bool => if i then p.1 else 0) p.2)
    (encPair encUnary encBool) encUnary := by
  apply ComputableInPolyTime.pi_apply' (indexEncoding := encBool)
    (values := fun (p : ℕ × Bool) (i : Bool) => if i then p.1 else 0) (index := Prod.snd)
  · apply ComputableInPolyTime.pi
    intro i
    cases i
    · exact ComputableInPolyTime.const 0
    · exact ComputableInPolyTime.fst encUnary encBool
  · exact ComputableInPolyTime.snd encUnary encBool
example : ComputableInPolyTime (Sum.inl (β := Bool)) encUnary (encSum encUnary encBool) :=
  ComputableInPolyTime.sumInl encUnary encBool
example : ComputableInPolyTime (Sum.inr (α := ℕ)) encBool (encSum encUnary encBool) :=
  ComputableInPolyTime.sumInr encUnary encBool
def encEmpty : Empty ↪ List Bool := ⟨Empty.elim, fun e => e.elim⟩
example : ComputableInPolyTime (fun _ : Bool => fun e : Empty => e) encBool
    (encPi encEmpty) := ComputableInPolyTime.pi (fun e => e.elim)
example : ComputableInPolyTime (fun e : Empty => e) encEmpty encEmpty :=
  ComputableInPolyTime.finite_cases (tagEncoding := encEmpty)
    (tag := fun e : Empty => e) (branch := fun _ e => e) (ComputableInPolyTime.id')
    (fun e => Empty.elim e)
run_meta do
  let env ← Lean.getEnv
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.finite_cases then
    throwError "retired finite_cases remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.finite_cases do
    throwError "plain finite_cases absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.ofFn then
    throwError "retired ofFn remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.ofFn do
    throwError "plain ofFn absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.pi then
    throwError "retired pi remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.pi do
    throwError "plain pi absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.pi_apply then
    throwError "retired pi_apply remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.pi_apply do
    throwError "plain pi_apply absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.pi_update then
    throwError "retired pi_update remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.pi_update do
    throwError "plain pi_update absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.pi_apply' then
    throwError "retired pi_apply' remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.pi_apply' do
    throwError "plain pi_apply' absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.pi_eval then
    throwError "retired pi_eval remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.pi_eval do
    throwError "plain pi_eval absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.pi_update' then
    throwError "retired pi_update' remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.pi_update' do
    throwError "plain pi_update' absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.dpi then
    throwError "retired dpi remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.dpi do
    throwError "plain dpi absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.dpi_apply then
    throwError "retired dpi_apply remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.dpi_apply do
    throwError "plain dpi_apply absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.dpi_update then
    throwError "retired dpi_update remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.dpi_update do
    throwError "plain dpi_update absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.sumInl then
    throwError "retired sumInl remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.sumInl do
    throwError "plain sumInl absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.sumInr then
    throwError "retired sumInr remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.sumInr do
    throwError "plain sumInr absent"
end ComplexityTests.PlainFunctionFamilyCutover
