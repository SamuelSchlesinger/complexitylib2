/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
open Turing.MultiTapeTM
example : ComputableInPolyTime (fun n : ℕ => Bool.not^[n] false) encUnary encBool := by
  apply ComputableInPolyTime.iterate_of_bounded_growth
    (ComputableInPolyTime.id') (ComputableInPolyTime.const false) ComputableInPolyTime.bool_not
    (growth := 0)
  intro state
  simp
example : ComputableInPolyTime (fun p : ℕ × Bool => (fun b => p.2 || b)^[p.1] false)
    (encPair encUnary encBool) encBool := by
  apply ComputableInPolyTime.iterateWith_of_bounded_growth
    (ComputableInPolyTime.snd encUnary encBool) (ComputableInPolyTime.fst encUnary encBool)
    (ComputableInPolyTime.const false) ComputableInPolyTime.bool_or
    (growth := fun _ => 0) (.const 0)
  intro p state
  simp
example : Bool.not^[3] false = true := rfl
example : (fun b => true || b)^[2] false = true := rfl
run_meta do
  let env ← Lean.getEnv
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterateWith then
    throwError "retired iterateWith remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.iterateWith do
    throwError "plain iterateWith absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterate then
    throwError "retired iterate remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.iterate do
    throwError "plain iterate absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterateWith_spec then
    throwError "retired iterateWith_spec remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.iterateWith_spec do
    throwError "plain iterateWith_spec absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterate_spec then
    throwError "retired iterate_spec remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.iterate_spec do
    throwError "plain iterate_spec absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterateWith_of_bounded_growth then
    throwError "retired iterateWith_of_bounded_growth remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.iterateWith_of_bounded_growth do
    throwError "plain iterateWith_of_bounded_growth absent"
  if env.contains
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterateWithInput_of_bounded_growth then
    throwError "retired iterateWithInput_of_bounded_growth remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.iterateWithInput_of_bounded_growth do
    throwError "plain iterateWithInput_of_bounded_growth absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterate_of_bounded_growth then
    throwError "retired iterate_of_bounded_growth remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.iterate_of_bounded_growth do
    throwError "plain iterate_of_bounded_growth absent"
