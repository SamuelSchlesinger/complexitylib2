/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PlainDirect.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PlainDirect.BigO
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PlainDirect.Degree
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id

/-! Spike for #862: plain closure rules proved without a tidy calculus. This file imports no tidy
asymptotic predicate, registers the direct plain rules with `fun_prop` locally, and closes goals
borrowed from `ComplexityTests/PolyTimePlain.lean`. A left fold computing the parity of a word and
a composition of upstream's (untidy) copy machine with itself check that the loop and Big-O rules
apply to real machines. -/

namespace ComplexityTests.PlainDirect

open Cslib Turing Turing.MultiTapeTM

/-! ### No tidy calculus in scope -/

/-- error: Unknown identifier `ComputableTidilyInPolyTime` -/
#guard_msgs in
#check ComputableTidilyInPolyTime

/-- error: Unknown identifier `ComputableTidilyInO` -/
#guard_msgs in
#check ComputableTidilyInO

/-! ### `fun_prop` with the direct plain rules only -/

section FunProp

universe u

variable {α β γ : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- Composition in execution order, which lets `fun_prop` infer the intermediate encoding from
the inner function. -/
theorem trans {f : α → β} {g : β → γ} (hf : ComputableInPolyTime f encIn encMid)
    (hg : ComputableInPolyTime g encMid encOut) :
    ComputableInPolyTime (fun x => g (f x)) encIn encOut :=
  PlainDirect.comp hg hf

/-- Pairing in `encPair`, the form `fun_prop` can use. -/
theorem prod {β₁ β₂ : Type} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool} {f : α → β₁}
    {g : α → β₂} (hf : ComputableInPolyTime f encIn enc₁)
    (hg : ComputableInPolyTime g encIn enc₂) :
    ComputableInPolyTime (fun x => (f x, g x)) encIn (encPair enc₁ enc₂) :=
  PlainDirect.pair hf hg

/-- The first component of a pair-valued function. -/
theorem fst' {β₁ β₂ : Type} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {f : α → β₁ × β₂} (hf : ComputableInPolyTime f encIn (encPair enc₁ enc₂)) :
    ComputableInPolyTime (fun x => (f x).1) encIn enc₁ :=
  PlainDirect.comp (PlainDirect.fst (enc₂ := enc₂)) hf

/-- The second component of a pair-valued function. -/
theorem snd' {β₁ β₂ : Type} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {f : α → β₁ × β₂} (hf : ComputableInPolyTime f encIn (encPair enc₁ enc₂)) :
    ComputableInPolyTime (fun x => (f x).2) encIn enc₂ :=
  PlainDirect.comp (PlainDirect.snd (enc₁ := enc₁)) hf

/-- Negation, a function on a finite type. -/
theorem bool_not : ComputableInPolyTime Bool.not encBool encBool :=
  .of_finite _

attribute [local fun_prop] PlainDirect.comp trans prod fst' snd' PlainDirect.ite bool_not

variable {enc : α ↪ List Bool}

/-- `PolyTimePlain`: a case distinction on plain hypotheses, with negation in one branch. -/
example {f g : α → Bool} (hf : ComputableInPolyTime f enc encBool)
    (hg : ComputableInPolyTime g enc encBool) :
    ComputableInPolyTime (fun a => if f a then !g a else g a) enc encBool := by fun_prop

/-- `PolyTimePlain`: projections of a pair-valued plain hypothesis. -/
example {β γ : Type} {encB : β ↪ List Bool} {encC : γ ↪ List Bool} {f : α → β × γ}
    (hf : ComputableInPolyTime f enc (encPair encB encC)) :
    ComputableInPolyTime (fun a => (f a).1) enc encB ∧
      ComputableInPolyTime (fun a => (f a).2) enc encC :=
  ⟨by fun_prop, by fun_prop⟩

/-- `PolyTimePlain`: negation of a projection. -/
example {δ : Type} {encD : δ ↪ List Bool} {f : α → δ × Bool}
    (hf : ComputableInPolyTime f enc (encPair encD encBool)) :
    ComputableInPolyTime (fun a => !(f a).2) enc encBool := by fun_prop

/-- Pairs, projections, negation and a case distinction together. -/
example {β : Type} {encB : β ↪ List Bool} {f : α → β × Bool} {g : α → Bool}
    (hf : ComputableInPolyTime f enc (encPair encB encBool))
    (hg : ComputableInPolyTime g enc encBool) :
    ComputableInPolyTime (fun a => (if g a then !(f a).2 else (f a).2, (f a).1)) enc
      (encPair encBool encB) := by fun_prop

/-- `PolyTimePlain`: without a hypothesis for `f`, `fun_prop` does not claim polynomial time. -/
example {f : α → Bool} (hf : ComputableInPolyTime f enc encBool) :
    ComputableInPolyTime (fun a => !f a) enc encBool := by
  fail_if_success (clear hf; fun_prop)
  fun_prop

end FunProp

/-! ### A loop on a real machine -/

/-- The parity of a word, by a left fold, from the direct plain loop rule: the list is the input,
the step is a function on a finite type, and every state is encoded in `2 n + 4` bits. -/
example : ComputableInPolyTime (fun w : List Bool => w.foldl (fun b x => b ^^ x) false)
    encBits encBool :=
  PlainDirect.foldl (encA := encBool) (encL := encBits) (encBA := encPair encBool encBool)
    (encS := encPair encBits encBool) (encO := encOption (encPair encBits encBool))
    (list := fun w => w) (init := fun _ => false) (step := fun b x => b ^^ x)
    (.of_eq fun _ => rfl) (.const false) (.of_finite _) (L := fun n => 2 * n + 4)
    (by fun_prop) (fun w => by simp [encBits]; omega) (fun w i hi => by simp)
    (fun w i hi => by simp [encBits]; omega)

/-! ### Bounds up to constants on a real machine -/

/-- Upstream's copy machine, which is not tidy, within linear time and space. -/
theorem computableInO_id :
    ComputableInO (fun w : List Bool => w) encBits encBits (fun w => w.length)
      (fun w => w.length) := by
  obtain ⟨k, State, hfin, tm, htm⟩ := computableInTimeAndSpace_id (enc := encBits)
  exact ⟨1, ⟨k, State, hfin, tm, htm.mono (fun _ => by simp [encBits]) (fun _ => Nat.zero_le _)⟩,
    fun _ => by simp [encBits]⟩

/-- The direct composition rule, on two untidy machines, with the bounds of the tidy rule. -/
example : ComputableInO (fun w : List Bool => w) encBits encBits
    (fun w => w.length + w.length) (fun w => w.length + w.length) :=
  PlainDirect.ComputableInO.comp computableInO_id computableInO_id

/-! ### Degrees on a real machine -/

/-- Upstream's copy machine, within time and workspace of degree one. -/
theorem computableInDegree_id :
    ComputableInDegree (fun w : List Bool => w) encBits encBits 1 1 :=
  ⟨⟨_, _, ⟨1, fun _ => by simp⟩, DegreeBounded.const 0, computableInTimeAndSpace_id⟩,
    ⟨1, fun _ => by simp [encBits]⟩⟩

/-- The direct composition rule keeps the degrees of the tidy rule. -/
example : ComputableInDegree (fun w : List Bool => w) encBits encBits 1 1 :=
  PlainDirect.ComputableInDegree.comp computableInDegree_id computableInDegree_id

/-! ### Axioms -/

/--
info: 'Turing.MultiTapeTM.PlainDirect.foldl' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PlainDirect.foldl

/--
info: 'Turing.MultiTapeTM.PlainDirect.ComputableInO.comp' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PlainDirect.ComputableInO.comp

end ComplexityTests.PlainDirect
