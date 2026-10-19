/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming
public import Mathlib.Tactic.FunProp

/-!
# Quantitative computability rules

`fun_prop (disch := lia)` composes degree certificates without replacing output-size bounds by
runtime bounds. Computation premises determine the intermediate encodings and degrees before the
arithmetic obligations compare the resulting degrees with the requested ones. The same `fun_prop`
interface recognizes ordinary finite-state bit folds with linear time and constant work space.
For nested projections with inferred degrees, `disch := first | apply le_refl | lia` first
instantiates a missing degree with the derived bound, then checks arithmetic inequalities.
Framed-list and option rules infer the payload encoding from the representation explicitly.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInDegree.comp_le`: composition at requested degrees.
* `Turing.MultiTapeTM.ComputableTidilyInDegree.prod_le`: pairing at requested degrees, retaining
  the components' output-size bounds.
* `Turing.MultiTapeTM.ComputableTidilyInDegree.bitsReverse`,
  `Turing.MultiTapeTM.ComputableTidilyInDegree.bitsDropLast`,
  `Turing.MultiTapeTM.ComputableTidilyInDegree.bitsGetLast`,
  `Turing.MultiTapeTM.ComputableTidilyInDegree.bitsGetLast?`,
  `Turing.MultiTapeTM.ComputableTidilyInDegree.optionBoolToList`,
  `Turing.MultiTapeTM.ComputableTidilyInDegree.bitsAppend`,
  `Turing.MultiTapeTM.ComputableTidilyInDegree.unaryAdd`: degree rules for raw bit-list reversal,
  prefix, last-bit extraction, concatenation, and unary addition.

## References

Uses Christian Reitwiessner's degree calculus and streaming backend; see the source markers in
`Degree.lean` and `Encodings/StreamFold.lean`.
-/

@[expose] public section

namespace Turing.MultiTapeTM

universe u

attribute [fun_prop] ComputableTidilyInDegree ComputableTidilyInO
attribute [fun_prop] ComputableTidilyInTimeAndSpace
attribute [fun_prop] ComputableTidilyInDegree.const ComputableTidilyInDegree.fst
  ComputableTidilyInDegree.snd ComputableTidilyInDegree.comp ComputableTidilyInDegree.prod
  ComputableTidilyInDegree.fst' ComputableTidilyInDegree.snd'
  ComputableTidilyInDegree.cons ComputableTidilyInDegree.snoc
  ComputableTidilyInDegree.listAppend ComputableTidilyInDegree.isSome
  ComputableTidilyInDegree.unary_succ ComputableTidilyInDegree.unary_pred
  ComputableTidilyInDegree.unary_sub ComputableTidilyInDegree.unary_min
  ComputableTidilyInDegree.int_succ ComputableTidilyInDegree.int_pred
  ComputableTidilyInO.foldl_bits_finite ComputableTidilyInTimeAndSpace.map_bits
  ComputableTidilyInTimeAndSpace.reverse_bits ComputableTidilyInTimeAndSpace.dropLast_bits
  ComputableTidilyInTimeAndSpace.getLast_bits ComputableTidilyInTimeAndSpace.getLast?_bits

namespace ComputableTidilyInDegree

/-- The result encoding fixes the element encoding, without reversing `ListEncoding` inference. -/
@[fun_prop]
theorem listTail {α : Type*} (enc : α ↪ List Bool) :
    ComputableTidilyInDegree List.tail (encList enc) (encList enc) 1 1 :=
  tail (enc₁ := enc)

/-- The framed input list determines the encoding of its head, including a fixed fallback. -/
@[fun_prop]
theorem listHeadD {α : Type*} (enc : α ↪ List Bool) (fallback : α) :
    ComputableTidilyInDegree (fun l => l.headD fallback) (encList enc) enc 1 1 :=
  headD (enc₁ := enc) fallback

/-- Testing a framed list for emptiness. -/
@[fun_prop]
theorem listIsEmpty {α : Type*} (enc : α ↪ List Bool) :
    ComputableTidilyInDegree List.isEmpty (encList enc) encBool 1 1 :=
  isEmpty (enc₁ := enc)

/-- The option encoding determines the encoding used for the payload and fallback. -/
@[fun_prop]
theorem optionGetD {α : Type*} (enc : α ↪ List Bool) (fallback : α) :
    ComputableTidilyInDegree (fun o => o.getD fallback) (encOption enc) enc 1 1 :=
  getD (enc₁ := enc) fallback

/-- Copy an encoded value. This identity rule also lets `fun_prop` retain a shared let binding. -/
@[fun_prop]
theorem id' {α : Type*} {enc : α ↪ List Bool} :
    ComputableTidilyInDegree (fun x : α => x) enc enc 1 1 :=
  of_eq fun _ => rfl

/-- Reverse a raw bit list in linear time and linear output size. -/
@[fun_prop]
theorem bitsReverse :
    ComputableTidilyInDegree List.reverse encBits encBits 1 1 :=
  of_bounds ⟨2, fun _ => by simp; omega⟩ ⟨0, fun _ => by simp⟩
    ComputableTidilyInTimeAndSpace.reverse_bits

/-- Drop the last bit of a raw bit list in linear time and linear output size. -/
@[fun_prop]
theorem bitsDropLast :
    ComputableTidilyInDegree List.dropLast encBits encBits 1 1 :=
  of_bounds ⟨8, fun _ => by simp; omega⟩ ⟨0, fun _ => by simp⟩
    ComputableTidilyInTimeAndSpace.dropLast_bits

/-- Extract the last bit of a raw bit list as a 0-or-1-element list in linear time and constant
output size. -/
@[fun_prop]
theorem bitsGetLast :
    ComputableTidilyInDegree (fun l : List Bool => l.getLast?.toList) encBits encBits 1 0 :=
  ⟨⟨_, _, ⟨8, fun _ => by simp; omega⟩, ⟨0, fun _ => by simp⟩,
    ComputableTidilyInTimeAndSpace.getLast_bits⟩,
    ⟨1, fun l => by simp [Option.length_toList_le]⟩⟩

/-- Extract the last bit of a raw bit list as an `Option Bool` in linear time and constant output
size. -/
@[fun_prop]
theorem bitsGetLast? :
    ComputableTidilyInDegree (List.getLast? (α := Bool)) encBits (encOption encBool) 1 0 :=
  ⟨⟨_, _, ⟨8, fun _ => by simp; omega⟩, ⟨0, fun _ => by simp⟩,
    ComputableTidilyInTimeAndSpace.getLast?_bits⟩,
    ⟨2, fun l => by cases h : l.getLast? <;> simp [h]⟩⟩

/-- Convert an `Option Bool` to a 0-or-1-element bit list in linear time and linear output size. -/
@[fun_prop]
theorem optionBoolToList :
    ComputableTidilyInDegree (Option.toList (α := Bool)) (encOption encBool) encBits 1 1 :=
  of_linear (.of_tail fun o => by cases o <;> rfl)

/-- Concatenate two raw bit lists while preserving their time and output degrees independently. -/
@[fun_prop]
theorem bitsAppend {α : Type*} {encIn : α ↪ List Bool} {f g : α → List Bool}
    {df ef dg eg d e : ℕ}
    (hf : ComputableTidilyInDegree f encIn encBits df ef)
    (hg : ComputableTidilyInDegree g encIn encBits dg eg)
    (hd : max df dg ≤ d) (he : max ef eg ≤ e) :
    ComputableTidilyInDegree (fun x => f x ++ g x) encIn encBits d e :=
  (hf.append hg fun _ => rfl).mono hd he

/-- Add two unary natural numbers while preserving their time and output degrees independently. -/
@[fun_prop]
theorem unaryAdd {α : Type*} {encIn : α ↪ List Bool} {f g : α → ℕ}
    {df ef dg eg d e : ℕ}
    (hf : ComputableTidilyInDegree f encIn encUnary df ef)
    (hg : ComputableTidilyInDegree g encIn encUnary dg eg)
    (hd : max df dg ≤ d) (he : max ef eg ≤ e) :
    ComputableTidilyInDegree (fun x => f x + g x) encIn encUnary d e :=
  (hf.append hg fun _ => List.replicate_add _ _ true).mono hd he

/-- Compose using the intermediate output size. The computation premises determine the degrees
before arithmetic compares them with the requested bound. -/
@[fun_prop]
theorem comp_le {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
    {encOut : γ ↪ List Bool} {f : β → γ} {g : α → β} {df ef dg eg d e : ℕ}
    (hg : ComputableTidilyInDegree g encIn encMid dg eg)
    (hf : ComputableTidilyInDegree f encMid encOut df ef)
    (hd : max dg (eg * df) ≤ d) (he : eg * ef ≤ e) :
    ComputableTidilyInDegree (fun x => f (g x)) encIn encOut d e :=
  (hf.comp hg).mono hd he

/-- Pair two results while preserving their output degrees independently of computation time. -/
@[fun_prop]
theorem prod_le {α β γ : Type u} {encIn : α ↪ List Bool} {encF : β ↪ List Bool}
    {encG : γ ↪ List Bool} {f : α → β} {g : α → γ} {df ef dg eg d e : ℕ}
    (hf : ComputableTidilyInDegree f encIn encF df ef)
    (hg : ComputableTidilyInDegree g encIn encG dg eg)
    (hd : max df dg ≤ d) (he : max ef eg ≤ e) :
    ComputableTidilyInDegree (fun x => (f x, g x)) encIn (encPair encF encG) d e :=
  (hf.prod hg).mono hd he

/-- Branching on a computed Boolean, retaining each branch's output degree. -/
@[fun_prop]
theorem ite_le {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {condition : α → Bool} {f g : α → β} {dc ec df ef dg eg d e : ℕ}
    (hc : ComputableTidilyInDegree condition encIn encBool dc ec)
    (hf : ComputableTidilyInDegree f encIn encOut df ef)
    (hg : ComputableTidilyInDegree g encIn encOut dg eg)
    (hd : max dc (max df dg) ≤ d) (he : max ef eg ≤ e) :
    ComputableTidilyInDegree (fun x => if condition x then f x else g x) encIn encOut d e :=
  (hc.ite (hf.restrict _) (hg.restrict _)).mono hd he

end ComputableTidilyInDegree

end Turing.MultiTapeTM
