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
  ComputableTidilyInDegree.int_succ ComputableTidilyInDegree.int_pred
  ComputableTidilyInO.foldl_bits_finite ComputableTidilyInTimeAndSpace.map_bits

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
