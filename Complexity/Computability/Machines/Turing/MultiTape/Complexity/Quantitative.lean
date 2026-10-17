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
  ComputableTidilyInO.foldl_bits_finite ComputableTidilyInTimeAndSpace.map_bits

namespace ComputableTidilyInDegree

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

end ComputableTidilyInDegree

end Turing.MultiTapeTM
