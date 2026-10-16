/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives

/-!
# Basic polynomial-time rules

Polynomial-time counterparts of Christian Reitwiessner's degree-bounded operations, and Boolean
rules for `fun_prop`.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.exists_degree`: polynomial-time functions
  admit explicit time and output degrees.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.of_finite`: functions on finite domains.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_eq`: equality for any fixed encoding.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}

/-- Compose in execution order. This also lets `fun_prop` infer the intermediate encoding from
the inner function when it cannot be inferred from the outer function. -/
@[fun_prop]
theorem trans {δ : Type} {encD : δ ↪ List Bool} {f : α → β} {g : β → δ}
    (hf : ComputableTidilyInPolyTime f encA encB)
    (hg : ComputableTidilyInPolyTime g encB encD) :
    ComputableTidilyInPolyTime (fun x => g (f x)) encA encD := hg.comp hf

/-- Project the first component of a polynomial-time pair-valued function. -/
@[fun_prop]
theorem fst' {δ : Type} {encD : δ ↪ List Bool} {f : α → β × δ}
    (hf : ComputableTidilyInPolyTime f encA (encPair encB encD)) :
    ComputableTidilyInPolyTime (fun x => (f x).1) encA encB :=
  (fst encB encD).comp hf

/-- Project the second component of a polynomial-time pair-valued function. -/
@[fun_prop]
theorem snd' {δ : Type} {encD : δ ↪ List Bool} {f : α → β × δ}
    (hf : ComputableTidilyInPolyTime f encA (encPair encB encD)) :
    ComputableTidilyInPolyTime (fun x => (f x).2) encA encD :=
  (snd encB encD).comp hf

/-- Every polynomial-time function admits explicit time and output degrees. -/
theorem exists_degree {f : α → β} (hf : ComputableTidilyInPolyTime f encA encB) :
    ∃ d e, ComputableTidilyInDegree f encA encB d e := by
  obtain ⟨t, s, ⟨ct, dt, ht⟩, ⟨cs, ds, hs⟩, hf⟩ := hf
  exact ⟨max dt ds, max dt ds, .of_bounds
    (DegreeBounded.mono_deg ⟨ct, ht⟩ (le_max_left dt ds))
    (DegreeBounded.mono_deg ⟨cs, hs⟩ (le_max_right dt ds)) hf⟩

/-- Every function on a finite domain is polynomial-time for any fixed encodings. -/
theorem of_finite [Finite α] (f : α → β) : ComputableTidilyInPolyTime f encA encB :=
  (ComputableTidilyInDegree.of_finite f).computableTidilyInPolyTime

@[fun_prop]
theorem bool_not : ComputableTidilyInPolyTime Bool.not encBool encBool := of_finite _

@[fun_prop]
theorem bool_and : ComputableTidilyInPolyTime (fun p : Bool × Bool => p.1 && p.2)
    (encPair encBool encBool) encBool := of_finite _

@[fun_prop]
theorem bool_or : ComputableTidilyInPolyTime (fun p : Bool × Bool => p.1 || p.2)
    (encPair encBool encBool) encBool := of_finite _

/-- Equality is polynomial-time for any encoding. -/
@[fun_prop]
theorem decide_eq [DecidableEq α] (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (fun p : α × α => decide (p.1 = p.2))
      (encPair enc enc) encBool :=
  (ComputableTidilyInDegree.eq enc).computableTidilyInPolyTime

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
