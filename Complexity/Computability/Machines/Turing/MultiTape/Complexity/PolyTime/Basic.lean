/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Basic polynomial-time rules

Polynomial-time counterparts of Christian Reitwiessner's degree-bounded operations, and Boolean
rules for `fun_prop`.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.exists_degree`: polynomial-time functions
  admit explicit time and output degrees.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.of_enc_eq`: reuse identical encoded outputs.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.of_finite`: functions on finite domains.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_eq`, `.beq`: equality for fixed encodings.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bool_and'`, `.decide_and`, `.cond`, `.ite_decide`:
  compound guards and conditionals with fixed intermediate Boolean encodings.
-/

@[expose] public section

/-- Apply a polynomial size bound to any input-size function. -/
theorem Turing.MultiTapeTM.PolyBounded.of_polynomiallyBounded {α : Type*}
    (size : α → ℕ) {bound : ℕ → ℕ} (hbound : Cslib.PolynomiallyBounded bound) :
    Turing.MultiTapeTM.PolyBounded size (fun a => bound (size a)) := by
  obtain ⟨c, d, h⟩ := Cslib.polynomiallyBounded_iff_le.mp hbound
  exact ⟨c, d, fun a => h (size a)⟩

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

/-- Reuse a computation when the new function emits the same encoded output word. -/
theorem of_enc_eq {δ : Type} {encD : δ ↪ List Bool} {f : α → β} {g : α → δ}
    (hf : ComputableTidilyInPolyTime f encA encB)
    (h : ∀ a, encD (g a) = encB (f a)) : ComputableTidilyInPolyTime g encA encD := by
  obtain ⟨d, e, hf⟩ := hf.exists_degree
  exact (hf.of_enc_eq h).computableTidilyInPolyTime

/-- Every function on a finite domain is polynomial-time for any fixed encodings. -/
theorem of_finite [Finite α] (f : α → β) : ComputableTidilyInPolyTime f encA encB :=
  (ComputableTidilyInDegree.of_finite f).computableTidilyInPolyTime

@[fun_prop]
theorem bool_not : ComputableTidilyInPolyTime Bool.not encBool encBool := of_finite _

@[fun_prop]
theorem bool_and : ComputableTidilyInPolyTime (fun p : Bool × Bool => p.1 && p.2)
    (encPair encBool encBool) encBool := of_finite _

/-- Conjoin computed guards, fixing both intermediate Boolean encodings. -/
@[fun_prop]
theorem bool_and' {left right : α → Bool}
    (hleft : ComputableTidilyInPolyTime left encA encBool)
    (hright : ComputableTidilyInPolyTime right encA encBool) :
    ComputableTidilyInPolyTime (fun a => left a && right a) encA encBool :=
  bool_and.comp (hleft.prod hright)

@[fun_prop]
theorem bool_or : ComputableTidilyInPolyTime (fun p : Bool × Bool => p.1 || p.2)
    (encPair encBool encBool) encBool := of_finite _

/-- Exclusive-or is a finite Boolean computation. -/
@[fun_prop]
theorem bool_xor : ComputableTidilyInPolyTime (fun p : Bool × Bool => p.1 ^^ p.2)
    (encPair encBool encBool) encBool := of_finite _

/-- Conjunction of efficiently decidable propositions uses the standard Boolean encoding. -/
@[fun_prop]
theorem decide_and {left right : α → Prop} [∀ a, Decidable (left a)] [∀ a, Decidable (right a)]
    (hleft : ComputableTidilyInPolyTime (fun a => decide (left a)) encA encBool)
    (hright : ComputableTidilyInPolyTime (fun a => decide (right a)) encA encBool) :
    ComputableTidilyInPolyTime (fun a => decide (left a ∧ right a)) encA encBool := by
  simpa only [Bool.decide_and, Function.comp_def] using bool_and.comp (hleft.prod hright)

/-- Disjunction of efficiently decidable propositions uses the standard Boolean encoding. -/
@[fun_prop]
theorem decide_or {left right : α → Prop} [∀ a, Decidable (left a)] [∀ a, Decidable (right a)]
    (hleft : ComputableTidilyInPolyTime (fun a => decide (left a)) encA encBool)
    (hright : ComputableTidilyInPolyTime (fun a => decide (right a)) encA encBool) :
    ComputableTidilyInPolyTime (fun a => decide (left a ∨ right a)) encA encBool := by
  simpa only [Bool.decide_or, Function.comp_def] using bool_or.comp (hleft.prod hright)

/-- A Boolean conditional fixes the guard encoding before automation synthesizes its proof. -/
@[fun_prop]
theorem cond {condition : α → Bool} {yes no : α → β}
    (hcondition : ComputableTidilyInPolyTime condition encA encBool)
    (hyes : ComputableTidilyInPolyTime yes encA encB)
    (hno : ComputableTidilyInPolyTime no encA encB) :
    ComputableTidilyInPolyTime (fun a => if condition a then yes a else no a) encA encB :=
  hcondition.ite' hyes hno

/-- A proposition-valued conditional computes its decision in the standard Boolean encoding. -/
@[fun_prop]
theorem ite_decide {condition : α → Prop} [∀ a, Decidable (condition a)] {yes no : α → β}
    (hcondition : ComputableTidilyInPolyTime (fun a => decide (condition a)) encA encBool)
    (hyes : ComputableTidilyInPolyTime yes encA encB)
    (hno : ComputableTidilyInPolyTime no encA encB) :
    ComputableTidilyInPolyTime (fun a => if condition a then yes a else no a) encA encB := by
  simpa only [decide_eq_true_eq] using hcondition.cond hyes hno

/-- Comparing two Boolean values is a finite-domain computation. -/
@[fun_prop]
theorem bool_beq : ComputableTidilyInPolyTime (fun p : Bool × Bool => p.1 == p.2)
    (encPair encBool encBool) encBool := of_finite _

/-- Equality is polynomial-time for any encoding. -/
@[fun_prop]
theorem decide_eq [DecidableEq α] (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (fun p : α × α => decide (p.1 = p.2))
      (encPair enc enc) encBool :=
  (ComputableTidilyInDegree.eq enc).computableTidilyInPolyTime

/-- Compare computed values for equality, inferring their common encoding from the arguments. -/
@[fun_prop]
theorem decide_eq' [DecidableEq β] {left right : α → β}
    (hleft : ComputableTidilyInPolyTime left encA encB)
    (hright : ComputableTidilyInPolyTime right encA encB) :
    ComputableTidilyInPolyTime (fun x => decide (left x = right x)) encA encBool :=
  (decide_eq encB).comp (hleft.prod hright)

/-- Lawful Boolean equality compares computed values through their common encoding. -/
@[fun_prop]
theorem beq [BEq β] [LawfulBEq β] {left right : α → β}
    (hleft : ComputableTidilyInPolyTime left encA encB)
    (hright : ComputableTidilyInPolyTime right encA encB) :
    ComputableTidilyInPolyTime (fun x => left x == right x) encA encBool := by
  classical
  simpa only [beq_eq_decide] using hleft.decide_eq' hright

/-- Compare two computed values using their common encoding. -/
@[fun_prop]
theorem decide_ne [DecidableEq β] {left right : α → β}
    (hleft : ComputableTidilyInPolyTime left encA encB)
    (hright : ComputableTidilyInPolyTime right encA encB) :
    ComputableTidilyInPolyTime (fun x => decide (left x ≠ right x)) encA encBool := by
  simpa only [Function.comp_def, decide_not] using
    bool_not.comp (hleft.decide_eq' hright)

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
