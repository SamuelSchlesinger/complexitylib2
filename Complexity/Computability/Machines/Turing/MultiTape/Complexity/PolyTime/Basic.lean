/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Basic polynomial-time rules

Polynomial-time counterparts of Christian Reitwiessner's degree-bounded operations, and Boolean
rules for `fun_prop`.

## Main results

* `Turing.MultiTapeTM.PolyBounded.exists_polynomial`: express a resource bound by a polynomial.

* `Turing.MultiTapeTM.ComputableInPolyTime.exists_degree`: polynomial-time functions
  admit explicit time and output degrees.
* `Turing.MultiTapeTM.ComputableInPolyTime.polyBounded`: a computed unary value bounds
  resources polynomially in the original input encoding.
* `Turing.MultiTapeTM.ComputableInPolyTime.of_enc_eq`: reuse identical encoded outputs.
* `Turing.MultiTapeTM.ComputableInPolyTime.encoded`, `.unframe`, `.dropFrame`: compose
  encoded values and total frame parsing without requiring an inverse for an encoding.
* `Turing.MultiTapeTM.ComputableInPolyTime.of_finite`: functions on finite domains.
* `Turing.MultiTapeTM.ComputableInPolyTime.fstWithEncoding`, `.sndWithEncoding`: projections
  that compose with a known encoding conversion.
* `Turing.MultiTapeTM.ComputableInPolyTime.decide_eq`, `.beq`: equality for fixed encodings.
* `Turing.MultiTapeTM.ComputableInPolyTime.bool_and'`, `.decide_and`, `.cond`, `.ite_decide`:
  compound guards and conditionals with fixed intermediate Boolean encodings.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- A polynomially bounded resource admits a polynomial upper bound at every input size. -/
theorem PolyBounded.exists_polynomial {α : Type*} {size u : α → ℕ}
    (h : PolyBounded size u) : ∃ p : Polynomial ℕ, ∀ a, u a ≤ p.eval (size a) := by
  obtain ⟨c, d, hle⟩ := h.exists_le
  exact ⟨Polynomial.C c * (Polynomial.X + 1) ^ d, fun a => by simpa using hle a⟩

end Turing.MultiTapeTM

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}

/-- An efficiently computed unary value is polynomially bounded in the original encoded input.
This supplies input-dependent resource bounds without exposing their polynomial coefficients. -/
theorem polyBounded {f : α → ℕ} (hf : ComputableInPolyTime f encA encUnary) :
    PolyBounded (fun x => (encA x).length) f := by
  simpa only [encUnary_apply, List.length_replicate] using hf.polyBounded_length

/-- Project a first component and convert its encoding. Certifying the pair-valued function first
determines the source encoding before automation searches for the conversion certificate. -/
@[fun_prop]
theorem fstWithEncoding {γ : Type} {encC : γ ↪ List Bool}
    {output : α ↪ List Bool} {f : γ → α × β}
    (hf : ComputableInPolyTime f encC (encPair encA encB))
    (h : ComputableInPolyTime (fun a => a) encA output) :
    ComputableInPolyTime (fun p => (f p).1) encC output :=
  h.comp hf.fst'

/-- Project a second component and convert its encoding. The pair certificate fixes the source
encoding; the conversion certificate supplies the efficient change of representation. -/
@[fun_prop]
theorem sndWithEncoding {γ : Type} {encC : γ ↪ List Bool}
    {output : β ↪ List Bool} {f : γ → α × β}
    (hf : ComputableInPolyTime f encC (encPair encA encB))
    (h : ComputableInPolyTime (fun a => a) encB output) :
    ComputableInPolyTime (fun p => (f p).2) encC output :=
  h.comp hf.snd'

/-- Every polynomial-time function admits explicit time and output degrees. -/
theorem exists_degree {f : α → β} (hf : ComputableInPolyTime f encA encB) :
    ∃ d e, ComputableInDegree f encA encB d e := by
  obtain ⟨t, s, ht, hs, h⟩ := hf
  obtain ⟨ct, dt, ht⟩ := Cslib.polynomiallyBounded_iff_le.mp ht
  obtain ⟨cs, ds, hs⟩ := Cslib.polynomiallyBounded_iff_le.mp hs
  have htime : DegreeBounded (fun a => (encA a).length)
      (fun a => t (encA a).length) (max dt ds) :=
    DegreeBounded.mono_deg ⟨ct, fun a => ht (encA a).length⟩ (le_max_left dt ds)
  have hspace : DegreeBounded (fun a => (encA a).length)
      (fun a => s (encA a).length) (max dt ds) :=
    DegreeBounded.mono_deg ⟨cs, fun a => hs (encA a).length⟩ (le_max_right dt ds)
  exact ⟨max dt ds, max dt ds, ⟨⟨_, _, htime, hspace, h⟩, htime.mono h.length_le⟩⟩


/-- Reuse a computation when the new function emits the same encoded output word. -/
theorem of_enc_eq {δ : Type} {encD : δ ↪ List Bool} {f : α → β} {g : α → δ}
    (hf : ComputableInPolyTime f encA encB)
    (h : ∀ a, encD (g a) = encB (f a)) : ComputableInPolyTime g encA encD :=
  let ⟨t, s, ht, hs, k, State, hfinite, tm, htm⟩ := hf
  ⟨t, s, ht, hs, k, State, hfinite, tm, fun a => h a ▸ htm a⟩

/-- Expose an already encoded value as a raw word. No inverse for the encoding is required. -/
@[fun_prop]
theorem encode (enc : α ↪ List Bool) : ComputableInPolyTime enc enc encBits :=
  of_eq fun _ => rfl

/-- Compute a value and expose its representation, inferring that representation from the
supplied certificate before composing. -/
@[fun_prop]
theorem encoded {f : α → β} (hf : ComputableInPolyTime f encA encB) :
    ComputableInPolyTime (fun a => encB (f a)) encA encBits :=
  hf.of_enc_eq fun _ => rfl

/-- Read the first frame from any raw word, including malformed encodings. -/
@[fun_prop]
theorem unframe : ComputableInPolyTime Turing.MultiTapeTM.unframe encBits encBits :=
  of_linear (.of_unframe fun _ => rfl)

/-- Drop the first frame from any raw word, including malformed encodings. -/
@[fun_prop]
theorem dropFrame : ComputableInPolyTime Turing.MultiTapeTM.dropFrame encBits encBits :=
  of_linear (.of_dropFrame fun _ => rfl)

@[fun_prop]
theorem bool_not : ComputableInPolyTime Bool.not encBool encBool := of_finite _

@[fun_prop]
theorem bool_and : ComputableInPolyTime (fun p : Bool × Bool => p.1 && p.2)
    (encPair encBool encBool) encBool := of_finite _

/-- Conjoin computed guards, fixing both intermediate Boolean encodings. -/
@[fun_prop]
theorem bool_and' {left right : α → Bool}
    (hleft : ComputableInPolyTime left encA encBool)
    (hright : ComputableInPolyTime right encA encBool) :
    ComputableInPolyTime (fun a => left a && right a) encA encBool :=
  bool_and.comp (hleft.prod hright)

@[fun_prop]
theorem bool_or : ComputableInPolyTime (fun p : Bool × Bool => p.1 || p.2)
    (encPair encBool encBool) encBool := of_finite _

/-- Exclusive-or is a finite Boolean computation. -/
@[fun_prop]
theorem bool_xor : ComputableInPolyTime (fun p : Bool × Bool => p.1 ^^ p.2)
    (encPair encBool encBool) encBool := of_finite _

/-- Conjunction of efficiently decidable propositions uses the standard Boolean encoding. -/
@[fun_prop]
theorem decide_and {left right : α → Prop} [∀ a, Decidable (left a)] [∀ a, Decidable (right a)]
    (hleft : ComputableInPolyTime (fun a => decide (left a)) encA encBool)
    (hright : ComputableInPolyTime (fun a => decide (right a)) encA encBool) :
    ComputableInPolyTime (fun a => decide (left a ∧ right a)) encA encBool := by
  simpa only [Bool.decide_and, Function.comp_def] using bool_and.comp (hleft.prod hright)

/-- Disjunction of efficiently decidable propositions uses the standard Boolean encoding. -/
@[fun_prop]
theorem decide_or {left right : α → Prop} [∀ a, Decidable (left a)] [∀ a, Decidable (right a)]
    (hleft : ComputableInPolyTime (fun a => decide (left a)) encA encBool)
    (hright : ComputableInPolyTime (fun a => decide (right a)) encA encBool) :
    ComputableInPolyTime (fun a => decide (left a ∨ right a)) encA encBool := by
  simpa only [Bool.decide_or, Function.comp_def] using bool_or.comp (hleft.prod hright)

/-- A Boolean conditional fixes the guard encoding before automation synthesizes its proof. -/
@[fun_prop]
theorem cond {condition : α → Bool} {yes no : α → β}
    (hcondition : ComputableInPolyTime condition encA encBool)
    (hyes : ComputableInPolyTime yes encA encB)
    (hno : ComputableInPolyTime no encA encB) :
    ComputableInPolyTime (fun a => if condition a then yes a else no a) encA encB :=
  hcondition.ite' hyes hno

/-- A proposition-valued conditional computes its decision in the standard Boolean encoding. -/
@[fun_prop]
theorem ite_decide {condition : α → Prop} [∀ a, Decidable (condition a)] {yes no : α → β}
    (hcondition : ComputableInPolyTime (fun a => decide (condition a)) encA encBool)
    (hyes : ComputableInPolyTime yes encA encB)
    (hno : ComputableInPolyTime no encA encB) :
    ComputableInPolyTime (fun a => if condition a then yes a else no a) encA encB := by
  simpa only [decide_eq_true_eq] using hcondition.cond hyes hno

/-- Comparing two Boolean values is a finite-domain computation. -/
@[fun_prop]
theorem bool_beq : ComputableInPolyTime (fun p : Bool × Bool => p.1 == p.2)
    (encPair encBool encBool) encBool := of_finite _

/-- Equality is polynomial-time for any encoding. -/
@[fun_prop]
theorem decide_eq [DecidableEq α] (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : α × α => decide (p.1 = p.2))
      (encPair enc enc) encBool :=
  by
    obtain ⟨⟨_, _, ht, hs, h⟩, _⟩ := ComputableTidilyInDegree.eq enc
    obtain ⟨T, hT, ht⟩ := ht.polyBounded
    obtain ⟨S, hS, hs⟩ := hs.polyBounded
    exact ⟨T, S, hT, hS, (h.mono ht hs).computableInTimeAndSpace⟩

/-- Compare computed values for equality, inferring their common encoding from the arguments. -/
@[fun_prop]
theorem decide_eq' [DecidableEq β] {left right : α → β}
    (hleft : ComputableInPolyTime left encA encB)
    (hright : ComputableInPolyTime right encA encB) :
    ComputableInPolyTime (fun x => decide (left x = right x)) encA encBool :=
  (decide_eq encB).comp (hleft.prod hright)

/-- Lawful Boolean equality compares computed values through their common encoding. -/
@[fun_prop]
theorem beq [BEq β] [LawfulBEq β] {left right : α → β}
    (hleft : ComputableInPolyTime left encA encB)
    (hright : ComputableInPolyTime right encA encB) :
    ComputableInPolyTime (fun x => left x == right x) encA encBool := by
  classical
  simpa only [beq_eq_decide] using hleft.decide_eq' hright

/-- Compare two computed values using their common encoding. -/
@[fun_prop]
theorem decide_ne [DecidableEq β] {left right : α → β}
    (hleft : ComputableInPolyTime left encA encB)
    (hright : ComputableInPolyTime right encA encB) :
    ComputableInPolyTime (fun x => decide (left x ≠ right x)) encA encBool := by
  simpa only [Function.comp_def, decide_not] using
    bool_not.comp (hleft.decide_eq' hright)

end Turing.MultiTapeTM.ComputableInPolyTime
