/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Fintype.Pi

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# The class BPP

`BPP` is defined through deterministic polynomial-time machines that read a random string
[Arora and Barak, Section 7.1][AroraBarak09]: `A ∈ BPP enc` when there are a polynomial `p`
and a function `V : α × List Bool → Bool`, computable in polynomial time on inputs
`encPair enc encBits (a, r) = frame (enc a) ++ r`, such that for every instance `a`, at least two
thirds of the random strings `r` of length `p (enc a).length` give the right answer:
`V (a, r) = true` exactly when `a ∈ A`.

The probability is written as a count over the random strings, which are functions
`Fin (p (enc a).length) → Bool`. The characterisation by probabilistic machines
(`Cslib.Complexity.mem_BPP_iff_exists_mem_BPTIME`) is proved in
`Complexity.Computability.Complexity.Classes.Time`.

## Main definitions

* `Cslib.Complexity.DecidesWithBoundedError`: the bounded-error condition.
* `Cslib.Complexity.BPP`.

## Main results

* `Cslib.Complexity.DecidesWithBoundedError.compl`: negating the verifier decides the complement
  with bounded error.
* `Cslib.Complexity.compl_mem_BPP`, `Cslib.Complexity.BPP_eq_preimage_compl_BPP`: `BPP` is closed
  under complement.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

/-- `V` decides `A` with bounded error, using random strings whose length is `p` evaluated at the
length of the encoded instance: for every instance `a`, at least two thirds of the random strings
`r` give the right answer, `V (a, r) = true` for members of `A` and `V (a, r) = false` for the
others. -/
def DecidesWithBoundedError (enc : α ↪ List Bool) (p : Polynomial ℕ) (V : α × List Bool → Bool)
    (A : Set α) : Prop :=
  ∀ a, (a ∈ A → 2 * 2 ^ p.eval (enc a).length ≤
      3 * (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn r) = true).card) ∧
    (a ∉ A → 2 * 2 ^ p.eval (enc a).length ≤
      3 * (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn r) = false).card)

/-- The problems decided with bounded error by polynomial-time machines reading polynomially long
random strings, with respect to the encoding `enc` of instances. -/
def BPP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧ DecidesWithBoundedError enc p V A}

theorem mem_BPP {enc : α ↪ List Bool} {A : Set α} :
    A ∈ BPP enc ↔ ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧
        DecidesWithBoundedError enc p V A :=
  Iff.rfl

namespace DecidesWithBoundedError

/-- Negating the verifier decides the complement with bounded error. -/
theorem compl {enc : α ↪ List Bool} {p : Polynomial ℕ} {V : α × List Bool → Bool} {A : Set α}
    (h : DecidesWithBoundedError enc p V A) :
    DecidesWithBoundedError enc p (fun x => !V x) Aᶜ := fun a => by
  simpa using (h a).symm

end DecidesWithBoundedError

/-- `BPP` is closed under complement. -/
theorem compl_mem_BPP {enc : α ↪ List Bool} {A : Set α} (hA : A ∈ BPP enc) : Aᶜ ∈ BPP enc :=
  let ⟨p, V, hV, h⟩ := hA
  ⟨p, fun x => !V x, ComputableTidilyInPolyTime.bool_not.comp hV, h.compl⟩

/-- `BPP` equals its preimage under complement. -/
theorem BPP_eq_preimage_compl_BPP (enc : α ↪ List Bool) : BPP enc = compl ⁻¹' BPP enc := by
  ext A
  refine ⟨compl_mem_BPP, fun hA => ?_⟩
  simpa using compl_mem_BPP hA

end Cslib.Complexity
