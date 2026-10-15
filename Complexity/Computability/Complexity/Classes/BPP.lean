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

/-!
# The class BPP

`BPP` is defined through deterministic polynomial-time machines that read a random string
[Arora and Barak, Section 7.1][AroraBarak09]: `A ∈ BPP enc` when there are a polynomial `p`
and a function `V : α × List Bool → Bool`, computable in polynomial time on inputs
`encPair enc encBits (a, r) = frame (enc a) ++ r`, such that for every instance `a`, at least two
thirds of the random strings `r` of length `p (enc a).length` give the right answer:
`V (a, r) = true` exactly when `a ∈ A`.

The probability is written as a count over the random strings, which are functions
`Fin (p (enc a).length) → Bool`. The characterisation by probabilistic machines is not proved
here.

## Main definitions

* `Cslib.Complexity.DecidesWithBoundedError`: the bounded-error condition.
* `Cslib.Complexity.BPP`.

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

end Cslib.Complexity
