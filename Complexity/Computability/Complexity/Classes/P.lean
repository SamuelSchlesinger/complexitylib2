/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Encoding
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# The class P

A decision problem is a set `A : Set α` of instances, together with an encoding
`enc : α ↪ List Bool` of instances as binary words, in the style of
`Turing.MultiTapeTM.DecidableInTimeAndSpace`. It is in `P` when a Boolean function deciding
membership is tidily computable in polynomial time (`Turing.MultiTapeTM.ComputableTidilyInPolyTime`)
with respect to `enc` and the encoding `Turing.MultiTapeTM.encBool` of answers
[Arora and Barak, Definition 1.13][AroraBarak09].

Polynomial time is taken in the tidy sense (the machine restores its work tapes and heads),
because that is the form in which polynomial-time computability is closed under composition.
It agrees with the plain notion: `A ∈ P enc` exactly when upstream
`Turing.MultiTapeTM.DecidableInTimeAndSpace` holds within time and space bounded by polynomially
bounded functions of the length of the encoded instance
(`Cslib.Complexity.mem_P_iff_exists_decidableInTimeAndSpace`), and, as in the textbook
definition, a polynomial time bound alone suffices
(`Cslib.Complexity.mem_P_of_decidableInTimeAndSpace`). Both follow from the tidy normal form
(`Turing.MultiTapeTM.computableTidilyInPolyTime_iff_exists_computableInTimeAndSpaceOfLength`).

Mathlib's `Turing.TM2ComputableInPolyTime` is stated for Mathlib's two-stack machines; this file
uses cslib's multi-tape machines, which carry the time and space measures the rest of the
development is built on.

## Main definitions

* `Cslib.Complexity.P`: problems decidable in polynomial time.

## Main results

* `Cslib.Complexity.mem_P_iff_exists_decidableInTimeAndSpace`: `P` in terms of upstream
  `Turing.MultiTapeTM.DecidableInTimeAndSpace` with polynomially bounded time and space.
* `Cslib.Complexity.mem_P_of_decidableInTimeAndSpace`: a polynomial time bound alone suffices.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type*}

/-- The problems decidable in polynomial time with respect to the encoding `enc`: `A ∈ P enc`
when a Boolean function deciding membership in `A` is computable in polynomial time. -/
def P (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f : α → Bool, ComputableTidilyInPolyTime f enc encBool ∧ ∀ a, a ∈ A ↔ f a = true}

theorem mem_P {enc : α ↪ List Bool} {A : Set α} :
    A ∈ P enc ↔
      ∃ f : α → Bool, ComputableTidilyInPolyTime f enc encBool ∧ ∀ a, a ∈ A ↔ f a = true :=
  Iff.rfl

/-- **`P` in upstream terms:** `A ∈ P enc` exactly when some machine with a binary alphabet and
finitely many states decides `A` within time and space bounded by polynomially bounded functions
of the length of the encoded instance. -/
theorem mem_P_iff_exists_decidableInTimeAndSpace {enc : α ↪ List Bool} {A : Set α} :
    A ∈ P enc ↔ ∃ t s : ℕ → ℕ, PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
      DecidableInTimeAndSpace A enc (fun a => t (enc a).length) (fun a => s (enc a).length) := by
  constructor
  · rintro ⟨f, hf, hA⟩
    obtain ⟨t, s, ht, hs, hf⟩ := hf.exists_computableInTimeAndSpaceOfLength
    exact ⟨t, s, ht, hs, decidableInTimeAndSpace_iff.mpr ⟨f, hf, hA⟩⟩
  · rintro ⟨t, s, ht, -, h⟩
    obtain ⟨f, hf, hA⟩ := decidableInTimeAndSpace_iff.mp h
    exact ⟨f, hf.computableTidilyInPolyTime ht, hA⟩

/-- A problem that some machine decides within a time bound polynomial in the length of the
encoded instance, with any space bound, is in `P`, as in the textbook definition. -/
theorem mem_P_of_decidableInTimeAndSpace {enc : α ↪ List Bool} {A : Set α} {t : ℕ → ℕ}
    {s : α → ℕ} (ht : PolynomiallyBounded t)
    (h : DecidableInTimeAndSpace A enc (fun a => t (enc a).length) s) : A ∈ P enc :=
  let ⟨f, hf, hA⟩ := decidableInTimeAndSpace_iff.mp h
  ⟨f, hf.computableTidilyInPolyTime ht, hA⟩

end Cslib.Complexity
