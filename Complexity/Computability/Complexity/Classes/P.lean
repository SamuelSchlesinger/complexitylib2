/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Encoding
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# The class P

A decision problem is a set `A : Set α` of instances, together with an encoding
`enc : α ↪ List Bool` of instances as binary words, in the style of
`Turing.MultiTapeTM.DecidableInTimeAndSpace`. It is in `P` when a Boolean function deciding
membership is computable in polynomial time (`Turing.MultiTapeTM.ComputableInPolyTime`) with
respect to `enc` and the encoding `Turing.MultiTapeTM.encBool` of answers
[Arora and Barak, Definition 1.13][AroraBarak09]. Equivalently, `A ∈ P enc` when upstream
`Turing.MultiTapeTM.DecidableInTimeAndSpace` holds within time and space bounded by polynomially
bounded functions of the length of the encoded instance
(`Cslib.Complexity.mem_P_iff_exists_decidableInTimeAndSpace`), and, as in the textbook
definition, a polynomial time bound alone suffices
(`Cslib.Complexity.mem_P_of_decidableInTimeAndSpace`).

Proofs usually build deciders with the tidy calculus, in which polynomial-time computability is
closed under composition. `Cslib.Complexity.mem_P_iff_tidy` states membership with a tidy decider
(`Turing.MultiTapeTM.ComputableTidilyInPolyTime`); the two notions agree
(`Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime`).

Mathlib's `Turing.TM2ComputableInPolyTime` is stated for Mathlib's stack machines; this file
uses cslib's multi-tape machines, which carry the time and space measures the rest of the
development is built on. For finite working alphabets and injective word encoders,
`Turing.TM2ComputableInPolyTime.computableTidilyInPolyTime` in
`Complexity.Computability.Machines.Turing.TM2.PolyTime` transfers Mathlib certificates to tidy
polynomial time, and so to this notion, under the standard binary encodings of their words.

## Main definitions

* `Cslib.Complexity.P`: problems decidable in polynomial time.

## Main results

* `Cslib.Complexity.mem_P_iff_tidy`: `P` with tidy deciders.
* `Cslib.Complexity.mem_P_iff_exists_decidableInTimeAndSpace`: `P` in terms of upstream
  `Turing.MultiTapeTM.DecidableInTimeAndSpace` with polynomially bounded time and space.
* `Cslib.Complexity.mem_P_of_decidableInTimeAndSpace`: a polynomial time bound alone suffices.
* `Cslib.Complexity.compl_mem_P`, `Cslib.Complexity.P_eq_preimage_compl_P`: `P` is closed under
  complement.

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
  {A | ∃ f : α → Bool, ComputableInPolyTime f enc encBool ∧ ∀ a, a ∈ A ↔ f a = true}

theorem mem_P {enc : α ↪ List Bool} {A : Set α} :
    A ∈ P enc ↔ ∃ f : α → Bool, ComputableInPolyTime f enc encBool ∧ ∀ a, a ∈ A ↔ f a = true :=
  Iff.rfl

/-- `P` with tidy deciders, the form in which proofs build them. -/
theorem mem_P_iff_tidy {enc : α ↪ List Bool} {A : Set α} :
    A ∈ P enc ↔
      ∃ f : α → Bool, ComputableTidilyInPolyTime f enc encBool ∧ ∀ a, a ∈ A ↔ f a = true := by
  simp only [mem_P, computableInPolyTime_iff_computableTidilyInPolyTime]

/-- **`P` in upstream terms:** `A ∈ P enc` exactly when some machine with a binary alphabet and
finitely many states decides `A` within time and space bounded by polynomially bounded functions
of the length of the encoded instance. -/
theorem mem_P_iff_exists_decidableInTimeAndSpace {enc : α ↪ List Bool} {A : Set α} :
    A ∈ P enc ↔ ∃ t s : ℕ → ℕ, PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
      DecidableInTimeAndSpace A enc (fun a => t (enc a).length) (fun a => s (enc a).length) :=
  ⟨fun ⟨f, ⟨t, s, ht, hs, hf⟩, hA⟩ => ⟨t, s, ht, hs, decidableInTimeAndSpace_iff.mpr ⟨f, hf, hA⟩⟩,
    fun ⟨t, s, ht, hs, h⟩ =>
      let ⟨f, hf, hA⟩ := decidableInTimeAndSpace_iff.mp h
      ⟨f, ⟨t, s, ht, hs, hf⟩, hA⟩⟩

/-- A problem that some machine decides within a time bound polynomial in the length of the
encoded instance, with any space bound, is in `P`, as in the textbook definition. -/
theorem mem_P_of_decidableInTimeAndSpace {enc : α ↪ List Bool} {A : Set α} {t : ℕ → ℕ}
    {s : α → ℕ} (ht : PolynomiallyBounded t)
    (h : DecidableInTimeAndSpace A enc (fun a => t (enc a).length) s) : A ∈ P enc :=
  let ⟨f, hf, hA⟩ := decidableInTimeAndSpace_iff.mp h
  ⟨f, hf.computableInPolyTime ht, hA⟩

/-- **`P` is closed under complement**: negate the answer of the decider. -/
theorem compl_mem_P {enc : α ↪ List Bool} {A : Set α} (hA : A ∈ P enc) : Aᶜ ∈ P enc :=
  let ⟨f, hf, h⟩ := hA
  ⟨fun a => !f a, ComputableInPolyTime.bool_not.comp hf,
    fun a => by simp [h a]⟩

/-- `P` equals its preimage under complement. -/
theorem P_eq_preimage_compl_P (enc : α ↪ List Bool) : P enc = compl ⁻¹' P enc :=
  Set.ext fun _ => ⟨compl_mem_P, fun h => by simpa using compl_mem_P h⟩

end Cslib.Complexity
