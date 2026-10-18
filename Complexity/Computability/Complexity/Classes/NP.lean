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

/-!
# The class NP

`NP` is defined through polynomial-time verifiers [Arora and Barak, Definition 2.1][AroraBarak09]:
`A ∈ NP enc` when there are a polynomial `p` and a function `V : α × List Bool → Bool`, computable
in polynomial time on inputs `encPair enc encBits (a, w) = frame (enc a) ++ w`, such that `a ∈ A`
exactly when some certificate `w` of length `p (enc a).length` makes `V (a, w)` true.

Two details follow the textbook and matter for reductions. The certificate length is fixed, so the
input length of the verifier is a function of the instance alone. And `p` is a polynomial, not
merely a polynomially bounded function: a reduction from an `NP` problem must be able to compute
where the certificate ends, which an arbitrary bound would not allow.

`NP` is exactly the class of problems decided in polynomial time by nondeterministic machines
with a binary alphabet and finitely many states (`Cslib.Complexity.mem_NP_iff_decidableInPolyTime`
in `Complexity.Computability.Complexity.Classes.NP.Nondeterministic`): such a machine guesses a
certificate and verifies it, and conversely a verifier checks an encoded accepting computation.

## Main definitions

* `Cslib.Complexity.IsVerifier`: the verifier condition.
* `Cslib.Complexity.NP`, `Cslib.Complexity.coNP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

/-- `V` verifies `A` with certificates whose length is `p` evaluated at the length of the encoded
instance: `a ∈ A` iff some such certificate is accepted. -/
def IsVerifier (enc : α ↪ List Bool) (p : Polynomial ℕ) (V : α × List Bool → Bool) (A : Set α) :
    Prop :=
  ∀ a, a ∈ A ↔ ∃ w : List Bool, w.length = p.eval (enc a).length ∧ V (a, w) = true

/-- The problems with polynomial-time verifiers and polynomially long certificates, with respect to
the encoding `enc` of instances. -/
def NP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧ IsVerifier enc p V A}

theorem mem_NP {enc : α ↪ List Bool} {A : Set α} :
    A ∈ NP enc ↔ ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧ IsVerifier enc p V A :=
  Iff.rfl

/-- The problems whose complements are in `NP`. -/
def coNP (enc : α ↪ List Bool) : Set (Set α) := {A | Aᶜ ∈ NP enc}

theorem mem_coNP {enc : α ↪ List Bool} {A : Set α} : A ∈ coNP enc ↔ Aᶜ ∈ NP enc := Iff.rfl

theorem coNP_eq_preimage_compl_NP (enc : α ↪ List Bool) : coNP enc = compl ⁻¹' NP enc := rfl

end Cslib.Complexity
