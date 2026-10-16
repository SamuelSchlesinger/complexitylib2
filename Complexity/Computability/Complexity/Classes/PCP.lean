/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat

/-!
# The classes PCP(r, q)

A probabilistically checkable proof system for a problem `A` [Arora and Safra][AroraSafra1998],
[Arora and Barak, Chapter 11][AroraBarak09] is a verifier that, on an instance `a`, reads a random
string `ρ`, computes from `a` and `ρ` a list of positions in a proof `π`, reads the bits of `π` at
those positions, and accepts or rejects. Every member of `A` has a proof that is accepted for every
random string (completeness), and for a non-member every proof is rejected for at least half of the
random strings (soundness).

A verifier (`PCPVerifier`) is a pair of functions: the positions it queries, and its verdict on
the instance, the random string and the bits read. It is nonadaptive, as in Arora and Barak: the
positions depend on the instance and the random string, not on the bits read. A proof is a finite
string, and a position past its end reads as `false`. The verifier is polynomial-time
(`PCPVerifier.PolyTime`) when both functions are computable in polynomial time, the positions as
lists of binary numbers. Time is measured in the length of the whole input of each function, which
includes the random string; when `r` is bounded by a polynomial, as for all the usual classes, this
is time polynomial in the length of the encoded instance.

`PCP r q enc` follows Arora and Barak in allowing constant factors: a problem is in it when, for
some constants `c` and `d`, a polynomial-time verifier uses `c * r n` random bits and at most
`d * q n` queries on instances whose encoding has length `n`. The verifier receives exactly
`c * r n` random bits, so it can see `r n`; for the class to be meaningful, `r` should be
computable in polynomial time (in unary), as the usual bounds are.

The PCP theorem, `NP = PCP(log n, 1)`, is not proved here; the finite combinatorial parts of
Dinur's proof are in `Cslib.PCP`.

## Main definitions

* `Cslib.Complexity.PCPVerifier`, with `PCPVerifier.Accepts` and `PCPVerifier.PolyTime`.
* `Cslib.Complexity.IsPCPVerifier`: completeness, soundness and the bound on queries.
* `Cslib.Complexity.PCP`.

## Main results

* `Cslib.Complexity.PCP_mono_queries`: more queries give a larger class.

## References

* [S. Arora, S. Safra, *Probabilistic checking of proofs*][AroraSafra1998]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

/-- A nonadaptive verifier of probabilistically checkable proofs for instances of type `α`. -/
structure PCPVerifier (α : Type) where
  /-- The positions of the proof read on an instance and a random string. -/
  queries : α × List Bool → List ℕ
  /-- The verdict on an instance, a random string, and the bits read at the queried positions. -/
  verdict : (α × List Bool) × List Bool → Bool

namespace PCPVerifier

/-- The bits of the proof `π` at the positions `is`; a position past the end of `π` reads as
`false`. -/
def answers (π : List Bool) (is : List ℕ) : List Bool := is.map fun i => π.getD i false

/-- The verdict of `V` on the instance `a` with the proof `π` and the random string `ρ`. -/
def Accepts (V : PCPVerifier α) (a : α) (π ρ : List Bool) : Bool :=
  V.verdict ((a, ρ), answers π (V.queries (a, ρ)))

/-- A verifier is polynomial-time, with respect to the encoding `enc` of instances, when its
queries and its verdict are computable in polynomial time, the queries as lists of binary
numbers. -/
def PolyTime (enc : α ↪ List Bool) (V : PCPVerifier α) : Prop :=
  ComputableTidilyInPolyTime V.queries (encPair enc encBits) (encList encNat) ∧
    ComputableTidilyInPolyTime V.verdict (encPair (encPair enc encBits) encBits) encBool

end PCPVerifier

/-- `V` is a verifier for `A` using `r n` random bits and at most `q n` queries on instances whose
encoding has length `n`: every member of `A` has a proof that is accepted for every random string,
and for every non-member, every proof is accepted for at most half of the random strings. -/
def IsPCPVerifier (enc : α ↪ List Bool) (r q : ℕ → ℕ) (V : PCPVerifier α) (A : Set α) : Prop :=
  (∀ a (ρ : List Bool), ρ.length = r (enc a).length →
      (V.queries (a, ρ)).length ≤ q (enc a).length) ∧
    (∀ a ∈ A, ∃ π : List Bool, ∀ ρ : List Bool, ρ.length = r (enc a).length →
      V.Accepts a π ρ = true) ∧
    ∀ a ∉ A, ∀ π : List Bool,
      2 * acceptCount (fun x => V.Accepts x.1 π x.2) a (r (enc a).length) ≤ 2 ^ r (enc a).length

/-- The class `PCP(r, q)` with respect to the encoding `enc` of instances: the problems with a
polynomial-time verifier using `O(r n)` random bits and `O(q n)` queries on instances whose
encoding has length `n`. -/
def PCP (r q : ℕ → ℕ) (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (V : PCPVerifier α) (c d : ℕ), V.PolyTime enc ∧
    IsPCPVerifier enc (fun n => c * r n) (fun n => d * q n) V A}

variable {enc : α ↪ List Bool}

theorem mem_PCP {r q : ℕ → ℕ} {A : Set α} : A ∈ PCP r q enc ↔
    ∃ (V : PCPVerifier α) (c d : ℕ), V.PolyTime enc ∧
      IsPCPVerifier enc (fun n => c * r n) (fun n => d * q n) V A :=
  Iff.rfl

theorem IsPCPVerifier.mono_queries {r q q' : ℕ → ℕ} {V : PCPVerifier α} {A : Set α}
    (hq : ∀ n, q n ≤ q' n) (h : IsPCPVerifier enc r q V A) : IsPCPVerifier enc r q' V A :=
  ⟨fun a ρ hρ => (h.1 a ρ hρ).trans (hq _), h.2⟩

/-- More queries give a larger class. (The class is not monotone in `r` in this generality: the
verifier receives exactly `c * r n` random bits.) -/
theorem PCP_mono_queries {r q q' : ℕ → ℕ} (hq : ∀ n, q n ≤ q' n) : PCP r q enc ⊆ PCP r q' enc :=
  fun _ ⟨V, c, d, hV, h⟩ => ⟨V, c, d, hV, h.mono_queries fun n => Nat.mul_le_mul_left d (hq n)⟩

end Cslib.Complexity
