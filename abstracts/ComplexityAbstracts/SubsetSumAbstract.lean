/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.SubsetSumBridge

/-! # A formal abstract of Subset Sum NP-completeness

This file defines the Subset Sum decision problem on finite lists of natural numbers, its binary
encoding, polynomial-time verifiers, the class NP and polynomial-time many-one reductions, and
proves that Subset Sum is NP-complete when numbers are written in binary.

To check that the formalization establishes this result, a reader only needs to inspect the
definitions and theorem statements in this file. Every public definition and theorem statement
depends only on this file, `Mathlib`, and upstream `Cslib`'s multi-tape Turing machine model;
`#check_abstract` mechanically verifies that no internal `Complexitylib` declarations leak into the
statements, and Lean checks the proofs through `SubsetSumBridge`.

## References

* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

namespace ComplexityTests.Abstracts.SubsetSumAbstract

/-! ## Subset Sum -/

/-- An instance `(numbers, target) : List ℕ × ℕ` belongs to `SubsetSum` if some
subsequence (`List.Sublist`) of `numbers` sums to `target`. Using lists rather
than sets allows repeated numbers in the input; each occurrence may be chosen at
most once. -/
def SubsetSum : Set (List ℕ × ℕ) :=
  {x | ∃ s : List ℕ, s.Sublist x.1 ∧ s.sum = x.2}

/-! ## Binary encoding convention

Values are encoded injectively as bitstrings (`List Bool`). A bitstring `w` is
framed by encoding each bit `b` as `[true, b]` and appending `[false]`, making
framed bitstrings self-delimiting under concatenation. Pairs frame the first
component before appending the second, and lists concatenate the framed
encodings of their elements. Natural numbers use Mathlib's canonical
little-endian binary digits `Nat.bits` (`0 ↦ []`, positive `n` with least
significant bit first and final bit `true`).
-/

/-- Frame a bitstring: write each bit `b` as `[true, b]`, then terminate with `[false]`. -/
def frame (w : List Bool) : List Bool :=
  w.flatMap (fun b => [true, b]) ++ [false]

/-- Encode a pair by framing the encoding of its first component and appending the encoding of
its second component. -/
def encodePair {α β : Type} (encA : α → List Bool) (encB : β → List Bool) (p : α × β) :
    List Bool :=
  frame (encA p.1) ++ encB p.2

/-- Encode a list by concatenating the framed encodings of its elements. -/
def encodeList {α : Type} (enc : α → List Bool) (l : List α) : List Bool :=
  l.flatMap (frame ∘ enc)

theorem encodePair_injective {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool) :
    Function.Injective (encodePair encA encB) :=
  CookLevinBridge.encodePair_injective encA encB

theorem encodeList_injective {α : Type} (enc : α ↪ List Bool) :
    Function.Injective (encodeList enc) :=
  SubsetSumBridge.encodeList_injective enc

theorem bits_injective : Function.Injective Nat.bits :=
  SubsetSumBridge.bits_injective

/-- Injective binary encoding of natural numbers by `Nat.bits`. -/
def encNat : ℕ ↪ List Bool :=
  ⟨Nat.bits, bits_injective⟩

/-- Injective framed encoding of lists. -/
def encList {α : Type} (enc : α ↪ List Bool) : List α ↪ List Bool :=
  ⟨encodeList enc, encodeList_injective enc⟩

/-- Injective framed encoding of pairs. -/
def encPair {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool) : α × β ↪ List Bool :=
  ⟨encodePair encA encB, encodePair_injective encA encB⟩

/-- Injective encoding of bitstrings as themselves. -/
def encBits : List Bool ↪ List Bool := Function.Embedding.refl _

/-- Injective encoding of a single Boolean as a one-bit word `[b]`. -/
def encBool : Bool ↪ List Bool :=
  ⟨fun b => [b], by intro a b h; injection h⟩

/-- Injective binary encoding of Subset Sum instances: the list of numbers, then the target. -/
def encSubsetSum : List ℕ × ℕ ↪ List Bool :=
  encPair (encList encNat) encNat

/-! ## Polynomial-time computability, NP, and NP-completeness

In upstream `Cslib`, `Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength f encA encB t s`
means that there exists a deterministic multi-tape Turing machine with a binary
tape alphabet and finitely many states that halts on every encoded input
`encA a` within `t (encA a).length` steps and `s (encA a).length` work-tape
cells, leaving `encB (f a)` on its output tape. `Cslib.PolynomiallyBounded`
asserts that a growth bound `ℕ → ℕ` is bounded above by a polynomial.
-/

/-- A total function `f : α → β` is computable in polynomial time with respect
to input encoding `encA` and output encoding `encB` if some deterministic
multi-tape binary Turing machine computes it within polynomially bounded time
and space in the input bit length. -/
def ComputableInPolyTime {α β : Type} (f : α → β)
    (encA : α ↪ List Bool) (encB : β ↪ List Bool) : Prop :=
  ∃ t s : ℕ → ℕ, Cslib.PolynomiallyBounded t ∧ Cslib.PolynomiallyBounded s ∧
    Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength f encA encB t s

/-- A function `V : α × List Bool → Bool` verifies a decision problem `A` with
certificate length polynomial `p` if an instance `a` belongs to `A` exactly
when there is a binary certificate `w` of length `p(|enc a|)` accepted by `V`. -/
def IsVerifier {α : Type} (enc : α ↪ List Bool) (p : Polynomial ℕ)
    (V : α × List Bool → Bool) (A : Set α) : Prop :=
  ∀ a, a ∈ A ↔ ∃ w : List Bool, w.length = p.eval (enc a).length ∧ V (a, w) = true

/-- The class NP with respect to instance encoding `enc` consists of decision
problems that have a polynomial-time verifier with polynomially long binary
certificates. -/
def NP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧ IsVerifier enc p V A}

/-- Problem `A` (with encoding `encA`) many-one reduces in polynomial time to
problem `B` (with encoding `encB`) if a polynomial-time computable map `f`
preserves yes/no membership on every instance. -/
def PolyTimeReducible {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (A : Set α) (B : Set β) : Prop :=
  ∃ f : α → β, ComputableInPolyTime f encA encB ∧ ∀ a, a ∈ A ↔ f a ∈ B

/-- A problem `B` is NP-complete if it belongs to NP and every NP problem (over
any instance type `α` and injective binary encoding `encA`) reduces to `B` in
polynomial time. -/
def NPComplete {β : Type} (encB : β ↪ List Bool) (B : Set β) : Prop :=
  B ∈ NP encB ∧
  ∀ (α : Type) (encA : α ↪ List Bool) (A : Set α),
    A ∈ NP encA → PolyTimeReducible encA encB A B

/-! ## Main result -/

/-- **Theorem (Karp):** Subset Sum is NP-complete under polynomial-time many-one
reductions when the input list and target sum are encoded in binary. -/
theorem subsetSum_npComplete : NPComplete encSubsetSum SubsetSum :=
  SubsetSumBridge.subsetSum_npComplete

/--
info: abstract audit passed for `ComplexityTests.Abstracts.SubsetSumAbstract`: 20 root
declarations, 61 dependencies checked
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.SubsetSumAbstract

end ComplexityTests.Abstracts.SubsetSumAbstract
