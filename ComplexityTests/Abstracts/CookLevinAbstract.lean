/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract tests)

import ComplexityTests.Abstracts.Check
import ComplexityTests.Abstracts.CookLevinBridge

/-! # Cook–Levin: satisfiability captures efficient verification

A proposed satisfying truth assignment is easy to check. Cook–Levin says that every problem
with short, efficiently checkable witnesses can be
translated into satisfiability in polynomial time. The translation describes a verifier's
computation by Boolean constraints: a satisfying assignment records an accepting computation.
Thus SAT is NP-complete, and its complement UNSAT is coNP-complete.

The definitions below specify CNF formulas, their binary encoding, total polynomial-time
reductions and native finite-state machine bounds. The claims are about asymptotic complexity,
not a fast practical SAT solver. Lean checks the bridge proofs; `#check_abstract` checks that the
statements use only the definitions here and upstream mathematical and machine foundations.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 2.3.
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94], Theorem 8.2.
-/

namespace ComplexityTests.Abstracts.CookLevinAbstract

/-! ## Propositional CNF formulas and satisfiability

A literal `(v, b)` pairs a natural-number variable index `v : ℕ` with a Boolean
polarity `b : Bool`. A clause is a finite list of literals interpreted as a
disjunction, and a CNF formula is a finite list of clauses interpreted as a
conjunction. Lists are used for finite collections so that algorithms can
process them directly; duplicate literals or clauses do not affect truth values.
-/

/-- A literal `(v, b)`: variable `v` with polarity `b` (`true` for `v`, `false` for `¬v`). -/
abbrev Literal := ℕ × Bool

/-- A clause: the disjunction of its literals. -/
abbrev Clause := List Literal

/-- A CNF formula: the conjunction of its clauses. -/
abbrev Formula := List Clause

/-- A truth assignment `τ : ℕ → Bool` satisfies a CNF formula `φ` if every
clause `c ∈ φ` contains at least one literal `(v, b) ∈ c` with `τ v = b`. -/
def Satisfiable (φ : Formula) : Prop :=
  ∃ τ : ℕ → Bool, ∀ c ∈ φ, ∃ l ∈ c, τ l.1 = l.2

/-- SAT is the set of satisfiable CNF formulas. -/
def SAT : Set Formula := {φ | Satisfiable φ}

/-- UNSAT is the set of unsatisfiable CNF formulas. Because instances are
formulas rather than raw bitstrings, UNSAT is the exact set-theoretic
complement of SAT. -/
def UNSAT : Set Formula := {φ | ¬ Satisfiable φ}

/-- ExactThreeSAT is the set of satisfiable CNF formulas in which every clause
has length 3 (repeated literals within a clause are permitted). -/
def ExactThreeSAT : Set Formula :=
  {φ | (∀ c ∈ φ, c.length = 3) ∧ Satisfiable φ}

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

/-- Encode a CNF formula as a list of clauses, each a list of literals `(v, b)` encoded as the
pair of `Nat.bits v` and the one-bit word `[b]`. -/
def encodeCNF : Formula → List Bool :=
  encodeList (encodeList (encodePair Nat.bits (fun b => [b])))

theorem encodePair_injective {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool) :
    Function.Injective (encodePair encA encB) :=
  CookLevinBridge.encodePair_injective encA encB

theorem encodeCNF_injective : Function.Injective encodeCNF :=
  CookLevinBridge.encodeCNF_injective

/-- Injective encoding of bitstrings as themselves. -/
def encBits : List Bool ↪ List Bool := Function.Embedding.refl _

/-- Injective encoding of a single Boolean as a one-bit word `[b]`. -/
def encBool : Bool ↪ List Bool :=
  ⟨fun b => [b], by intro a b h; injection h⟩

/-- Injective framed encoding of pairs. -/
def encPair {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool) : α × β ↪ List Bool :=
  ⟨encodePair encA encB, encodePair_injective encA encB⟩

/-- Injective framed binary encoding of CNF formulas. -/
def encCNF : Formula ↪ List Bool :=
  ⟨encodeCNF, encodeCNF_injective⟩

/-! ## Polynomial-time computability, NP, coNP, and completeness

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

/-- The class coNP consists of decision problems whose complements belong to NP. -/
def coNP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | Aᶜ ∈ NP enc}

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

/-- A problem `B` is coNP-complete if it belongs to coNP and every coNP problem
reduces to `B` in polynomial time. -/
def coNPComplete {β : Type} (encB : β ↪ List Bool) (B : Set β) : Prop :=
  B ∈ coNP encB ∧
  ∀ (α : Type) (encA : α ↪ List Bool) (A : Set α),
    A ∈ coNP encA → PolyTimeReducible encA encB A B

/-! ## Main results -/

/-- **Theorem (Cook–Levin):** SAT is NP-complete under polynomial-time many-one
reductions. -/
theorem sat_npComplete : NPComplete encCNF SAT :=
  CookLevinBridge.sat_npComplete

/-- **Corollary:** UNSAT is coNP-complete under polynomial-time many-one
reductions. -/
theorem unsat_coNPComplete : coNPComplete encCNF UNSAT :=
  CookLevinBridge.unsat_coNPComplete

/-- **Theorem (3SAT with exact clause width 3):** Satisfiability of CNF formulas
whose clauses each have 3 literal occurrences (permitting repeated literals) is
NP-complete under polynomial-time many-one reductions. -/
theorem exactThreeSAT_npComplete : NPComplete encCNF ExactThreeSAT :=
  CookLevinBridge.exactThreeSAT_npComplete

/--
info: abstract audit passed for `ComplexityTests.Abstracts.CookLevinAbstract`: 28 root
declarations, 68 dependencies checked
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.CookLevinAbstract

end ComplexityTests.Abstracts.CookLevinAbstract
