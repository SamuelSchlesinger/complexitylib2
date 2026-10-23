/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.PCPBridge

/-! # The PCP theorem

For every problem with certificates checkable in polynomial time, proofs can be presented so that
verification reads only constantly many bits. The verifier chooses those positions using only
logarithmically many random bits. A correct instance has a proof accepted for every random choice;
for an incorrect instance, every purported proof is rejected with probability at least one half.
Dinur's construction repeatedly magnifies the fraction of violated constraints while returning
to a fixed alphabet, so a constant number of local checks can detect global inconsistency.

Queries are nonadaptive: their positions are chosen before any proof bits are read. Native
machine bounds charge the complete construction, the binary query addresses and verification.
The construction is asymptotically polynomial, with enormous fixed constants.

Lean checks the bridge to the complete construction, and `#check_abstract` audits the public
statement's dependency boundary.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

namespace ComplexityTests.Abstracts.PCPAbstract

/-- Frame each bit as `[true, b]` and terminate the word with `[false]`. -/
def frame (w : List Bool) : List Bool := w.flatMap (fun b => [true, b]) ++ [false]

/-- Encode a pair by framing its first component and appending its second component. -/
def encodePair {α β : Type} (a : α → List Bool) (b : β → List Bool) (p : α × β) :
    List Bool := frame (a p.1) ++ b p.2

/-- Encode a list by concatenating its framed elements. -/
def encodeList {α : Type} (enc : α → List Bool) (l : List α) : List Bool :=
  l.flatMap (frame ∘ enc)

theorem encodePair_injective {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) :
    Function.Injective (encodePair a b) := PCPBridge.encodePair_injective a b

theorem encodeList_injective {α : Type} (enc : α ↪ List Bool) :
    Function.Injective (encodeList enc) := PCPBridge.encodeList_injective enc

theorem bits_injective : Function.Injective Nat.bits := PCPBridge.bits_injective

/-- Natural numbers are encoded by their canonical little-endian binary digits. -/
def encNat : ℕ ↪ List Bool := ⟨Nat.bits, bits_injective⟩

/-- Pair encoding; `↪` records injectivity. -/
def encPair {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) : α × β ↪ List Bool :=
  ⟨encodePair a b, encodePair_injective a b⟩

/-- List encoding. -/
def encList {α : Type} (enc : α ↪ List Bool) : List α ↪ List Bool :=
  ⟨encodeList enc, encodeList_injective enc⟩

/-- A Boolean is encoded by a single bit. -/
def encBool : Bool ↪ List Bool := ⟨fun b => [b], by intro a b h; injection h⟩

/-- Bitstrings encode themselves. -/
def encBits : List Bool ↪ List Bool := Function.Embedding.refl _

/-- A single finite-state binary multi-tape machine computes `f` on every encoded input,
within polynomial time and work space. Inputs are read-only; outputs are write-only.
`Cslib.PolynomiallyBounded` means bounded above by some polynomial. -/
def ComputableInPolyTime {α β : Type} (f : α → β)
    (a : α ↪ List Bool) (b : β ↪ List Bool) : Prop :=
  ∃ t s : ℕ → ℕ, Cslib.PolynomiallyBounded t ∧ Cslib.PolynomiallyBounded s ∧
    Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength f a b t s

/-- NP consists of problems with a polynomial-time deterministic verifier and binary
certificates of an exact polynomial length. The verifier halts on every input pair. -/
def NP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
    ∀ a, a ∈ A ↔ ∃ w : List Bool, w.length = p.eval (enc a).length ∧ V (a, w) = true}

/-- Read a finite proof at the queried addresses. Positions beyond its end read as false. -/
def proofAnswers (proof : List Bool) (positions : List ℕ) : List Bool :=
  positions.map (fun i => proof.getD i false)

/-- The number of `n`-bit random strings on which the verifier accepts a fixed proof. -/
def acceptCount {α : Type} (queries : α × List Bool → List ℕ)
    (verdict : (α × List Bool) × List Bool → Bool) (a : α) (proof : List Bool) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun r : Fin n → Bool =>
    verdict ((a, List.ofFn r), proofAnswers proof (queries (a, List.ofFn r))) = true).card

/-- Nonadaptive probabilistically checkable proofs: one fixed polynomial-time algorithm
computes the number of random bits, the list of binary proof addresses and the final verdict.
For constants `c,d`, it uses at most `c*r(n)` random bits and `d*q(n)` queries. A yes-instance
has a finite proof accepted for every random string; on a no-instance every finite proof is
accepted on at most half of the random strings. -/
def PCP {α : Type} (r q : ℕ → ℕ) (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (coins : α → ℕ) (queries : α × List Bool → List ℕ)
      (verdict : (α × List Bool) × List Bool → Bool) (c d : ℕ),
    ComputableInPolyTime coins enc encNat ∧
    ComputableInPolyTime queries (encPair enc encBits) (encList encNat) ∧
    ComputableInPolyTime verdict (encPair (encPair enc encBits) encBits) encBool ∧
    (∀ a, coins a ≤ c * r (enc a).length) ∧
    (∀ a ρ, ρ.length = coins a → (queries (a, ρ)).length ≤ d * q (enc a).length) ∧
    (∀ a ∈ A, ∃ proof : List Bool, ∀ ρ, ρ.length = coins a →
      verdict ((a, ρ), proofAnswers proof (queries (a, ρ))) = true) ∧
    ∀ a ∉ A, ∀ proof, 2 * acceptCount queries verdict a proof (coins a) ≤ 2 ^ coins a}

/-- NP equals logarithmic-randomness, constant-query PCP, with perfect completeness and
soundness at most one half. Queries are nonadaptive; their binary addresses and all computation
are charged, including the full gap-graph construction. -/
theorem pcp_theorem {α : Type} (enc : α ↪ List Bool) :
    NP enc = PCP (fun n => Nat.log 2 n + 1) (fun _ => 1) enc := PCPBridge.pcp_theorem enc

/--
info: abstract audit passed for `ComplexityTests.Abstracts.PCPAbstract`:
18 root declarations, 83 dependencies checked
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.PCPAbstract

end ComplexityTests.Abstracts.PCPAbstract
