/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.MapOp
public import Cslib.Computability.Languages.Slice
public import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Constant-depth circuit classes

`ConstDepth I` is the class of languages decided, at every input length, by circuits over the
Boolean basis `I` of polynomially bounded size and constant depth. AC⁰
[Arora and Barak, Section 6.7.1][AroraBarak09], AC⁰[q] [Arora and Barak, Section 14.2][AroraBarak09]
and TC⁰ [Vollmer, Chapter 4][Vollmer1999] are this class for their bases. A map of bases that keeps
the meaning of every operation embeds the classes (`ConstDepth.mono`).

The depth of a circuit counts every gate on a path, and its size counts every gate (cslib's
`Circuit.depth` and `Circuit.size`); for a constant-depth class with polynomial size, the
convention does not matter.

## Main definitions

* `Cslib.Circuits.Boolean.ConstDepth`: the languages decided by circuits over a basis of
  polynomially bounded size and constant depth.

## Main results

* `Cslib.Circuits.Boolean.ConstDepth.mono`: a map of bases keeping the meaning of operations
  embeds the classes.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

variable {σ τ : Signature}

/-- The languages over `Bool` decided, at every input length, by circuits over the basis `I` of
polynomially bounded size and constant depth. -/
def ConstDepth (I : Interpretation σ Bool) : Set (Language Bool) :=
  {L | ∃ (d : ℕ) (s : ℕ → ℕ), PolynomiallyBounded s ∧ ∀ n,
    ∃ C : Circuit σ n 1, C.Computes I (single (L.slice n)) ∧ C.depth ≤ d ∧ C.size ≤ s n}

namespace ConstDepth

variable {I : Interpretation σ Bool} {L : Language Bool}

/-- Membership in `ConstDepth I`: a depth bound and a polynomial size bound, and circuits for every
slice within them. -/
theorem mem_iff : L ∈ ConstDepth I ↔ ∃ (d : ℕ) (s : ℕ → ℕ), PolynomiallyBounded s ∧ ∀ n,
    ∃ C : Circuit σ n 1, C.Computes I (single (L.slice n)) ∧ C.depth ≤ d ∧ C.size ≤ s n :=
  Iff.rfl

/-- **A map of bases keeping the meaning of every operation embeds the classes**: translate the
circuits gate by gate. -/
theorem mono (φ : σ.Hom τ) {J : Interpretation τ Bool} [φ.Preserves I J] :
    ConstDepth I ⊆ ConstDepth J := by
  rintro L ⟨d, s, hs, hC⟩
  refine ⟨d, s, hs, fun n => ?_⟩
  obtain ⟨C, hCc, hCd, hCs⟩ := hC n
  exact ⟨C.mapOp φ, hCc.mapOp, by simpa using hCd, by simpa using hCs⟩

end ConstDepth

end Cslib.Circuits.Boolean
