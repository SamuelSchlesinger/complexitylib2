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

* `Cslib.Circuits.Boolean.DepthClass`: the languages decided by circuits over a basis of
  polynomially bounded size and depth `O(D n)`.
* `Cslib.Circuits.Boolean.ConstDepth`: the case of constant depth.

## Main results

* `Cslib.Circuits.Boolean.DepthClass.mono`: a map of bases keeping the meaning of operations
  embeds the classes.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

variable {σ τ : Signature}

/-- The languages over `Bool` decided, at every input length `n`, by circuits over the basis `I` of
polynomially bounded size and depth at most `c * D n` for a constant `c`. -/
def DepthClass (I : Interpretation σ Bool) (D : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (s : ℕ → ℕ), PolynomiallyBounded s ∧ ∀ n,
    ∃ C : Circuit σ n 1, C.Computes I (single (L.slice n)) ∧ C.depth ≤ c * D n ∧ C.size ≤ s n}

namespace DepthClass

variable {I : Interpretation σ Bool} {D D' : ℕ → ℕ}

/-- **A map of bases keeping the meaning of every operation embeds the classes**: translate the
circuits gate by gate. -/
theorem mono (φ : σ.Hom τ) {J : Interpretation τ Bool} [φ.Preserves I J] :
    DepthClass I D ⊆ DepthClass J D := by
  rintro L ⟨c, s, hs, hC⟩
  refine ⟨c, s, hs, fun n => ?_⟩
  obtain ⟨C, hCc, hCd, hCs⟩ := hC n
  exact ⟨C.mapOp φ, hCc.mapOp, by simpa using hCd, by simpa using hCs⟩

/-- A larger depth envelope gives a larger class. -/
theorem mono_depth (h : ∀ n, D n ≤ D' n) : DepthClass I D ⊆ DepthClass I D' := by
  rintro L ⟨c, s, hs, hC⟩
  refine ⟨c, s, hs, fun n => ?_⟩
  obtain ⟨C, hCc, hCd, hCs⟩ := hC n
  exact ⟨C, hCc, hCd.trans (Nat.mul_le_mul_left _ (h n)), hCs⟩

end DepthClass

/-- The languages over `Bool` decided, at every input length, by circuits over the basis `I` of
polynomially bounded size and constant depth. -/
def ConstDepth (I : Interpretation σ Bool) : Set (Language Bool) :=
  DepthClass I fun _ => 1

namespace ConstDepth

variable {I : Interpretation σ Bool} {L : Language Bool}

/-- Membership in `ConstDepth I`: a depth bound and a polynomial size bound, and circuits for every
slice within them. -/
theorem mem_iff : L ∈ ConstDepth I ↔ ∃ (d : ℕ) (s : ℕ → ℕ), PolynomiallyBounded s ∧ ∀ n,
    ∃ C : Circuit σ n 1, C.Computes I (single (L.slice n)) ∧ C.depth ≤ d ∧ C.size ≤ s n := by
  simp only [ConstDepth, DepthClass, Set.mem_ofPred_eq, mul_one]

/-- **A map of bases keeping the meaning of every operation embeds the classes.** -/
theorem mono (φ : σ.Hom τ) {J : Interpretation τ Bool} [φ.Preserves I J] :
    ConstDepth I ⊆ ConstDepth J :=
  DepthClass.mono φ

end ConstDepth

end Cslib.Circuits.Boolean
