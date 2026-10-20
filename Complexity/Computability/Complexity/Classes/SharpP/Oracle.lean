/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle.Closure
public import Complexity.Computability.Complexity.Classes.SharpP.Combinators
import Complexity.Computability.Complexity.Classes.Oracle.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Counting functions relative to a language oracle

`SharpPWithOracle A enc` counts accepted Boolean witnesses of a fixed polynomial length using
`ComputableInPolyTimeWithOracle A`. Its deterministic word-query program is fixed before the
witness and oracle replies. The certificate realizes that program under one polynomial clock
against every stateful word oracle, charging query construction and reply access. Correctness
of the Boolean verifier is required against the fixed, stateless `languageOracle A`.

`GapPWithOracle` consists of differences of two such counts. These definitions reuse the ordinary
verifier counting semantics; equivalence with nondeterministic oracle-machine counting is not
claimed. Ignoring an oracle embeds the ordinary classes, and the existing certified simulation
eliminates every polynomial-time decidable oracle. Oracle lowness for other classes is separate.

## Main definitions

* `Cslib.Complexity.SharpPWithOracle`: fixed-length counting with an oracle verifier.
* `Cslib.Complexity.GapPWithOracle`: differences of relativized counting functions.

## Main results

* `Cslib.Complexity.SharpP_subset_SharpPWithOracle`,
  `Cslib.Complexity.GapP_subset_GapPWithOracle`: ignore the oracle.
* `Cslib.Complexity.SharpPWithOracle_eq_SharpP`,
  `Cslib.Complexity.GapPWithOracle_eq_GapP`: eliminate an oracle in P.
* `Cslib.Complexity.computableInPolyTimeWithOracle_andVerifier`,
  `Cslib.Complexity.computableInPolyTimeWithOracle_selectVerifier`: reuse verifier combinators.

## References

* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994].
* [L. Fortnow, *Counting Complexity*][Fortnow1997], Lemma 3.6.
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 3.4.
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set (List Bool)}

/-- Count witnesses of exactly `p(|enc a|)` bits with a strict polynomial-time oracle verifier.
The oracle is fixed for correctness; its resource certificate applies to arbitrary replies. -/
def SharpPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (α → ℕ) :=
  {f | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTimeWithOracle A V (encPair enc encBits) encBool ∧
      ∀ a, f a = acceptCount V a (p.eval (enc a).length)}

/-- Integer differences of two counting functions relative to the same language oracle. -/
def GapPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (α → ℤ) :=
  {g | ∃ f₁ ∈ SharpPWithOracle A enc, ∃ f₂ ∈ SharpPWithOracle A enc,
    ∀ a, g a = (f₁ a : ℤ) - f₂ a}

/-- Ordinary counting verifiers can ignore every oracle. -/
theorem SharpP_subset_SharpPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    SharpP enc ⊆ SharpPWithOracle A enc := fun _ ⟨p, V, hV, hf⟩ =>
  ⟨p, V, hV.computableInPolyTimeWithOracle A, hf⟩

/-- Ordinary gap functions can ignore every oracle. -/
theorem GapP_subset_GapPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    GapP enc ⊆ GapPWithOracle A enc := fun _ ⟨f₁, h₁, f₂, h₂, hg⟩ =>
  ⟨f₁, SharpP_subset_SharpPWithOracle A enc h₁,
    f₂, SharpP_subset_SharpPWithOracle A enc h₂, hg⟩

/-- A polynomial-time oracle adds no counting functions. -/
theorem SharpPWithOracle_eq_SharpP (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    SharpPWithOracle A enc = SharpP enc :=
  Set.Subset.antisymm (fun _ ⟨p, V, hV, hf⟩ =>
    ⟨p, V, hV.computableTidilyInPolyTime hA, hf⟩) (SharpP_subset_SharpPWithOracle A enc)

/-- A polynomial-time oracle adds no gap functions. -/
theorem GapPWithOracle_eq_GapP (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    GapPWithOracle A enc = GapP enc := by
  simp only [GapPWithOracle, SharpPWithOracle_eq_SharpP hA, GapP]

/-- Oracle verifiers can run on disjoint parts of a witness and conjoin their results. -/
theorem computableInPolyTimeWithOracle_andVerifier {k : α → ℕ}
    {V₁ V₂ : α × List Bool → Bool} (hk : ComputableTidilyInPolyTime k enc encUnary)
    (h₁ : ComputableInPolyTimeWithOracle A V₁ (encPair enc encBits) encBool)
    (h₂ : ComputableInPolyTimeWithOracle A V₂ (encPair enc encBits) encBool) :
    ComputableInPolyTimeWithOracle A (andVerifier k V₁ V₂) (encPair enc encBits) encBool := by
  unfold andVerifier
  exact ((h₁.preprocess (input := encPair enc encBits)
      (g := fun x : α × List Bool => (x.1, x.2.take (k x.1))) (by fun_prop)).prod
    (h₂.preprocess (input := encPair enc encBits)
      (g := fun x : α × List Bool => (x.1, x.2.drop (k x.1))) (by fun_prop))).map
      (g := fun b => b.1 && b.2) (output := encBool) (by fun_prop)

/-- The first witness bit selects between two oracle verifier results. Both certified programs
may be run sequentially, so the resource bound remains valid for arbitrary stateful replies. -/
theorem computableInPolyTimeWithOracle_selectVerifier {V₀ V₁ : α × List Bool → Bool}
    (h₀ : ComputableInPolyTimeWithOracle A V₀ (encPair enc encBits) encBool)
    (h₁ : ComputableInPolyTimeWithOracle A V₁ (encPair enc encBits) encBool) :
    ComputableInPolyTimeWithOracle A (selectVerifier V₀ V₁) (encPair enc encBits) encBool := by
  unfold selectVerifier
  exact (((h₀.prod h₁).preprocess (input := encPair enc encBits)
      (g := fun x : α × List Bool => (x.1, x.2.tail)))
    (by fun_prop)).map_with (g := fun x b => if x.2.headD false then b.2 else b.1)
      (output := encBool) (by fun_prop)

end Cslib.Complexity
