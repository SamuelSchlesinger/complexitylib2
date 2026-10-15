/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.BranchingProgram.MonoidProgram
public import Cslib.Computability.Languages.Slice
public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Mathlib.Data.Set.Image

/-!
# Languages of polynomial-length programs over a monoid

A program over a monoid `M` *decides* a Boolean function `f` with an accepting set `S` of elements
of `M` when `f` is true exactly on the inputs where the value of the program lies in `S`
(`MonoidProgram.Decides`) [BarringtonTherien1988]. `PolyLength M` is the class of languages over
`Bool` decided, at every input length, by programs over `M` of polynomially bounded length. Over
`Equiv.Perm (Fin w)` these are the languages of polynomial-length permutation branching programs
of width `w`, and over `Function.End (Fin w)` those of polynomial-length branching programs of
width `w` [Barrington1989]. Like the circuit classes, `PolyLength M` is nonuniform.

A program that `σ`-computes `f`, with `σ ≠ 1`, decides `f` with the accepting set `{σ}`
(`MonoidProgram.Computes.decides`), and an injective homomorphism of monoids embeds the classes
(`PolyLength.subset_of_injective`).

## Main definitions

* `Cslib.BranchingPrograms.MonoidProgram.Decides`: deciding a function with an accepting set.
* `Cslib.BranchingPrograms.PolyLength`: the languages of polynomial-length programs over a monoid.

## Main results

* `Cslib.BranchingPrograms.MonoidProgram.Computes.decides`: `σ`-computing is deciding.
* `Cslib.BranchingPrograms.PolyLength.subset_of_injective`: an injective homomorphism of monoids
  embeds the classes.

## References

* [D. A. Barrington, *Bounded-width polynomial-size branching programs recognize exactly those
  languages in NC¹*][Barrington1989]
* [D. A. Mix Barrington, D. Thérien, *Finite monoids and the fine structure of
  NC¹*][BarringtonTherien1988]
-/

@[expose] public section

namespace Cslib.BranchingPrograms

variable {n : ℕ} {M N : Type*} [Monoid M] [Monoid N]

/-- A program decides `f` with the accepting set `S` when `f` is true exactly on the inputs where
the value of the program lies in `S`. -/
def MonoidProgram.Decides (P : MonoidProgram n M) (S : Set M) (f : BooleanFunction n) : Prop :=
  ∀ x, f x = true ↔ P.eval x ∈ S

section Decides

variable {P : MonoidProgram n M} {S : Set M} {f : BooleanFunction n}

/-- A program that `σ`-computes `f`, with `σ ≠ 1`, decides `f` with the accepting set `{σ}`. -/
theorem MonoidProgram.Computes.decides {σ : M} (h : P.Computes σ f) (hσ : σ ≠ 1) :
    P.Decides {σ} f := fun x => by
  rw [h x, Set.mem_singleton_iff]
  cases f x
  · simpa using hσ.symm
  · simp

/-- Pushing a program along an injective homomorphism keeps what it decides, with the image of the
accepting set. -/
theorem MonoidProgram.Decides.map (h : P.Decides S f) {φ : M →* N} (hφ : Function.Injective φ) :
    (P.map φ).Decides (φ '' S) f := fun x => by
  rw [h x, eval_map, hφ.mem_set_image]

/-- The empty program decides every function of no variables, accepting everything when the
function is true and nothing when it is false. -/
theorem MonoidProgram.decides_one (f : BooleanFunction 0) :
    (1 : MonoidProgram 0 M).Decides {_m | f Fin.elim0 = true} f := fun x => by
  rw [Subsingleton.elim x Fin.elim0]
  rfl

end Decides

/-- The languages over `Bool` decided, at every input length `n`, by a program over `M` of length
at most `s n`, with an accepting set, for a polynomially bounded `s`. -/
def PolyLength (M : Type*) [Monoid M] : Set (Language Bool) :=
  {L | ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧ ∀ n,
    ∃ (P : MonoidProgram n M) (S : Set M), P.Decides S (L.slice n) ∧ P.length ≤ s n}

/-- **An injective homomorphism of monoids embeds the classes**: push the programs along it. -/
theorem PolyLength.subset_of_injective {φ : M →* N} (hφ : Function.Injective φ) :
    PolyLength M ⊆ PolyLength N := by
  rintro L ⟨s, hs, hP⟩
  refine ⟨s, hs, fun n => ?_⟩
  obtain ⟨P, S, hPS, hlen⟩ := hP n
  exact ⟨P.map φ, φ '' S, hPS.map hφ, (MonoidProgram.length_map φ P).trans_le hlen⟩

end Cslib.BranchingPrograms
