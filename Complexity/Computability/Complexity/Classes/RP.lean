/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP
public import Mathlib.Data.Fintype.Pi

/-!
# The classes RP and coRP

`RP` is defined like `BPP` (`Cslib.Complexity.BPP`), through deterministic polynomial-time
machines that read a random string, but with one-sided error
[Arora and Barak, Section 7.3][AroraBarak09]: `A ∈ RP enc` when there are a polynomial `p` and
a function `V : α × List Bool → Bool`, computable in polynomial time on inputs
`frame (enc a) ++ r`, such that for every member `a` of `A` at least half of the random strings
`r` of length `p (enc a).length` are accepted, and for every non-member none is. `coRP` contains
the complements of problems in `RP`.

Since an accepted random string is a certificate, `RP ⊆ NP` (`RP_subset_NP`). `ZPP` is not defined
here: its definition by expected running time does not fit the worst-case
`ComputableTidilyInPolyTime`, and its characterisation as `RP ∩ coRP` is only useful together with
the closure properties of polynomial time.

## Main definitions

* `Cslib.Complexity.DecidesWithOneSidedError`: the one-sided error condition.
* `Cslib.Complexity.RP`, `Cslib.Complexity.coRP`.

## Main results

* `Cslib.Complexity.RP_subset_NP`, `Cslib.Complexity.coRP_subset_coNP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

/-- `V` decides `A` with one-sided error, using random strings whose length is `p` evaluated at the
length of the encoded instance: for every member `a` of `A` at least half of the random strings are
accepted, and for every non-member none is. -/
def DecidesWithOneSidedError (enc : α ↪ List Bool) (p : Polynomial ℕ) (V : α × List Bool → Bool)
    (A : Set α) : Prop :=
  ∀ a, (a ∈ A → 2 ^ p.eval (enc a).length ≤
      2 * (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn r) = true).card) ∧
    (a ∉ A → ∀ r : Fin (p.eval (enc a).length) → Bool, V (a, List.ofFn r) = false)

/-- The problems decided with one-sided error by polynomial-time machines reading polynomially
long random strings, with respect to the encoding `enc` of instances. -/
def RP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧
      DecidesWithOneSidedError enc p V A}

/-- The problems whose complements are in `RP`. -/
def coRP (enc : α ↪ List Bool) : Set (Set α) := {A | Aᶜ ∈ RP enc}

variable {enc : α ↪ List Bool}

theorem mem_RP {A : Set α} : A ∈ RP enc ↔ ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧
      DecidesWithOneSidedError enc p V A :=
  Iff.rfl

theorem mem_coRP {A : Set α} : A ∈ coRP enc ↔ Aᶜ ∈ RP enc := Iff.rfl

/-- A random string accepted by a one-sided-error decider is a certificate: one-sided error gives
a verifier. -/
theorem DecidesWithOneSidedError.isVerifier {p : Polynomial ℕ} {V : α × List Bool → Bool}
    {A : Set α} (h : DecidesWithOneSidedError enc p V A) : IsVerifier enc p V A := by
  intro a
  constructor
  · intro ha
    have hpos := Nat.one_le_two_pow (n := p.eval (enc a).length)
    obtain ⟨r, hr⟩ : (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn r) = true).Nonempty := by
      rw [← Finset.card_pos]
      have := (h a).1 ha
      omega
    exact ⟨List.ofFn r, List.length_ofFn, (Finset.mem_filter.1 hr).2⟩
  · rintro ⟨w, hw, hV⟩
    by_contra ha
    have := (h a).2 ha fun i => w[i.val]'(by omega)
    rw [show (List.ofFn fun i : Fin (p.eval (enc a).length) => w[i.val]'(by omega)) = w from
      List.ext_getElem (by simp [hw]) fun i _ _ => by simp] at this
    rw [hV] at this
    exact Bool.noConfusion this

theorem RP_subset_NP : RP enc ⊆ NP enc := fun _ ⟨p, V, hV, h⟩ => ⟨p, V, hV, h.isVerifier⟩

theorem coRP_subset_coNP : coRP enc ⊆ coNP enc := fun _ hA => RP_subset_NP hA

end Cslib.Complexity
