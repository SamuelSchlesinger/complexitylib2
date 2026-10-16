/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.Fintype.Pi

/-!
# The counting classes #P and GapP

`#P` is defined through polynomial-time verifiers, like `NP` (`Cslib.Complexity.NP`)
[Valiant][Valiant1979], [Arora and Barak, Chapter 17][AroraBarak09]: `f ∈ SharpP enc` when there
are a polynomial `p` and a function `V : α × List Bool → Bool`, computable in polynomial time on
inputs `encPair enc encBits (a, w) = frame (enc a) ++ w`, such that `f a` is the number of strings
`w` of length `p (enc a).length` with `V (a, w) = true`. The problems in `NP` are exactly the sets
where functions in `#P` are nonzero (`mem_NP_iff_exists_SharpP`).

`GapP` consists of the differences of two functions in `#P`. Fenner, Fortnow and Kurtz define it
through the differences between the numbers of accepting and rejecting paths of nondeterministic
machines, and show that this gives the differences of functions in `#P`
[Fenner, Fortnow and Kurtz][FennerFortnowKurtz1994]; here that characterisation is the
definition. The characterisations by nondeterministic machines are not proved here.

## Main definitions

* `Cslib.Complexity.acceptCount`: the number of strings of a given length that a verifier accepts
  together with an instance.
* `Cslib.Complexity.SharpP`, `Cslib.Complexity.GapP`.

## Main results

* `Cslib.Complexity.mem_NP_iff_exists_SharpP`: `NP` consists of the supports of functions in `#P`.
* `Cslib.Complexity.SharpP.exists_le_two_pow`: functions in `#P` are at most exponential.
* `Cslib.Complexity.GapP.neg`: `GapP` is closed under negation.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

/-- The number of strings `w` of length `n` with `V (a, w) = true`. -/
def acceptCount (V : α × List Bool → Bool) (a : α) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin n → Bool => V (a, List.ofFn w) = true).card

section acceptCount

variable {V : α × List Bool → Bool} {a : α} {n : ℕ}

theorem acceptCount_le_two_pow : acceptCount V a n ≤ 2 ^ n :=
  (Finset.card_filter_le _ _).trans (by simp)

theorem acceptCount_pos_iff :
    0 < acceptCount V a n ↔ ∃ w : List Bool, w.length = n ∧ V (a, w) = true := by
  rw [acceptCount, Finset.card_pos, Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨w, -, hw⟩
    exact ⟨List.ofFn w, List.length_ofFn, hw⟩
  · rintro ⟨w, rfl, hw⟩
    exact ⟨fun i => w[i.val], Finset.mem_univ _, by rwa [List.ofFn_getElem]⟩

/-- The strings that `V` accepts together with `a` and those it rejects are all the strings. -/
theorem acceptCount_add_card_filter_eq_false :
    acceptCount V a n +
      (Finset.univ.filter fun w : Fin n → Bool => V (a, List.ofFn w) = false).card = 2 ^ n := by
  have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    fun w : Fin n → Bool => V (a, List.ofFn w) = true
  simpa only [acceptCount, Bool.not_eq_true, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] using this

end acceptCount

/-- The functions counting the certificates that a polynomial-time verifier accepts, with
certificates of polynomial length, with respect to the encoding `enc` of instances. -/
def SharpP (enc : α ↪ List Bool) : Set (α → ℕ) :=
  {f | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧
      ∀ a, f a = acceptCount V a (p.eval (enc a).length)}

/-- The differences of two functions in `#P`, with respect to the encoding `enc` of instances. -/
def GapP (enc : α ↪ List Bool) : Set (α → ℤ) :=
  {g | ∃ f₁ ∈ SharpP enc, ∃ f₂ ∈ SharpP enc, ∀ a, g a = f₁ a - f₂ a}

variable {enc : α ↪ List Bool}

theorem mem_SharpP {f : α → ℕ} : f ∈ SharpP enc ↔ ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧
      ∀ a, f a = acceptCount V a (p.eval (enc a).length) :=
  Iff.rfl

theorem mem_GapP {g : α → ℤ} :
    g ∈ GapP enc ↔ ∃ f₁ ∈ SharpP enc, ∃ f₂ ∈ SharpP enc, ∀ a, g a = f₁ a - f₂ a :=
  Iff.rfl

/-- **`NP` consists of the supports of functions in `#P`**: a problem is in `NP` exactly when it
is the set of instances where some function in `#P` is nonzero. -/
theorem mem_NP_iff_exists_SharpP {A : Set α} :
    A ∈ NP enc ↔ ∃ f ∈ SharpP enc, ∀ a, a ∈ A ↔ 0 < f a := by
  constructor
  · rintro ⟨p, V, hV, h⟩
    exact ⟨_, ⟨p, V, hV, fun _ => rfl⟩, fun a => (h a).trans acceptCount_pos_iff.symm⟩
  · rintro ⟨f, ⟨p, V, hV, hf⟩, h⟩
    exact ⟨p, V, hV, fun a => by rw [h a, hf a, acceptCount_pos_iff]⟩

namespace SharpP

/-- A function in `#P` is at most exponential in the length of the encoded instance. -/
theorem exists_le_two_pow {f : α → ℕ} (hf : f ∈ SharpP enc) :
    ∃ p : Polynomial ℕ, ∀ a, f a ≤ 2 ^ p.eval (enc a).length :=
  let ⟨p, _, _, h⟩ := hf
  ⟨p, fun a => (h a).trans_le acceptCount_le_two_pow⟩

end SharpP

namespace GapP

theorem sub_mem {f₁ f₂ : α → ℕ} (hf₁ : f₁ ∈ SharpP enc) (hf₂ : f₂ ∈ SharpP enc) :
    (fun a => (f₁ a : ℤ) - f₂ a) ∈ GapP enc :=
  ⟨f₁, hf₁, f₂, hf₂, fun _ => rfl⟩

/-- `GapP` is closed under negation: exchange the two functions in `#P`. -/
theorem neg {g : α → ℤ} (hg : g ∈ GapP enc) : -g ∈ GapP enc :=
  let ⟨f₁, hf₁, f₂, hf₂, h⟩ := hg
  ⟨f₂, hf₂, f₁, hf₁, fun a => by rw [Pi.neg_apply, h a, neg_sub]⟩

end GapP

end Cslib.Complexity
