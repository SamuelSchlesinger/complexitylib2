/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP
import Complexity.Computability.Complexity.Classes.SharpP.Combinators
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Closure properties of #P and GapP

`#P` (`Cslib.Complexity.SharpP`) is closed under addition and multiplication
[Arora and Barak, Chapter 17][AroraBarak09], and so `GapP` (`Cslib.Complexity.GapP`), the
differences of functions in `#P`, is closed under addition, subtraction and multiplication
[Fenner, Fortnow and Kurtz][FennerFortnowKurtz1994].

For the sum `f₁ + f₂`, the first bit of a certificate chooses which verifier to run
(`Cslib.Complexity.selectVerifier`); since the two verifiers read certificates of different
lengths `p₁(n)` and `p₂(n)`, each is padded to `p₁(n) + p₂(n)` bits by requiring the extra bits to
be `false` (`Cslib.Complexity.acceptCount_andVerifier_allFalseVerifier`). For the product, the two
verifiers read disjoint parts of the certificate (`Cslib.Complexity.acceptCount_andVerifier`).

## Main results

* `Cslib.Complexity.SharpP.add_mem`, `Cslib.Complexity.SharpP.mul_mem`: `#P` is closed under
  addition and multiplication.
* `Cslib.Complexity.SharpP.one_mem`, `Cslib.Complexity.SharpP.add_one_mem`,
  `Cslib.Complexity.SharpP.sum_mem`, `Cslib.Complexity.SharpP.prod_mem`,
  `Cslib.Complexity.SharpP.two_pow_mem`, `Cslib.Complexity.SharpP.two_pow_mul_mem`.
* `Cslib.Complexity.SharpP.exists_two_pow_sub_mem`: the complementary count of a function in `#P`.
* `Cslib.Complexity.GapP.add`, `Cslib.Complexity.GapP.sub`, `Cslib.Complexity.GapP.mul`: `GapP` is
  closed under addition, subtraction and multiplication.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

namespace SharpP

/-- **`#P` is closed under addition**: the first bit of a certificate chooses the verifier, and
the bits that the chosen verifier does not read must be `false`. -/
theorem add_mem {f₁ f₂ : α → ℕ} (h₁ : f₁ ∈ SharpP enc) (h₂ : f₂ ∈ SharpP enc) :
    f₁ + f₂ ∈ SharpP enc := by
  obtain ⟨p₁, V₁, hV₁, hf₁⟩ := h₁
  obtain ⟨p₂, V₂, hV₂, hf₂⟩ := h₂
  refine ⟨p₁ + p₂ + 1, selectVerifier
      (andVerifier (fun a => p₁.eval (enc a).length) V₁ allFalseVerifier)
      (andVerifier (fun a => p₂.eval (enc a).length) V₂ allFalseVerifier), by fun_prop,
    fun a => ?_⟩
  have e₁ := acceptCount_andVerifier_allFalseVerifier (fun a => p₁.eval (enc a).length) V₁ a
    (p₂.eval (enc a).length)
  have e₂ := acceptCount_andVerifier_allFalseVerifier (fun a => p₂.eval (enc a).length) V₂ a
    (p₁.eval (enc a).length)
  rw [Nat.add_comm (p₂.eval _)] at e₂
  rw [Pi.add_apply, hf₁ a, hf₂ a, Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_one,
    acceptCount_selectVerifier, e₁, e₂]

/-- **`#P` is closed under multiplication**: the two verifiers read disjoint parts of the
certificate. -/
theorem mul_mem {f₁ f₂ : α → ℕ} (h₁ : f₁ ∈ SharpP enc) (h₂ : f₂ ∈ SharpP enc) :
    f₁ * f₂ ∈ SharpP enc := by
  obtain ⟨p₁, V₁, hV₁, hf₁⟩ := h₁
  obtain ⟨p₂, V₂, hV₂, hf₂⟩ := h₂
  refine ⟨p₁ + p₂, andVerifier (fun a => p₁.eval (enc a).length) V₁ V₂, by fun_prop,
    fun a => ?_⟩
  rw [Pi.mul_apply, hf₁ a, hf₂ a, Polynomial.eval_add, acceptCount_andVerifier]

/-- The function `2 ^ q(n)`, where `n` is the length of the encoded instance, is in `#P`: every
certificate of length `q(n)` is accepted. -/
theorem two_pow_mem (q : Polynomial ℕ) : (fun a => 2 ^ q.eval (enc a).length) ∈ SharpP enc :=
  ⟨q, fun _ => true, .const true, fun a => (acceptCount_true a _).symm⟩

/-- The constant function `1` is in `#P`: the empty certificate is accepted. -/
theorem one_mem : (1 : α → ℕ) ∈ SharpP enc :=
  ⟨0, fun _ => true, .const true, fun a => by simp⟩

/-- `#P` is closed under adding one. -/
theorem add_one_mem {f : α → ℕ} (h : f ∈ SharpP enc) : f + 1 ∈ SharpP enc :=
  add_mem h one_mem

/-- `#P` is closed under multiplication by `2 ^ q(n)`, where `n` is the length of the encoded
instance. -/
theorem two_pow_mul_mem (q : Polynomial ℕ) {f : α → ℕ} (h : f ∈ SharpP enc) :
    (fun a => 2 ^ q.eval (enc a).length * f a) ∈ SharpP enc :=
  mul_mem (two_pow_mem q) h

/-- `#P` is closed under finite sums. -/
theorem sum_mem {ι : Type*} (s : Finset ι) {f : ι → α → ℕ} (h : ∀ i ∈ s, f i ∈ SharpP enc) :
    ∑ i ∈ s, f i ∈ SharpP enc := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero_mem (enc := enc))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact add_mem (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- `#P` is closed under finite products. -/
theorem prod_mem {ι : Type*} (s : Finset ι) {f : ι → α → ℕ} (h : ∀ i ∈ s, f i ∈ SharpP enc) :
    ∏ i ∈ s, f i ∈ SharpP enc := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one_mem (enc := enc))
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact mul_mem (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- **The complementary count**: a function `f` in `#P` is at most `2 ^ p(n)` for a polynomial
`p`, where `n` is the length of the encoded instance, with `2 ^ p(n) - f` also in `#P`: the
negated verifier accepts the rejected certificates. -/
theorem exists_two_pow_sub_mem {f : α → ℕ} (hf : f ∈ SharpP enc) :
    ∃ p : Polynomial ℕ, (∀ a, f a ≤ 2 ^ p.eval (enc a).length) ∧
      (fun a => 2 ^ p.eval (enc a).length - f a) ∈ SharpP enc := by
  obtain ⟨p, V, hV, hf⟩ := hf
  refine ⟨p, fun a => (hf a).trans_le acceptCount_le_two_pow,
    p, fun x => !V x, ComputableTidilyInPolyTime.bool_not.comp hV, fun a => ?_⟩
  beta_reduce
  rw [hf a, acceptCount_not]

/-- A function in `#P`, cast to the integers, is in `GapP`. -/
theorem natCast_mem_GapP {f : α → ℕ} (hf : f ∈ SharpP enc) :
    (fun a => (f a : ℤ)) ∈ GapP enc :=
  ⟨f, hf, 0, zero_mem, fun a => by simp⟩

end SharpP

namespace GapP

/-- **`GapP` is closed under addition.** -/
theorem add {g₁ g₂ : α → ℤ} (h₁ : g₁ ∈ GapP enc) (h₂ : g₂ ∈ GapP enc) : g₁ + g₂ ∈ GapP enc := by
  obtain ⟨f₁, hf₁, f₂, hf₂, hg₁⟩ := h₁
  obtain ⟨f₃, hf₃, f₄, hf₄, hg₂⟩ := h₂
  refine ⟨f₁ + f₃, SharpP.add_mem hf₁ hf₃, f₂ + f₄, SharpP.add_mem hf₂ hf₄, fun a => ?_⟩
  rw [Pi.add_apply, hg₁ a, hg₂ a, Pi.add_apply, Pi.add_apply]
  push_cast
  ring

/-- **`GapP` is closed under subtraction.** -/
theorem sub {g₁ g₂ : α → ℤ} (h₁ : g₁ ∈ GapP enc) (h₂ : g₂ ∈ GapP enc) : g₁ - g₂ ∈ GapP enc := by
  simpa only [sub_eq_add_neg] using add h₁ (neg h₂)

/-- **`GapP` is closed under multiplication**:
`(f₁ - f₂) (f₃ - f₄) = (f₁ f₃ + f₂ f₄) - (f₁ f₄ + f₂ f₃)`. -/
theorem mul {g₁ g₂ : α → ℤ} (h₁ : g₁ ∈ GapP enc) (h₂ : g₂ ∈ GapP enc) : g₁ * g₂ ∈ GapP enc := by
  obtain ⟨f₁, hf₁, f₂, hf₂, hg₁⟩ := h₁
  obtain ⟨f₃, hf₃, f₄, hf₄, hg₂⟩ := h₂
  refine ⟨f₁ * f₃ + f₂ * f₄, SharpP.add_mem (SharpP.mul_mem hf₁ hf₃) (SharpP.mul_mem hf₂ hf₄),
    f₁ * f₄ + f₂ * f₃, SharpP.add_mem (SharpP.mul_mem hf₁ hf₄) (SharpP.mul_mem hf₂ hf₃),
    fun a => ?_⟩
  simp only [Pi.mul_apply, Pi.add_apply, hg₁ a, hg₂ a]
  push_cast
  ring

end GapP

end Cslib.Complexity
