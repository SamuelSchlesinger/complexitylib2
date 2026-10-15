/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Kolmogorov.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import Mathlib.Data.Nat.Size

/-!
# Conditional complexity and the chain rule

A *conditional description method* for `α` given `β` is a family `N : β → DescriptionMethod α`:
the description method `N y` has access to the condition `y`. The conditional complexity
`C_N(x | y)` is `(N y).complexity x`, and its time-bounded version `C_N^t(x | y)` is
`(N y).timeBoundedComplexity t x`. All results about description methods apply to them for a fixed
condition; for instance fewer than `2 ^ r` objects have `C_N(x | y) < r`, for every `y`.

A *composition* of a description method `M` and a conditional description method `N` into a
description method `J` along a pairing `pair` combines a program for `x` under `M` and a program
for `y` given `x` under `N x` into a program for `pair x y` under `J`. If combining costs `ℓ |p|`
bits beyond the lengths of the two programs, then the *chain rule*
`C_J(pair x y) ≤ C_M(x) + C_N(y | x) + ℓ (C_M(x))` holds, and similarly for the time-bounded
complexities. For the combined program to be decodable, the end of the program for `x` must be
marked, and this costs more than a constant number of bits. The self-delimiting code
`selfDelimitingCode p` of `p`, which prefixes `p` with its length in binary, costs
`ℓ n = 2 log₂ n + O(1)` bits [Li and Vitányi, Chapters 1 and 2][LiVitanyi2019]; prefixing `p` with
its doubled bits instead gives `C(x, y) ≤ 2 C(x) + C(y) + O(1)` [Sipser, Section 6.4][Sipser2013].

## Main definitions

* `Cslib.Kolmogorov.selfDelimitingCode`: a program prefixed by its length in binary.
* `Cslib.Kolmogorov.DescriptionMethod.Composition`: a combination of programs for `x` and for `y`
  given `x` into programs for `pair x y`.
* `Cslib.Kolmogorov.DescriptionMethod.Composition.ofSelfDelimitingCode`: the composition whose
  combined program is the self-delimiting code of the first program followed by the second.

## Main results

* `Cslib.Kolmogorov.selfDelimitingCode_append_inj`: a self-delimiting code followed by any string
  determines both.
* `Cslib.Kolmogorov.length_selfDelimitingCode`: the code of `p` has length
  `|p| + 2 size |p| + 1`.
* `Cslib.Kolmogorov.DescriptionMethod.Composition.complexity_le`: the chain rule
  `C_J(pair x y) ≤ C_M(x) + C_N(y | x) + ℓ (C_M(x))`.
* `Cslib.Kolmogorov.DescriptionMethod.Composition.timeBoundedComplexity_le_of_le`: the
  time-bounded chain rule.

## References

* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Kolmogorov

open Turing.MultiTapeTM (frame encNat frame_append_inj)

/-! ### A self-delimiting code -/

/-- The *self-delimiting code* of a binary string `p`: the binary digits of its length, framed,
followed by `p`. A self-delimiting code followed by any string determines both
(`selfDelimitingCode_append_inj`), at a cost of `2 size |p| + 1` bits. -/
def selfDelimitingCode (p : List Bool) : List Bool :=
  frame (encNat p.length) ++ p

theorem length_selfDelimitingCode (p : List Bool) :
    (selfDelimitingCode p).length = p.length + (2 * p.length.size + 1) := by
  simp only [selfDelimitingCode, List.length_append, Turing.MultiTapeTM.length_frame,
    Turing.MultiTapeTM.encNat_apply, Nat.size_eq_bits_len]
  omega

/-- A self-delimiting code followed by any string determines both. -/
theorem selfDelimitingCode_append_inj {p p' q q' : List Bool}
    (h : selfDelimitingCode p ++ q = selfDelimitingCode p' ++ q') : p = p' ∧ q = q' := by
  simp only [selfDelimitingCode, List.append_assoc] at h
  obtain ⟨hlen, h⟩ := frame_append_inj h
  exact List.append_inj h (encNat.injective hlen)

namespace DescriptionMethod

variable {α β γ : Type*}

/-! ### Composition and the chain rule -/

/-- A *composition* of the description method `M` for `α` and the conditional description method
`N` for `β` given `α` into the description method `J` for `γ`, along `pair : α → β → γ`, with
length overhead `ℓ` and time overhead `τ`. If the program `p` outputs `x` under `M` within `t₁`
steps and the program `q` outputs `y` under `N x` within `t₂` steps, then `combine p q` is a
program of length at most `|p| + |q| + ℓ |p|` that outputs `pair x y` under `J` within
`τ (|p| + |q|) (t₁ + t₂)` steps. -/
structure Composition (M : DescriptionMethod α) (N : α → DescriptionMethod β)
    (J : DescriptionMethod γ) (pair : α → β → γ) (ℓ : ℕ → ℕ) (τ : ℕ → ℕ → ℕ) where
  /-- The combination of a program for `x` and a program for `y` given `x`. -/
  combine : List Bool → List Bool → List Bool
  /-- Combining costs at most `ℓ |p|` bits beyond the lengths of the two programs. -/
  length_combine_le (p q : List Bool) : (combine p q).length ≤ p.length + q.length + ℓ p.length
  /-- The combined program outputs the pair, within the time overhead. -/
  mem_run_combine {p q : List Bool} {t₁ t₂ : ℕ} {x : α} {y : β} :
    x ∈ M.run p t₁ → y ∈ (N x).run q t₂ →
      pair x y ∈ J.run (combine p q) (τ (p.length + q.length) (t₁ + t₂))

namespace Composition

variable {M : DescriptionMethod α} {N : α → DescriptionMethod β} {J : DescriptionMethod γ}
  {pair : α → β → γ} {ℓ : ℕ → ℕ} {τ : ℕ → ℕ → ℕ}

/-- The composition whose combined program is the self-delimiting code of the program for `x`
followed by the program for `y` given `x`; its length overhead is `2 size |p| + 1`. -/
def ofSelfDelimitingCode
    (h : ∀ {p q : List Bool} {t₁ t₂ : ℕ} {x : α} {y : β}, x ∈ M.run p t₁ → y ∈ (N x).run q t₂ →
      pair x y ∈ J.run (selfDelimitingCode p ++ q) (τ (p.length + q.length) (t₁ + t₂))) :
    Composition M N J pair (fun n => 2 * n.size + 1) τ where
  combine p q := selfDelimitingCode p ++ q
  length_combine_le p q := by
    rw [List.length_append, length_selfDelimitingCode]
    omega
  mem_run_combine := h

theorem produces_combine (S : Composition M N J pair ℓ τ) {p q : List Bool} {x : α} {y : β}
    (hx : M.Produces p x) (hy : (N x).Produces q y) : J.Produces (S.combine p q) (pair x y) :=
  let ⟨_, hx⟩ := hx
  let ⟨_, hy⟩ := hy
  ⟨_, S.mem_run_combine hx hy⟩

/-- **Chain rule.** `C_J(pair x y) ≤ C_M(x) + C_N(y | x) + ℓ (C_M(x))`. When `C_M(x) = ⊤` the
right-hand side is `⊤`, so the value `ℓ 0` used for `ℓ ⊤` does not matter. -/
theorem complexity_le (S : Composition M N J pair ℓ τ) (x : α) (y : β) :
    J.complexity (pair x y) ≤
      M.complexity x + (N x).complexity y + ℓ (M.complexity x).toNat := by
  by_cases hx : M.complexity x = ⊤
  · simp [hx]
  by_cases hy : (N x).complexity y = ⊤
  · simp [hy]
  obtain ⟨p, hp, hplen⟩ := exists_length_eq_complexity hx
  obtain ⟨q, hq, hqlen⟩ := exists_length_eq_complexity hy
  rw [← hplen, ← hqlen, ENat.toNat_natCast]
  exact (complexity_le_length (S.produces_combine hp hq)).trans (mod_cast S.length_combine_le p q)

/-- **Time-bounded chain rule.** If `C_M^{t₁}(x) ≤ k` and `C_N^{t₂}(y | x) ≤ l`, then
`C_J^{τ (k + l) (t₁ + t₂)}(pair x y) ≤ k + l + ℓ k`, for overheads monotone in the program
lengths. -/
theorem timeBoundedComplexity_le_of_le (S : Composition M N J pair ℓ τ) (hℓ : Monotone ℓ)
    {t₁ t₂ k l : ℕ} (hτ : Monotone (τ · (t₁ + t₂))) {x : α} {y : β}
    (hx : M.timeBoundedComplexity t₁ x ≤ k) (hy : (N x).timeBoundedComplexity t₂ y ≤ l) :
    J.timeBoundedComplexity (τ (k + l) (t₁ + t₂)) (pair x y) ≤ (k + l + ℓ k : ℕ) := by
  obtain ⟨p, hp, hpx⟩ := timeBoundedComplexity_le_natCast_iff.mp hx
  obtain ⟨q, hq, hqy⟩ := timeBoundedComplexity_le_natCast_iff.mp hy
  refine timeBoundedComplexity_le_natCast_iff.mpr ⟨S.combine p q, ?_, ?_⟩
  · have := hℓ hp
    have := S.length_combine_le p q
    omega
  · exact J.run_mono (hτ (Nat.add_le_add hp hq)) (S.mem_run_combine hpx hqy)

end Composition

end DescriptionMethod

end Cslib.Kolmogorov
