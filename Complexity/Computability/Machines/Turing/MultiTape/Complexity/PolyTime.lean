/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: subset of crei/tidy-universal `Complexity/PolyTime.lean`;
-- definitions only, delete when it lands

public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs
import Mathlib.Tactic.Ring

/-!
# Tidy computability in polynomial time

`ComputableTidilyInPolyTime f encIn encOut`: `f` is tidily computable within time and space
bounded by a polynomial in the length of the encoded input.

A verbatim subset of Christian Reitwiessner's `Complexity/PolyTime.lean` (branch
`crei/tidy-universal`): the definitions and the arithmetic of polynomial bounds, without the
closure properties, which need the composition machinery not yet in cslib.

## Main definitions

* `Turing.MultiTapeTM.PolyBounded`: a function bounded by a polynomial in a size.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime`: tidy computability in polynomial time and space.
-/

namespace Turing.MultiTapeTM

/-! ### Polynomial bounds -/

/-- `u` is bounded by a polynomial in `size`. -/
@[expose] public def PolyBounded {α : Type*} (size u : α → ℕ) : Prop :=
  ∃ c d, ∀ a, u a ≤ c * (size a + 1) ^ d

namespace PolyBounded

variable {α β : Type*} {size : α → ℕ} {u v : α → ℕ}

public theorem mono (h : PolyBounded size v) (huv : ∀ a, u a ≤ v a) : PolyBounded size u :=
  let ⟨c, d, hv⟩ := h
  ⟨c, d, fun a => (huv a).trans (hv a)⟩

public theorem const (k : ℕ) : PolyBounded size fun _ => k :=
  ⟨k, 0, fun _ => by simp⟩

public theorem self : PolyBounded size size :=
  ⟨1, 1, fun _ => by simp⟩

public theorem add (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size fun a => u a + v a := by
  obtain ⟨c₁, d₁, h₁⟩ := hu
  obtain ⟨c₂, d₂, h₂⟩ := hv
  refine ⟨c₁ + c₂, max d₁ d₂, fun a => (add_le_add (h₁ a) (h₂ a)).trans ?_⟩
  rw [Nat.add_mul]
  gcongr <;> omega

public theorem mul (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size fun a => u a * v a := by
  obtain ⟨c₁, d₁, h₁⟩ := hu
  obtain ⟨c₂, d₂, h₂⟩ := hv
  refine ⟨c₁ * c₂, d₁ + d₂, fun a => (Nat.mul_le_mul (h₁ a) (h₂ a)).trans_eq ?_⟩
  rw [Nat.pow_add]
  ring

/-- Substitution: if `v` is bounded by a polynomial in `size'` and `size' ∘ g` by a polynomial in
`size`, then `v ∘ g` is bounded by a polynomial in `size`. -/
public theorem comp {size' : β → ℕ} {v : β → ℕ} {g : α → β} (hv : PolyBounded size' v)
    (hg : PolyBounded size fun a => size' (g a)) : PolyBounded size fun a => v (g a) := by
  obtain ⟨c₁, d₁, h₁⟩ := hg
  obtain ⟨c₂, d₂, h₂⟩ := hv
  refine ⟨c₂ * (c₁ + 1) ^ d₂, d₁ * d₂, fun a => (h₂ (g a)).trans ?_⟩
  have h : size' (g a) + 1 ≤ (c₁ + 1) * (size a + 1) ^ d₁ := by
    have := h₁ a
    dsimp only at this
    have := Nat.one_le_pow d₁ (size a + 1) (Nat.succ_pos _)
    rw [Nat.add_one_mul]
    omega
  refine (Nat.mul_le_mul_left c₂ (Nat.pow_le_pow_left h d₂)).trans_eq ?_
  rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc]

end PolyBounded

/-! ### Polynomial time -/

/-- `f` is tidily computable within time and space bounded by a polynomial in the length of the
encoded input. -/
@[expose] public def ComputableTidilyInPolyTime {α β : Type*} (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) : Prop :=
  ∃ t s, PolyBounded (fun a => (encIn a).length) t ∧ PolyBounded (fun a => (encIn a).length) s ∧
    ComputableTidilyInTimeAndSpace f encIn encOut t s

end Turing.MultiTapeTM
