/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, next to `Finset.card_le_mul_card_image`)

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting a finite set by its fibers

`Set.ncard` forms of the familiar `Finset` estimates.

## Main results

* `Set.ncard_eq_sum_ncard_fiberwise`: a finite set mapped into a finset is the disjoint union of
  its fibers (`Finset.card_eq_sum_card_fiberwise`).
* `Set.ncard_le_mul_ncard_image`: a finite set whose fibers under `f` have at most `n` elements
  has at most `n` times as many elements as its image (`Finset.card_le_mul_card_image`).
* `Set.ncard_image_le_ncard_image_of_factorsThrough`: if `f` factors through `g` on `s`, then
  `f` takes at most as many values on `s` as `g`.
* `Set.encard_lt_coe_iff_finite_ncard_lt`: `encard` and `ncard` agree below a natural number
  (`Set.encard_le_coe_iff_finite_ncard_le`).
-/

@[expose] public section

namespace Set

variable {α β γ : Type*}

/-- A set has fewer than `k` elements, counted with `encard`, exactly when it is finite with fewer
than `k` elements counted with `ncard`. -/
theorem encard_lt_coe_iff_finite_ncard_lt {s : Set α} {k : ℕ} :
    s.encard < k ↔ s.Finite ∧ s.ncard < k := by
  refine ⟨fun h => ?_, fun ⟨hs, h⟩ => ?_⟩
  · have hs : s.Finite := encard_lt_top_iff.mp (h.trans (ENat.natCast_lt_top k))
    rw [← hs.cast_ncard_eq] at h
    exact ⟨hs, by exact_mod_cast h⟩
  · rw [← hs.cast_ncard_eq]
    exact_mod_cast h

/-- A finite set that `f` maps into the finset `t` is the disjoint union of its fibers over
`t`. -/
theorem ncard_eq_sum_ncard_fiberwise {s : Set α} (hs : s.Finite) {f : α → β} {t : Finset β}
    (H : MapsTo f s t) : s.ncard = ∑ b ∈ t, {a ∈ s | f a = b}.ncard := by
  classical
  lift s to Finset α using hs
  rw [ncard_coe_finset, Finset.card_eq_sum_card_fiberwise H]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← ncard_coe_finset, Finset.coe_filter]
  rfl

/-- A finite set whose fibers under `f` have at most `n` elements has at most `n` times as many
elements as its image. -/
theorem ncard_le_mul_ncard_image {s : Set α} (hs : s.Finite) (f : α → β) (n : ℕ)
    (hn : ∀ b ∈ f '' s, {a ∈ s | f a = b}.ncard ≤ n) : s.ncard ≤ n * (f '' s).ncard := by
  classical
  lift s to Finset α using hs
  rw [ncard_coe_finset, ← Finset.coe_image, ncard_coe_finset]
  refine Finset.card_le_mul_card_image s n fun b hb => ?_
  have := hn b (by simpa using hb)
  rwa [← ncard_coe_finset, Finset.coe_filter]

/-- If `f` factors through `g` on `s`, that is, `f` agrees on any two points of `s` at which `g`
agrees, then `f` takes at most as many values on the finite set `s` as `g` does. -/
theorem ncard_image_le_ncard_image_of_factorsThrough {s : Set α} (hs : s.Finite) {f : α → β}
    {g : α → γ} (h : ∀ a ∈ s, ∀ b ∈ s, g a = g b → f a = f b) :
    (f '' s).ncard ≤ (g '' s).ncard := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · simp
  have : Nonempty α := ⟨a₀⟩
  -- `f` is a function of `g` on `s`: read `f` off any point of `s` with the same value of `g`.
  have hfg : f '' s = (fun c => f (Function.invFunOn g s c)) '' (g '' s) := by
    rw [image_image]
    refine image_congr fun a ha => ?_
    exact (h _ (Function.invFunOn_mem ⟨a, ha, rfl⟩) a ha (Function.invFunOn_eq ⟨a, ha, rfl⟩)).symm
  exact hfg ▸ ncard_image_le (hs.image g)

end Set
