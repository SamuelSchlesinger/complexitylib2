/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Restrict
public import Mathlib.Logic.Function.DependsOn
import Mathlib.Logic.Equiv.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Rectangles and rectangle-free sets

An *input* is a function `x : ι → U` from a type of coordinates to an alphabet. A set of
coordinates `X` cuts an input into two parts: its restriction to `X` and its restriction to the
complement `Xᶜ`. The *rectangle* with sides `A` and `B` is the set of inputs whose part on `X`
lies in `A` and whose part on `Xᶜ` lies in `B`: a combinatorial rectangle in the sense of
communication complexity, for the cut of the coordinates into `X` and `Xᶜ`.

A set of inputs `S` is `K`-*rectangle-free* when every rectangle inside `S`, for every cut of the
coordinates, has a side with fewer than `K` elements. This is the only property of a hard set
that the frontier method uses.

**The support lemma** (`RectangleFree.pow_ncard_compl_lt`): a large rectangle-free set depends on
all but fewer than `log_|U| K` coordinates. If `S` ignored a set `D` of coordinates carrying at
least `K` assignments, then `S` would contain the rectangle whose side on `D` is everything; its
other side, and hence `S`, would be small.

## Main definitions

* `Cslib.Circuits.Frontier.rectangle X A B`: the rectangle with sides `A` on `X` and `B` on `Xᶜ`.
* `Cslib.Circuits.Frontier.RectangleFree S K`: every rectangle inside `S` has a side with fewer
  than `K` elements.

## Main results

* `Cslib.Circuits.Frontier.RectangleFree.ncard_le_of_dependsOn`: a rectangle-free set that
  ignores the coordinates in `D`, with `K ≤ |U| ^ |D|`, has at most `|U| ^ |D| * (K - 1)`
  elements.
* `Cslib.Circuits.Frontier.RectangleFree.pow_ncard_compl_lt`: the support lemma.

## References

* [E. Kushilevitz, N. Nisan, *Communication Complexity*, Ch. 1][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set

variable {ι U : Type*}

/-- The *rectangle* with sides `A` and `B` for the cut `X`: the inputs whose part on `X` lies
in `A` and whose part on the complement `Xᶜ` lies in `B`. -/
def rectangle (X : Set ι) (A : Set (X → U)) (B : Set (↥Xᶜ → U)) : Set (ι → U) :=
  {x | X.domRestrict x ∈ A ∧ Xᶜ.domRestrict x ∈ B}

@[simp]
theorem mem_rectangle {X : Set ι} {A : Set (X → U)} {B : Set (↥Xᶜ → U)} {x : ι → U} :
    x ∈ rectangle X A B ↔ X.domRestrict x ∈ A ∧ Xᶜ.domRestrict x ∈ B :=
  Iff.rfl

/-- An input is determined by its two parts: cutting along `X` is injective. -/
theorem domRestrict_prodMk_injective (X : Set ι) :
    Function.Injective fun x : ι → U => (X.domRestrict x, Xᶜ.domRestrict x) := by
  classical
  exact (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => U).injective

/-- A set of inputs `S` is `K`-*rectangle-free* when every rectangle contained in `S`, for
every cut of the coordinates, has a side with fewer than `K` elements.

Sides are counted with `Set.ncard`, so the notion is meant for finitely many coordinates and a
finite alphabet, as in all results below. -/
def RectangleFree (S : Set (ι → U)) (K : ℕ) : Prop :=
  ∀ (X : Set ι) (A : Set (X → U)) (B : Set (↥Xᶜ → U)),
    rectangle X A B ⊆ S → A.ncard < K ∨ B.ncard < K

namespace RectangleFree

variable {S T : Set (ι → U)} {K K' : ℕ}

/-- The threshold of a rectangle-free set is positive: the empty rectangle has empty sides. -/
theorem pos (h : RectangleFree S K) : 0 < K := by
  rcases h univ ∅ ∅ (by simp [rectangle]) with h | h <;> simpa using h

/-- A subset of a rectangle-free set is rectangle-free. -/
theorem subset (h : RectangleFree S K) (hTS : T ⊆ S) : RectangleFree T K :=
  fun X A B hAB => h X A B (hAB.trans hTS)

/-- Raising the threshold keeps a set rectangle-free. -/
theorem mono (h : RectangleFree S K) (hK : K ≤ K') : RectangleFree S K' :=
  fun X A B hAB => (h X A B hAB).imp (·.trans_le hK) (·.trans_le hK)

section Finite

variable [Finite ι] [Finite U]

/-- A rectangle-free set that does not depend on the coordinates in `D` is small: if `D` alone
carries at least `K` assignments, then `S` has at most `|U| ^ |D| * (K - 1)` elements.

The rectangle whose side on `D` is *every* assignment and whose side on `Dᶜ` is the set of
`Dᶜ`-parts of `S` lies inside `S`. Its first side is large, so its second side is small. -/
theorem ncard_le_of_dependsOn (hS : RectangleFree S K) {D : Set ι}
    (hD : DependsOn (· ∈ S) Dᶜ) (hK : K ≤ Nat.card U ^ D.ncard) :
    S.ncard ≤ Nat.card U ^ D.ncard * (K - 1) := by
  set B : Set (↥Dᶜ → U) := Dᶜ.domRestrict '' S
  have hsub : rectangle D univ B ⊆ S := by
    rintro z ⟨-, y, hy, hyz⟩
    have : (y ∈ S) = (z ∈ S) := hD fun i hi => congrFun hyz ⟨i, hi⟩
    exact this ▸ hy
  have hA : (univ : Set (D → U)).ncard = Nat.card U ^ D.ncard := by
    rw [ncard_univ, Nat.card_fun, Nat.card_coe_set_eq]
  have hB : B.ncard ≤ K - 1 := by
    rcases hS D univ B hsub with h | h <;> omega
  calc S.ncard
      ≤ ((univ : Set (D → U)) ×ˢ B).ncard :=
        ncard_le_ncard_of_injOn _ (fun x hx => ⟨mem_univ _, x, hx, rfl⟩)
          (domRestrict_prodMk_injective D).injOn
    _ = Nat.card U ^ D.ncard * B.ncard := by rw [ncard_prod, hA]
    _ ≤ Nat.card U ^ D.ncard * (K - 1) := Nat.mul_le_mul_left _ hB

/-- **The support lemma.** A `K`-rectangle-free set with at least `|U| * K ^ 2` elements depends
on all but fewer than `log_|U| K` coordinates: if `S` depends only on the coordinates in `R`,
then `|U| ^ |Rᶜ| < K`. -/
theorem pow_ncard_compl_lt [Nonempty U] (hS : RectangleFree S K) {R : Set ι}
    (hR : DependsOn (· ∈ S) R) (hbig : Nat.card U * K ^ 2 ≤ S.ncard) :
    Nat.card U ^ Rᶜ.ncard < K := by
  set q := Nat.card U
  have hK := hS.pos
  have hq : 0 < q := Nat.card_pos
  -- If `K ≤ q ^ d` for some `d ≤ |Rᶜ|`, then `S` ignores `d` coordinates and is small.
  have hsmall : ∀ d ≤ Rᶜ.ncard, K ≤ q ^ d → S.ncard ≤ q ^ d * (K - 1) := fun d hd hle => by
    obtain ⟨D, hDR, rfl⟩ := exists_subset_card_eq hd
    exact hS.ncard_le_of_dependsOn (hR.mono (subset_compl_comm.mp hDR)) hle
  -- Hence `q ^ d < K` for every `d ≤ |Rᶜ|`, by induction on `d`.
  suffices ∀ d ≤ Rᶜ.ncard, q ^ d < K from this _ le_rfl
  intro d hd
  by_contra! hle
  have hS' := hsmall d hd hle
  induction d with
  | zero =>
    -- `|S| ≤ K - 1 < K ≤ q K ^ 2`.
    rw [pow_zero, one_mul] at hS'
    have : K ≤ q * K ^ 2 := by nlinarith
    omega
  | succ d ih =>
    -- `q ^ d < K` by induction, so `|S| ≤ q ^ (d + 1) (K - 1) ≤ q (K - 1) ^ 2 < q K ^ 2`.
    have hd' : q ^ d ≤ K - 1 := by
      by_contra! h
      exact ih (by omega) (by omega) (hsmall d (by omega) (by omega))
    have : q ^ (d + 1) * (K - 1) ≤ q * ((K - 1) * (K - 1)) := by
      rw [pow_succ', mul_assoc]; gcongr
    have : (K - 1) * (K - 1) < K ^ 2 := by
      rw [sq]; exact Nat.mul_lt_mul'' (by omega) (by omega)
    nlinarith

end Finite

end RectangleFree

end Cslib.Circuits.Frontier
