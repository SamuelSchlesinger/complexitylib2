/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Fusion.Cyclic.Closure

/-!
# Semifilter closure clients

A single pair generates an intersection cover on arbitrary, possibly infinite carriers.
The universal and empty targets admit zero-pair covers even with no inputs. A nontrivial
generated semifilter need not satisfy the complementary-set condition.
-/

namespace ComplexityTests.FusionClosure

open Cslib.Circuits.Fusion

private def interCover {U : Type*} (A B : Set U) : PairCover (A ∩ B) ![A, B] :=
  PairCover.ofDerivesEmpty [(Subtype.val ⁻¹' A, Subtype.val ⁻¹' B)] fun point hx =>
    (PairDerivation.inter (Subtype.val ⁻¹' A, Subtype.val ⁻¹' B) (by simp)
      (.input 0 hx.1) (.input 1 hx.2)).mono
      (fun y hy => (y.property hy).elim)

example {U : Type*} (A B : Set U) : (interCover A B).pairs.length = 1 := rfl

example {U : Type*} (A B : Set U) :
    pairClosure (A ∩ B) ![A, B] (interCover A B).pairs ∅ = A ∩ B :=
  (interCover A B).pairClosure_empty

-- The characterization also applies directly on an infinite carrier.
example (n : ℕ) :
    PairDerivation ({n : ℕ | 2 ∣ n} ∩ {n : ℕ | 3 ∣ n})
      ![{n : ℕ | 2 ∣ n}, {n : ℕ | 3 ∣ n}]
      (interCover {n : ℕ | 2 ∣ n} {n : ℕ | 3 ∣ n}).pairs n ∅ ↔ 2 ∣ n ∧ 3 ∣ n :=
  (interCover _ _).derives_empty_iff n

private def topCover {U : Type*} : PairCover (Set.univ : Set U) Fin.elim0 :=
  PairCover.ofDerivesEmpty [] fun _ _ =>
    PairDerivation.univ.mono (fun y _ => (y.property (Set.mem_univ y.val)).elim)

example {U : Type*} : (topCover (U := U)).pairs = [] := rfl

example {U : Type*} : pairClosure Set.univ (Fin.elim0 : Fin 0 → Set U) [] ∅ = Set.univ :=
  (topCover (U := U)).pairClosure_empty

private def bottomCover {U : Type*} : PairCover (∅ : Set U) Fin.elim0 :=
  PairCover.ofDerivesEmpty [] fun _ h => h.elim

example {U : Type*} : pairClosure ∅ (Fin.elim0 : Fin 0 → Set U) [] ∅ = ∅ :=
  (bottomCover (U := U)).pairClosure_empty

-- With no inputs or pairs, only the full complement can be derived.
private theorem noInput_derives_iff {U : Type*} (target : Set U) (point : U)
    (s : Set ↥(targetᶜ)) : PairDerivation target (Fin.elim0 : Fin 0 → Set U) [] point s ↔
      s = Set.univ := by
  refine ⟨fun h => Set.eq_univ_of_univ_subset ?_, fun h => h ▸ PairDerivation.univ⟩
  exact PairDerivation.le (P := fun s => Set.univ ⊆ s) Set.Subset.rfl (fun i => i.elim0)
    (fun _ _ hst hs => hs.trans hst) (fun _ h => (List.not_mem_nil h).elim) s h

private def fullOnly : Semifilter ↥((∅ : Set Bool)ᶜ) :=
  PairDerivation.semifilter (target := ∅) (input := Fin.elim0) (pairs := []) (point := false)
    (fun h => by
      have hs := (noInput_derives_iff ∅ false ∅).mp h
      have : (⟨false, by simp⟩ : ↥((∅ : Set Bool)ᶜ)) ∈ (∅ : Set ↥((∅ : Set Bool)ᶜ)) :=
        hs ▸ Set.mem_univ _
      exact this)

example : ¬ fullOnly.IsUltra := by
  intro h
  rcases h {x | x.val = true} with htrue | hfalse
  · have hs := (noInput_derives_iff ∅ false _).mp htrue
    have := congrArg (fun s : Set ↥((∅ : Set Bool)ᶜ) => (⟨false, by simp⟩ : _) ∈ s) hs
    simp at this
  · have hs := (noInput_derives_iff ∅ false _).mp hfalse
    have := congrArg (fun s : Set ↥((∅ : Set Bool)ᶜ) => (⟨true, by simp⟩ : _) ∈ s) hs
    simp at this

end ComplexityTests.FusionClosure
