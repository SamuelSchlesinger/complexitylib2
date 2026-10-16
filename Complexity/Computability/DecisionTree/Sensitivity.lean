/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Complexity.Foundations.Data.BitString.Flip
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Sensitivity, block sensitivity and certificates

For a function `f` of Boolean variables and an input `x`:

* the *sensitivity* `sensitivityAt f x` is the number of variables whose flip changes `f x`
  (`BitString.sensitivityAt`);
* the *block sensitivity* `blockSensitivityAt f x` is the largest number of pairwise disjoint
  blocks of variables each of whose flip changes `f x`;
* the *certificate complexity* `certificateComplexityAt f x` is the least size of a set of
  variables whose values at `x` determine `f x`.

Each is at most the next, and the variables queried on the way to the leaf of `x` are a
certificate, so all three are at most the decision tree complexity
(`sensitivity_le_blockSensitivity`, `blockSensitivity_le_certificateComplexity`,
`certificateComplexity_le_complexity`) [Nisan1991], [Jukna, Section 14.3][Jukna2012].

## Main definitions

* `Cslib.DecisionTree.blockSensitivityAt`, `Cslib.DecisionTree.blockSensitivity`.
* `Cslib.DecisionTree.IsCertificate`, `Cslib.DecisionTree.certificateComplexityAt`,
  `Cslib.DecisionTree.certificateComplexity`.

## Main results

* `Cslib.DecisionTree.sensitivity_le_blockSensitivity`,
  `Cslib.DecisionTree.blockSensitivity_le_certificateComplexity`,
  `Cslib.DecisionTree.certificateComplexity_le_complexity`: `s(f) ≤ bs(f) ≤ C(f) ≤ D(f)`.

## References

* [N. Nisan, *CREW PRAMs and decision trees*][Nisan1991]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.DecisionTree

open Finset BitString

variable {ι β : Type*}

section Certificate

/-- `S` is a certificate for `f` at `x`: the values of `x` on `S` determine `f x`. -/
def IsCertificate (f : (ι → Bool) → β) (x : ι → Bool) (S : Finset ι) : Prop :=
  ∀ y, (∀ i ∈ S, y i = x i) → f y = f x

/-- The least size of a certificate for `f` at `x`. -/
noncomputable def certificateComplexityAt (f : (ι → Bool) → β) (x : ι → Bool) : ℕ :=
  sInf {k | ∃ S, IsCertificate f x S ∧ #S ≤ k}

variable {f : (ι → Bool) → β} {x : ι → Bool}

theorem certificateComplexityAt_le {S : Finset ι} (hS : IsCertificate f x S) :
    certificateComplexityAt f x ≤ #S :=
  Nat.sInf_le ⟨S, hS, le_rfl⟩

theorem isCertificate_univ [Fintype ι] (f : (ι → Bool) → β) (x : ι → Bool) :
    IsCertificate f x univ :=
  fun _ hy => congrArg f (funext fun i => hy i (mem_univ i))

theorem exists_isCertificate_card_eq [Finite ι] (f : (ι → Bool) → β) (x : ι → Bool) :
    ∃ S, IsCertificate f x S ∧ #S = certificateComplexityAt f x := by
  have := Fintype.ofFinite ι
  obtain ⟨S, hS, hle⟩ := Nat.sInf_mem (s := {k | ∃ S, IsCertificate f x S ∧ #S ≤ k})
    ⟨_, univ, isCertificate_univ f x, le_rfl⟩
  exact ⟨S, hS, le_antisymm hle (certificateComplexityAt_le hS)⟩

/-- Certificate complexity at an input is at most the depth of any tree computing the function:
the variables it queries certify the output. -/
theorem certificateComplexityAt_le_depth {t : DecisionTree ι β} (ht : t.Computes f)
    (x : ι → Bool) : certificateComplexityAt f x ≤ t.depth := by
  classical
  exact (certificateComplexityAt_le fun y hy => (ht y).symm.trans
    ((t.eval_eq_of_forall_mem_queries hy).trans (ht x))).trans (t.card_queries_le_depth x)

end Certificate

variable [DecidableEq ι]

variable [Fintype ι] [DecidableEq β]

/-- The families of pairwise disjoint blocks each of whose flip changes `f x`. -/
def sensitiveFamilies (f : (ι → Bool) → β) (x : ι → Bool) : Finset (Finset (Finset ι)) :=
  {F | (∀ B ∈ F, ∀ C ∈ F, B ≠ C → Disjoint B C) ∧ ∀ B ∈ F, f (BitString.flipOn B x) ≠ f x}

/-- The largest number of pairwise disjoint blocks each of whose flip changes `f x`. -/
def blockSensitivityAt (f : (ι → Bool) → β) (x : ι → Bool) : ℕ :=
  (sensitiveFamilies f x).sup card

/-- The block sensitivity of `f`: its largest block sensitivity at an input. -/
def blockSensitivity (f : (ι → Bool) → β) : ℕ :=
  univ.sup (blockSensitivityAt f)

/-- The certificate complexity of `f`: its largest certificate complexity at an input. -/
noncomputable def certificateComplexity (f : (ι → Bool) → β) : ℕ :=
  univ.sup (certificateComplexityAt f)

variable {f : (ι → Bool) → β} {x : ι → Bool}

@[simp] theorem mem_sensitiveFamilies {F : Finset (Finset ι)} :
    F ∈ sensitiveFamilies f x ↔
      (∀ B ∈ F, ∀ C ∈ F, B ≠ C → Disjoint B C) ∧ ∀ B ∈ F, f (BitString.flipOn B x) ≠ f x := by
  simp [sensitiveFamilies]

/-- Sensitivity at an input is at most block sensitivity there: sensitive variables are
sensitive blocks. -/
theorem sensitivityAt_le_blockSensitivityAt (f : (ι → Bool) → β) (x : ι → Bool) :
    sensitivityAt f x ≤ blockSensitivityAt f x := by
  have hmem : ({i | f (Function.update x i !x i) ≠ f x} : Finset ι).map
      ⟨fun i => ({i} : Finset ι), singleton_injective⟩ ∈ sensitiveFamilies f x := by
    refine mem_sensitiveFamilies.2 ⟨fun B hB C hC hBC => ?_, fun B hB => ?_⟩
    · obtain ⟨i, -, rfl⟩ := mem_map.1 hB
      obtain ⟨j, -, rfl⟩ := mem_map.1 hC
      simpa using fun h : i = j => hBC (by rw [h])
    · obtain ⟨i, hi, rfl⟩ := mem_map.1 hB
      simpa using (mem_filter.1 hi).2
  exact (card_map _).symm.trans_le (le_sup (f := card) hmem)

/-- A certificate meets every sensitive block, so disjoint sensitive blocks are at most as many as
the variables of a certificate. -/
theorem IsCertificate.card_le_of_mem_sensitiveFamilies {S : Finset ι} (hS : IsCertificate f x S)
    {F : Finset (Finset ι)} (hF : F ∈ sensitiveFamilies f x) : #F ≤ #S := by
  rw [mem_sensitiveFamilies] at hF
  refine card_le_card_of_forall_subsingleton (fun B i => i ∈ B) (fun B hB => ?_)
    fun i _ B hB C hC => by_contra fun hne => disjoint_left.1 (hF.1 B hB.1 C hC.1 hne) hB.2 hC.2
  by_contra! h
  exact hF.2 B hB (hS _ fun i hi => by simp [BitString.flipOn, fun hiB => h i hi hiB])

/-- Block sensitivity at an input is at most certificate complexity there. -/
theorem blockSensitivityAt_le_certificateComplexityAt (f : (ι → Bool) → β) (x : ι → Bool) :
    blockSensitivityAt f x ≤ certificateComplexityAt f x := by
  obtain ⟨S, hS, hcard⟩ := exists_isCertificate_card_eq f x
  exact hcard ▸ Finset.sup_le fun F hF => hS.card_le_of_mem_sensitiveFamilies hF

theorem sensitivity_le_blockSensitivity (f : (ι → Bool) → β) :
    sensitivity f ≤ blockSensitivity f :=
  sup_mono_fun fun x _ => sensitivityAt_le_blockSensitivityAt f x

theorem blockSensitivity_le_certificateComplexity (f : (ι → Bool) → β) :
    blockSensitivity f ≤ certificateComplexity f :=
  sup_mono_fun fun x _ => blockSensitivityAt_le_certificateComplexityAt f x

omit [DecidableEq β] in
/-- Certificate complexity is at most decision tree complexity. -/
theorem certificateComplexity_le_complexity (f : (ι → Bool) → β) :
    certificateComplexity f ≤ complexity f := by
  obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity f
  exact Finset.sup_le fun x _ => (certificateComplexityAt_le_depth ht x).trans hd.le

/-- A lower bound on sensitivity at one input is a lower bound on decision tree complexity. -/
theorem sensitivityAt_le_complexity (f : (ι → Bool) → β) (x : ι → Bool) :
    sensitivityAt f x ≤ complexity f :=
  (le_sup (f := sensitivityAt f) (mem_univ x)).trans <|
    (sensitivity_le_blockSensitivity f).trans <|
      (blockSensitivity_le_certificateComplexity f).trans (certificateComplexity_le_complexity f)

/-- A function sensitive to every variable at some input needs to query all of them. -/
theorem complexity_eq_card_of_sensitivityAt_eq_card (h : sensitivityAt f x = Fintype.card ι) :
    complexity f = Fintype.card ι :=
  le_antisymm (complexity_le_card f) (h ▸ sensitivityAt_le_complexity f x)

end Cslib.DecisionTree
