/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Basic
public import Cslib.Computability.Circuit.Boolean.Complexity
public import Cslib.Computability.Circuit.Boolean.Counting
public import Mathlib.Data.Set.Card

/-!
# The Minimum Circuit Size Problem

The *Minimum Circuit Size Problem* (MCSP) asks, given the truth table of a Boolean function `f`
on `n` inputs and a number `s`, whether `f` has a circuit with at most `s` gates
[KabanetsCai2000]. Its gap version `GapMCSP[s₁, s₂]` is the promise problem of telling, for each
`n`, the truth tables of functions with circuits of at most `s₁ n` gates from those of functions
that need more than `s₂ n` gates [OliveiraPichSanthanam2019, Definition 2.4].

The truth table of `f` lists its `2 ^ n` values in the order of `BitString.equivFin`. Circuits are
De Morgan circuits, and their size counts every AND, OR, NOT and constant gate, so the measure is
cslib's `complexity interpretation (single f)`; see `Cslib.Computability.Circuit.Boolean.Basic`.
Only the semantics of the problems is defined here, not an encoding of their instances as
strings, so nothing is said about their computational complexity.

The yes-instances of MCSP on functions of `n` inputs at threshold `s` are the truth tables of
cslib's `computableFunctions n s`, so there are as many of them as such functions
(`MCSP.ncard_setOf_mem`).

## Main definitions

* `Cslib.MCSP.truthTable`: truth tables of Boolean functions.
* `Cslib.MCSP.Instance`, `Cslib.MCSP`: the instances and the yes-instances of MCSP.
* `Cslib.GapMCSP.yes`, `Cslib.GapMCSP.no`: the two sides of `GapMCSP[s₁, s₂]`.

## Main results

* `Cslib.MCSP.mem_iff_exists_circuit`, `Cslib.MCSP.mem_iff_mem_computableFunctions`: the yes-
  instances of MCSP, as circuits and as computable functions.
* `Cslib.MCSP.ncard_setOf_mem`: the number of yes-instances of a given arity and threshold.
* `Cslib.GapMCSP.disjoint_yes_no`: the promise of `GapMCSP[s₁, s₂]` is consistent when
  `s₁ ≤ s₂`, and `Cslib.GapMCSP.no_eq_compl_yes`: `GapMCSP[s, s]` is MCSP at threshold `s`.

## References

* [V. Kabanets, J.-Y. Cai, *Circuit minimization problem*][KabanetsCai2000]
* [I. C. Oliveira, J. Pich, R. Santhanam, *Hardness magnification near state-of-the-art lower
  bounds*][OliveiraPichSanthanam2019]
-/

@[expose] public section

namespace Cslib

open Circuits Circuits.Boolean

namespace MCSP

variable {n : ℕ}

variable (n) in
/-- The truth table of a Boolean function on `n` inputs: its values on the `2 ^ n` inputs, in the
order of `BitString.equivFin`. -/
def truthTable : BooleanFunction n ≃ BitString (2 ^ n) where
  toFun f i := f ((BitString.equivFin n).symm i)
  invFun T x := T (BitString.equivFin n x)
  left_inv f := funext fun x => by simp
  right_inv T := funext fun i => by simp

@[simp] theorem truthTable_apply (f : BooleanFunction n) (i : Fin (2 ^ n)) :
    truthTable n f i = f ((BitString.equivFin n).symm i) :=
  rfl

@[simp] theorem truthTable_symm_apply (T : BitString (2 ^ n)) (x : BitString n) :
    (truthTable n).symm T x = T (BitString.equivFin n x) :=
  rfl

/-- An instance of the Minimum Circuit Size Problem: the truth table of a Boolean function on
`arity` inputs, and a size threshold. -/
structure Instance where
  /-- The number of inputs of the function. -/
  arity : ℕ
  /-- The truth table of the function. -/
  table : BitString (2 ^ arity)
  /-- The number of gates allowed. -/
  threshold : ℕ

/-- The Boolean function whose truth table an instance gives. -/
def Instance.function (x : Instance) : BooleanFunction x.arity :=
  (truthTable x.arity).symm x.table

end MCSP

open MCSP

/-- **The Minimum Circuit Size Problem** [KabanetsCai2000]: the instances whose function has a
De Morgan circuit with at most `threshold` gates. -/
def MCSP : Set MCSP.Instance :=
  {x | complexity interpretation (single x.function) ≤ x.threshold}

namespace MCSP

variable {n s t : ℕ}

theorem mem_iff {x : Instance} :
    x ∈ MCSP ↔ complexity interpretation (single x.function) ≤ x.threshold :=
  Iff.rfl

/-- The truth table of `f` with threshold `s` is a yes-instance exactly when `f` has complexity at
most `s`. -/
@[simp] theorem mk_truthTable_mem_iff {f : BooleanFunction n} :
    ⟨n, truthTable n f, s⟩ ∈ MCSP ↔ complexity interpretation (single f) ≤ s := by
  simp [mem_iff, Instance.function]

/-- The truth table of `f` with threshold `s` is a yes-instance exactly when `f` is computable
with at most `s` gates. -/
theorem mk_truthTable_mem_iff_mem {f : BooleanFunction n} :
    ⟨n, truthTable n f, s⟩ ∈ MCSP ↔ f ∈ computableFunctions n s := by
  rw [mk_truthTable_mem_iff, mem_computableFunctions_iff_ecomplexity_le, ← natCast_complexity]
  exact Nat.cast_le.symm

/-- An instance is a yes-instance exactly when some circuit with at most `threshold` gates
computes its function. -/
theorem mem_iff_exists_circuit {x : Instance} :
    x ∈ MCSP ↔ ∃ c : Circuit signature x.arity 1,
      c.Computes interpretation (single x.function) ∧ c.size ≤ x.threshold :=
  complexity_le_iff

/-- The yes-instances are the truth tables of the functions computable within the threshold. -/
theorem mem_iff_mem_computableFunctions {x : Instance} :
    x ∈ MCSP ↔ x.function ∈ computableFunctions x.arity x.threshold := by
  rw [mem_iff_exists_circuit, mem_computableFunctions]

/-- Raising the threshold keeps a yes-instance a yes-instance. -/
theorem mem_of_le {T : BitString (2 ^ n)} (h : ⟨n, T, s⟩ ∈ MCSP) (hst : s ≤ t) :
    ⟨n, T, t⟩ ∈ MCSP :=
  le_trans h hst

/-- There are as many yes-instances of arity `n` and threshold `s` as functions on `n` inputs
computable with at most `s` gates. -/
theorem ncard_setOf_mem (n s : ℕ) :
    {T : BitString (2 ^ n) | ⟨n, T, s⟩ ∈ MCSP}.ncard = (computableFunctions n s).card := by
  have h : {T : BitString (2 ^ n) | ⟨n, T, s⟩ ∈ MCSP} =
      truthTable n '' (computableFunctions n s : Set (BooleanFunction n)) := by
    ext T
    obtain ⟨f, rfl⟩ := (truthTable n).surjective T
    simp [complexity_le_iff]
  rw [h, Set.ncard_image_of_injective _ (truthTable n).injective, Set.ncard_coe_finset]

end MCSP

namespace GapMCSP

open MCSP

variable {s₁ s₂ : ℕ → ℕ} {n : ℕ}

/-- The yes-instances of `GapMCSP[s₁, s₂]` on functions of `n` inputs: the truth tables of
functions with circuits of at most `s₁ n` gates [OliveiraPichSanthanam2019, Definition 2.4]. -/
def yes (s₁ : ℕ → ℕ) (n : ℕ) : Set (BitString (2 ^ n)) :=
  {T | complexity interpretation (single ((truthTable n).symm T)) ≤ s₁ n}

/-- The no-instances of `GapMCSP[s₁, s₂]` on functions of `n` inputs: the truth tables of
functions that need more than `s₂ n` gates [OliveiraPichSanthanam2019, Definition 2.4]. -/
def no (s₂ : ℕ → ℕ) (n : ℕ) : Set (BitString (2 ^ n)) :=
  {T | s₂ n < complexity interpretation (single ((truthTable n).symm T))}

/-- The yes-instances of `GapMCSP[s₁, s₂]` are those of MCSP at threshold `s₁ n`. -/
theorem mem_yes_iff {T : BitString (2 ^ n)} : T ∈ yes s₁ n ↔ ⟨n, T, s₁ n⟩ ∈ MCSP :=
  Iff.rfl

/-- The no-instances of `GapMCSP[s₁, s₂]` are the truth tables that are not yes-instances of
MCSP at threshold `s₂ n`. -/
theorem no_eq_compl_yes (s₂ : ℕ → ℕ) (n : ℕ) : no s₂ n = (yes s₂ n)ᶜ := by
  ext T
  simp [yes, no]

/-- The promise of `GapMCSP[s₁, s₂]` is consistent: when `s₁ n ≤ s₂ n`, no truth table is both a
yes-instance and a no-instance. -/
theorem disjoint_yes_no (h : s₁ n ≤ s₂ n) : Disjoint (yes s₁ n) (no s₂ n) :=
  Set.disjoint_left.mpr fun _ hyes hno => (lt_irrefl _) ((hyes.trans h).trans_lt hno)

/-- Raising the yes-threshold adds yes-instances. -/
theorem yes_mono {s₁' : ℕ → ℕ} (h : s₁ n ≤ s₁' n) : yes s₁ n ⊆ yes s₁' n :=
  fun _ hT => le_trans hT h

/-- Raising the no-threshold removes no-instances. -/
theorem no_anti {s₂' : ℕ → ℕ} (h : s₂ n ≤ s₂' n) : no s₂' n ⊆ no s₂ n :=
  fun _ hT => lt_of_le_of_lt h hT

end GapMCSP

end Cslib
