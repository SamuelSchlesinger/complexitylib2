/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Majority

/-!
# TC⁰

**TC⁰** is the class of languages decided, at every input length, by circuits of polynomial size
and constant depth whose gates are negations, conjunctions and disjunctions of unbounded fan-in,
and majority gates of unbounded fan-in [Arora and Barak, Chapter 14][AroraBarak09]. Every AC⁰
circuit is a TC⁰ circuit (`AC0_subset_TC0`), and majority is a single gate, so majority is in TC⁰
(`majority_mem_TC0`) but not in AC⁰: **AC⁰ is strictly contained in TC⁰** (`AC0_ssubset_TC0`).
Parity reduces to majority in constant depth, so parity is in TC⁰ too (`parity_mem_TC0`).

## Main definitions

* `Cslib.Circuits.Boolean.MajorityBasis.signature`: the AC⁰ basis with majority gates.
* `Cslib.Circuits.Boolean.MajorityBasis.TC0`: the class TC⁰.

## Main results

* `Cslib.Circuits.Boolean.MajorityBasis.AC0_ssubset_TC0`: `AC⁰ ⊊ TC⁰`.
* `Cslib.Circuits.Boolean.MajorityBasis.parity_mem_TC0`: parity is in TC⁰.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.MajorityBasis

/-- The operations of the AC⁰ basis, and majority of `m` arguments for every `m`. -/
inductive Op where
  /-- An operation of the AC⁰ basis. -/
  | ac (op : Unbounded.Op)
  /-- Majority of `m` arguments. -/
  | maj (m : ℕ)
  deriving DecidableEq

/-- The arity of an operation. -/
abbrev Op.arity : Op → ℕ
  | .ac op => op.arity
  | .maj m => m

/-- The signature of the AC⁰ basis with majority gates. It is reducible, so that case analysis on
its operations sees their arities. -/
abbrev signature : Signature :=
  ⟨Op, Op.arity⟩

/-- The Boolean meaning of the operations. -/
def interpretation : Interpretation signature Bool
  | .ac op, x => Unbounded.interpretation op x
  | .maj m, x => majority m x

/-- The AC⁰ basis inside the basis with majority gates. -/
def ofUnbounded : Unbounded.signature.Hom signature :=
  ⟨Op.ac, fun _ => rfl⟩

/-- **TC⁰**: the languages over `Bool` decided, at every input length, by circuits with majority
gates of polynomially bounded size and constant depth. -/
def TC0 : Set (Language Bool) :=
  ConstDepth interpretation

/-- **AC⁰ ⊆ TC⁰**: every AC⁰ circuit is a circuit with majority gates. -/
theorem AC0_subset_TC0 : Unbounded.AC0 ⊆ TC0 :=
  ConstDepth.mono (φ := ofUnbounded) fun _ _ => rfl

/-- **Majority is in TC⁰**: it is a single gate. -/
theorem majority_mem_TC0 : Language.ofSlices majority ∈ TC0 := by
  refine ⟨1, fun _ => 1, by fun_prop, fun n => ⟨Circuit.oneGate (σ := signature) (.maj n) id,
    fun x => ?_, Circuit.depth_oneGate_le _ _, le_rfl⟩⟩
  funext j
  rw [Language.slice_ofSlices]
  rfl

/-- **Parity is in TC⁰**: it reduces to majority in constant depth. -/
theorem parity_mem_TC0 : Language.ofSlices parity ∈ TC0 :=
  Unbounded.parity_mem_of_majority_mem (φ := ofUnbounded) (fun _ _ => rfl) majority_mem_TC0

/-- **AC⁰ is strictly contained in TC⁰.** -/
theorem AC0_ssubset_TC0 : Unbounded.AC0 ⊂ TC0 :=
  Set.ssubset_iff_of_subset AC0_subset_TC0 |>.2
    ⟨_, majority_mem_TC0, Unbounded.majority_notMem_AC0⟩

end Cslib.Circuits.Boolean.MajorityBasis
