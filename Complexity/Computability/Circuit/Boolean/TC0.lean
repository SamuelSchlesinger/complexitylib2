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
and majority gates of unbounded fan-in [Vollmer, Chapter 4][Vollmer1999]: the unbounded fan-in
basis extended by majority (`Unbounded.extInterpretation majority`). Every AC⁰ circuit is a TC⁰
circuit (`AC0_subset_TC0`), and majority is a single gate, so majority is in TC⁰
(`majority_mem_TC0`) but not in AC⁰: **AC⁰ is strictly contained in TC⁰** (`AC0_ssubset_TC0`).
Parity reduces to majority in constant depth, so parity is in TC⁰ too (`parity_mem_TC0`).

## Main definitions

* `Cslib.Circuits.Boolean.TC0`: the class TC⁰.

## Main results

* `Cslib.Circuits.Boolean.AC0_ssubset_TC0`: `AC⁰ ⊊ TC⁰`.
* `Cslib.Circuits.Boolean.parity_mem_TC0`: parity is in TC⁰.

## References

* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

/-- **TC⁰**: the languages over `Bool` decided, at every input length, by circuits with majority
gates of polynomially bounded size and constant depth. -/
def TC0 : Set (Language Bool) :=
  ConstDepth (Unbounded.extInterpretation majority)

/-- **AC⁰ ⊆ TC⁰**: every AC⁰ circuit is a circuit with majority gates. -/
theorem AC0_subset_TC0 : AC0 ⊆ TC0 :=
  ConstDepth.mono Unbounded.toExt

/-- **Majority is in TC⁰**: it is a single gate. -/
theorem majority_mem_TC0 : Language.ofSlices majority ∈ TC0 := by
  refine ConstDepth.mem_iff.2 ⟨1, fun _ => 1, by fun_prop, fun n =>
    ⟨Circuit.oneGate (σ := Unbounded.extSignature) (.gate n) id, fun x => ?_,
      (Circuit.depth_oneGate _ _).le, le_rfl⟩⟩
  funext j
  rw [Language.slice_ofSlices]
  rfl

/-- **Parity is in TC⁰**: it reduces to majority in constant depth. -/
theorem parity_mem_TC0 : Language.ofSlices parity ∈ TC0 :=
  ConstDepth.parity_mem_of_majority_mem Unbounded.toExt majority_mem_TC0

/-- **AC⁰ is strictly contained in TC⁰.** -/
theorem AC0_ssubset_TC0 : AC0 ⊂ TC0 :=
  Set.ssubset_iff_of_subset AC0_subset_TC0 |>.2 ⟨_, majority_mem_TC0, majority_notMem_AC0⟩

end Cslib.Circuits.Boolean
