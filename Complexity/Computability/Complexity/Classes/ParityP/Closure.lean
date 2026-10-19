/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.ParityP
public import Mathlib.Data.Set.SymmDiff
import Complexity.Computability.Complexity.Classes.SharpP.Closure

/-!
# Boolean closure of ParityP

## Main results

`ParityP` is closed under union, intersection and symmetric difference.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open scoped symmDiff

variable {α : Type} {enc : α ↪ List Bool} {A B : Set α}

/-- `⊕P` is closed under intersection. -/
theorem inter_mem_ParityP (hA : A ∈ ParityP enc) (hB : B ∈ ParityP enc) :
    A ∩ B ∈ ParityP enc := by
  obtain ⟨f, hf, hA⟩ := mem_ParityP_iff_exists_SharpP.mp hA
  obtain ⟨g, hg, hB⟩ := mem_ParityP_iff_exists_SharpP.mp hB
  exact mem_ParityP_iff_exists_SharpP.mpr
    ⟨f * g, SharpP.mul_mem hf hg, fun a => by simp [hA a, hB a, Nat.odd_mul]⟩

/-- `⊕P` is closed under union. -/
theorem union_mem_ParityP (hA : A ∈ ParityP enc) (hB : B ∈ ParityP enc) :
    A ∪ B ∈ ParityP enc := by
  simpa [Set.compl_inter] using
    compl_mem_ParityP (inter_mem_ParityP (compl_mem_ParityP hA) (compl_mem_ParityP hB))

/-- `⊕P` is closed under symmetric difference. -/
theorem symmDiff_mem_ParityP (hA : A ∈ ParityP enc) (hB : B ∈ ParityP enc) :
    A ∆ B ∈ ParityP enc := by
  obtain ⟨f, hf, hA⟩ := mem_ParityP_iff_exists_SharpP.mp hA
  obtain ⟨g, hg, hB⟩ := mem_ParityP_iff_exists_SharpP.mp hB
  refine mem_ParityP_iff_exists_SharpP.mpr ⟨f + g, SharpP.add_mem hf hg, fun a => ?_⟩
  simp only [Set.mem_symmDiff, hA a, hB a, Pi.add_apply, Nat.odd_add, ← Nat.not_odd_iff_even]
  tauto

end Cslib.Complexity
