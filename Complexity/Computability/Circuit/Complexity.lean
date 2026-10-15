/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (additions to `Cslib/Computability/Circuit/Complexity.lean`)

public import Cslib.Computability.Circuit.Complexity
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Computing several functions side by side

Computing `m` functions of the same inputs at once costs at most the sum of their complexities:
the circuits are placed next to each other.

## Main results

* `Cslib.Circuits.ecomplexity_pi_le`, `Cslib.Circuits.complexity_pi_le`.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {U : Type*} {I : Interpretation σ U} {n : ℕ}

/-- Computing `m` functions side by side costs at most the sum of their complexities. -/
theorem ecomplexity_pi_le : ∀ {m : ℕ} (f : Fin m → (Fin n → U) → U),
    ecomplexity I (fun x i => f i x) ≤ ∑ i, ecomplexity I (single (f i))
  | 0, f => by
    have : (fun x (i : Fin 0) => f i x) = fun x => x ∘ (Fin.elim0 : Fin 0 → Fin n) :=
      funext fun _ => funext fun i => i.elim0
    rw [this, ecomplexity_wiring]
    exact bot_le
  | m + 1, f => by
    have : (fun x (i : Fin (m + 1)) => f i x) =
        fun x => Fin.append (fun i : Fin m => f i.castSucc x) (single (f (Fin.last m)) x) := by
      funext x i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp [single, Fin.append, Fin.addCases, Fin.last]
      · simp [Fin.append, Fin.addCases]
    rw [this, Fin.sum_univ_castSucc]
    exact (ecomplexity_append_le _ _).trans (add_le_add (ecomplexity_pi_le _) le_rfl)

/-- Computing `m` functions side by side costs at most the sum of their complexities. -/
theorem complexity_pi_le [I.IsComplete] {m : ℕ} (f : Fin m → (Fin n → U) → U) :
    complexity I (fun x i => f i x) ≤ ∑ i, complexity I (single (f i)) := by
  have h := ecomplexity_pi_le (I := I) f
  simp only [← natCast_complexity] at h
  exact_mod_cast h

end Cslib.Circuits
