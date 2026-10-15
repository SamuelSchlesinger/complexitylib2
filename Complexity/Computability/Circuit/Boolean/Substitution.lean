/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Synthesis

/-!
# Substituting variables and constants for inputs

A *substitution* `ρ : Fin N → Fin n ⊕ Bool` feeds every input of a Boolean function of `N`
variables from one of `n` new variables or from a constant; several inputs may receive the same
variable, so this is a projection in Valiant's sense rather than a restriction, which would leave
the remaining inputs free. A substitution does not make a function harder to compute: a circuit for
`f` with its inputs rewired, and two gates for the constants, computes `f ∘ ρ`.

The substitution `appendInputs r` fixes the last `p` inputs of a function of `n + p` variables to
the bits `r`: substituting it computes `x ↦ f (Fin.append x r)`.

## Main definitions

* `Cslib.Circuits.Boolean.substitute`, `Cslib.Circuits.Boolean.appendInputs`.

## Main results

* `Cslib.Circuits.Boolean.complexity_substitute_le`: a substitution costs at most two gates.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

variable {n N : ℕ}

/-- The inputs of a function of `N` variables fed by `ρ` from the variables `x`: input `j` is
`x i` when `ρ j = .inl i`, and the constant `b` when `ρ j = .inr b`. -/
def substitute (ρ : Fin N → Fin n ⊕ Bool) (x : Fin n → Bool) : Fin N → Bool :=
  fun j => (ρ j).elim x id

@[simp] theorem substitute_inl {ρ : Fin N → Fin n ⊕ Bool} {x : Fin n → Bool} {j : Fin N}
    {i : Fin n} (h : ρ j = .inl i) : substitute ρ x j = x i := by
  simp [substitute, h]

@[simp] theorem substitute_inr {ρ : Fin N → Fin n ⊕ Bool} {x : Fin n → Bool} {j : Fin N}
    {b : Bool} (h : ρ j = .inr b) : substitute ρ x j = b := by
  simp [substitute, h]

/-- A substitution costs at most two gates, one for each constant. -/
theorem complexity_substitute_le_two (ρ : Fin N → Fin n ⊕ Bool) :
    complexity interpretation (substitute ρ) ≤ 2 := by
  have h : Synthesis interpretation (inputs n) (Set.range fun j x => substitute ρ x j)
      (1 + 1 + 0) :=
    ((Synthesis.const false).union (Synthesis.const true)).trans <| Synthesis.of_subset <| by
      rintro _ ⟨j, rfl⟩
      rcases hj : ρ j with i | b
      · exact Or.inl ⟨i, funext fun x => (substitute_inl hj).symm⟩
      · refine Or.inr ?_
        cases b
        · exact Or.inl (funext fun x => substitute_inr hj)
        · exact Or.inr (funext fun x => substitute_inr hj)
  obtain ⟨c, hc, hsize⟩ := h.exists_circuit_outputs
  exact (complexity_le_of_computes c hc).trans hsize

/-- **Substitutions do not make functions harder.** Feeding the inputs of `f` from variables and
constants costs at most two more gates than `f`. -/
theorem complexity_substitute_le (ρ : Fin N → Fin n ⊕ Bool) (f : BooleanFunction N) :
    complexity interpretation (single fun x => f (substitute ρ x)) ≤
      complexity interpretation (single f) + 2 := by
  have h := complexity_comp_le (I := interpretation) (substitute ρ) (single f)
  rw [add_comm] at h
  exact h.trans (Nat.add_le_add_left (complexity_substitute_le_two ρ) _)

/-- The substitution fixing the last `p` inputs of a function of `n + p` variables to `r`. -/
def appendInputs {p : ℕ} (r : Fin p → Bool) : Fin (n + p) → Fin n ⊕ Bool :=
  Fin.append Sum.inl (Sum.inr ∘ r)

@[simp] theorem substitute_appendInputs {p : ℕ} (r : Fin p → Bool) (x : Fin n → Bool) :
    substitute (appendInputs r) x = Fin.append x r := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [substitute, appendInputs]

end Cslib.Circuits.Boolean
