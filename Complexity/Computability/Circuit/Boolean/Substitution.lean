/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Formula
public import Complexity.Computability.Circuit.Boolean.Synthesis
public import Complexity.Foundations.Data.BitString.PartialAssignment

/-!
# Substituting variables and constants for inputs

A *substitution* `ρ : Fin N → Fin n ⊕ Bool` feeds every input of a Boolean function of `N`
variables from one of `n` new variables or from a constant; several inputs may receive the same
variable, so this is a projection in Valiant's sense rather than a restriction, which would leave
the remaining inputs free. A substitution does not make a function harder to compute: a circuit for
`f` with its inputs rewired, and two gates for the constants, computes `f ∘ ρ`.

The substitution `appendInputs r` fixes the last `p` inputs of a function of `n + p` variables to
the bits `r`: substituting it computes `x ↦ f (Fin.append x r)`. A restriction (partial
assignment) is the substitution that replaces each bit by itself or by a constant
(`BitString.PartialAssignment.substitute_toSubstitution`).

## Main definitions

* `Cslib.Circuits.Boolean.substitute`, `Cslib.Circuits.Boolean.appendInputs`.
* `Cslib.Circuits.Boolean.substituteCircuit`: executable substitution with two shared constants.
* `Cslib.BitString.PartialAssignment.toSubstitution`: a partial assignment as a substitution.

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

/-- Implement a substitution using one shared gate for each Boolean constant.
Both gates are included even when unused or when the output is empty. -/
def substituteCircuit {n N : ℕ} (ρ : Fin N → Fin n ⊕ Bool) : Circuit signature n N :=
  (Circuit.wiring signature (fun j => (ρ j).elim (Fin.castAdd 2)
    (fun b => Fin.natAdd n (if b then 1 else 0)))).comp
    ((Circuit.id signature n).append
      (Circuit.pi fun i : Fin 2 => (Formula.const (i == 1)).toCircuit))

/-- The shared-constant circuit implements its input substitution. -/
@[simp] theorem eval_substituteCircuit {n N : ℕ} (ρ : Fin N → Fin n ⊕ Bool) (x : BitString n) :
    (substituteCircuit ρ).eval interpretation x = substitute ρ x := by
  funext j
  cases h : ρ j with
  | inl i => simp [substituteCircuit, substitute, h]
  | inr b =>
    cases b <;> simp [substituteCircuit, substitute, h]

/-- Substitution charges each of the two shared constant gates once. -/
theorem cost_program_substituteCircuit {n N : ℕ} (ρ : Fin N → Fin n ⊕ Bool)
    (cost : signature.Op → ℕ) :
    (substituteCircuit ρ).program.cost cost = cost (.const false) + cost (.const true) := by
  unfold substituteCircuit
  erw [Circuit.cost_program_comp, Circuit.cost_program_wiring, Circuit.cost_program_append,
    Circuit.cost_program_pi]
  simp [Circuit.id, Formula.cost_toCircuit, Fin.sum_univ_two, Formula.const]

/-- The substitution circuit has exactly two gates, regardless of the output width. -/
@[simp] theorem size_substituteCircuit {n N : ℕ} (ρ : Fin N → Fin n ⊕ Bool) :
    (substituteCircuit ρ).size = 2 := by
  simpa only [Program.cost_const, one_mul] using
    cost_program_substituteCircuit ρ (fun _ => 1)


/-- A substitution costs at most two gates, one for each constant. -/
theorem complexity_substitute_le_two (ρ : Fin N → Fin n ⊕ Bool) :
    complexity interpretation (substitute ρ) ≤ 2 := by
  simpa only [size_substituteCircuit] using
    complexity_le_of_computes (substituteCircuit ρ) (eval_substituteCircuit ρ)

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

namespace Cslib.BitString.PartialAssignment

open Circuits.Boolean

variable {n : ℕ}

/-- The substitution replacing each fixed bit by its value and each free bit by itself. -/
def toSubstitution (ρ : PartialAssignment (Fin n)) : Fin n → Fin n ⊕ Bool :=
  fun i => (ρ i).elim (.inl i) .inr

/-- Restricting is substituting constants for the fixed bits. -/
theorem substitute_toSubstitution (ρ : PartialAssignment (Fin n)) :
    substitute ρ.toSubstitution = ρ.fill := by
  funext x i
  cases h : ρ i <;> simp [toSubstitution, fill, h]

end Cslib.BitString.PartialAssignment
