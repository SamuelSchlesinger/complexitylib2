/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.B2.Restructure

/-!
# Eliminating the minimal AND

Cases 7 to 10 of [Mishra and Santhanam, Section 4.3][MishraSanthanam2026]. After the preliminary
reductions and the restructuring of Section 4.2, the minimal gate `G` is an AND-type gate reading
two unpaired parameters `x` and `y` of degree at least two, no child of `G` reads `x` or `y`, and
`G` is not the output and has a child (`State.MinAnd`). Then:

* Case 7: `deg x = deg y = 2` and `x`, `y` share their second child `B`; restricting to a line on
  which both `G` and `B` are constant deletes both (`State.Valid.step_case7`);
* Case 8: otherwise, unless in the bottleneck configuration, fixing `x` so that `G` becomes
  constant deletes the children of `x` and of `G` (`State.Valid.step_case8`);
* Cases 9 and 10: the bottleneck configuration, where `G` has a unique child `D` whose other input
  is an unpaired isolated parameter `z` (`State.Valid.step_bottleneck`).

The cases are proved in `Case7.lean`, `Case8.lean` and `Bottleneck.lean`.

## Main definitions

* `Cslib.Circuits.Boolean.B2.State.MinAnd`: the configuration of Section 4.3.
* `Cslib.Circuits.Boolean.B2.State.Case7`, `Cslib.Circuits.Boolean.B2.State.Bottleneck`: the
  configurations of Case 7 and of Cases 9 and 10.

## Main results

* `Cslib.Circuits.Boolean.B2.State.exists_and_form`: the normal form of AND-type operations.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.B2

open Finset Cslib.BitString

namespace State

variable {n : ℕ} {f : BooleanFunction n}

/-- Every AND-type operation has the form `(a + α)(b + β) + γ`. -/
theorem exists_and_form {op : Bool → Bool → Bool} (h : ¬ IsAffineOp op) :
    ∃ α β γ : Bool, ∀ a b, op a b = (((a ^^ α) && (b ^^ β)) ^^ γ) := by
  have key : ∃ α β γ : Bool, op false false = ((α && β) ^^ γ) ∧
      op true false = (((!α) && β) ^^ γ) ∧ op false true = ((α && !β) ^^ γ) ∧
      op true true = (((!α) && !β) ^^ γ) := by
    unfold IsAffineOp at h
    revert h
    generalize op false false = a₀; generalize op true false = b₀
    generalize op false true = c₀; generalize op true true = d₀
    revert a₀ b₀ c₀ d₀; decide
  obtain ⟨α, β, γ, h0, h1, h2, h3⟩ := key
  refine ⟨α, β, γ, fun a b => ?_⟩
  cases a <;> cases b
  · rw [h0]; cases α <;> cases β <;> rfl
  · rw [h2]; cases α <;> cases β <;> rfl
  · rw [h1]; cases α <;> cases β <;> rfl
  · rw [h3]; cases α <;> cases β <;> rfl

/-- The configuration of Section 4.3: `G` is an AND-type gate reading the distinct unpaired
parameters `x` and `y` with `2 ≤ deg y ≤ deg x`, no child of `G` reads `x` or `y`, and `G` is not
the output and has a child. -/
structure MinAnd (S : State n) (G x y : ℕ) : Prop where
  mem : G ∈ S.gates
  and_op : ¬ IsAffineOp (S.gate G).op
  args : ((S.gate G).left = .node x ∧ (S.gate G).right = .node y) ∨
    ((S.gate G).left = .node y ∧ (S.gate G).right = .node x)
  unpaired_x : x ∈ S.unpaired
  unpaired_y : y ∈ S.unpaired
  ne : x ≠ y
  deg_y : 2 ≤ S.deg y
  deg_le : S.deg y ≤ S.deg x
  children : ∀ K ∈ S.gates, (S.gate K).Reads G → ¬ (S.gate K).Reads x ∧ ¬ (S.gate K).Reads y
  not_out : ¬ S.out.Reads G
  has_child : ∃ K ∈ S.gates, (S.gate K).Reads G

/-- The configuration of Case 7: `deg x = deg y = 2` and the second children coincide. -/
def Case7 (S : State n) (G x y : ℕ) : Prop :=
  S.deg x = 2 ∧ ∃ B, B ≠ .inl G ∧ B ∈ S.children x ∧ B ∈ S.children y

/-- The bottleneck configuration: `deg x = 2`, `G` has a unique child `D`, and `D` reads an
unpaired isolated parameter `z`. -/
def Bottleneck (S : State n) (G x : ℕ) : Prop :=
  S.deg x = 2 ∧ ∃ D z, (∀ K ∈ S.gates, (S.gate K).Reads G ↔ K = D) ∧ D ∈ S.gates ∧
    z ∈ S.unpaired ∧ S.deg z = 1 ∧ (S.gate D).Reads z

end State

end Cslib.Circuits.Boolean.B2
