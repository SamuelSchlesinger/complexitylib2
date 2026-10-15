/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.GateElimination
import Complexity.Computability.Circuit.Boolean.Khrapchenko
import Complexity.Computability.Circuit.Boolean.PolynomialTime
import Complexity.Computability.Circuit.Boolean.Smolensky
import Complexity.Computability.Circuit.Boolean.TC0
import Complexity.Computability.Circuit.Monotone.Clique.Asymptotic
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id

/-!
# Non-vacuity of the complexity classes

A machine without work tapes that writes a constant answer in one step computes a constant
function in polynomial time, whatever the input encoding. So the empty and the full problem are in
`P`, `NP`, `BPP` and `RP`, and the hypotheses of the theorems about these classes (such as
`Cslib.Circuits.Boolean.PPoly.of_mem_P` and `PPoly.of_mem_BPP`) can be met.

Constant functions will come from the composition machinery upstream; this file only guards
against definitions that are accidentally unsatisfiable.
-/

namespace ComplexityTests.NonVacuity

open Turing Turing.MultiTapeTM Cslib.Complexity Cslib.Circuits.Boolean

/-- The machine that writes `b` and halts. -/
def constTM (b : Bool) : MultiTapeTM 0 Bool Unit :=
  ofTr () fun _ _ _ => ⟨0, Fin.elim0, some b, none⟩

theorem computesTidily_constTM (b : Bool) (w : List Bool) :
    (constTM b).ComputesTidilyInTimeAndSpace w [b] 1 0 := by
  rw [computesTidily_iff]
  refine ⟨?_, ?_⟩
  · rw [show (1 : ℕ) = 0 + 1 from rfl, runFrom_succ, show runFrom _ 0 = _ from rfl,
      step_of_state (q := ()) rfl]
    simp only [constTM, tr_ofTr, wordsCfg, Action.apply, moveInputPos_zero]
    congr <;> funext i <;> exact i.elim0
  · simp [spaceUsed]

theorem polyTime_const {α : Type} (enc : α ↪ List Bool) (b : Bool) :
    ComputableTidilyInPolyTime (fun _ : α => b) enc encBool :=
  ⟨fun _ => 1, fun _ => 0, ⟨1, 0, fun _ => by simp⟩, ⟨0, 0, fun _ => by simp⟩,
    0, Unit, inferInstance, constTM b, fun a => computesTidily_constTM b (enc a)⟩

example : (∅ : Set (List Bool)) ∈ Cslib.Complexity.P encBits :=
  ⟨fun _ => false, polyTime_const _ false, fun _ => by simp⟩

example : (Set.univ : Set (List Bool)) ∈ Cslib.Complexity.P encBits :=
  ⟨fun _ => true, polyTime_const _ true, fun _ => by simp⟩

example : (∅ : Set (List Bool)) ∈ NP encBits :=
  ⟨0, fun _ => false, polyTime_const _ false, fun _ => by simp⟩

example : (Set.univ : Set (List Bool)) ∈ NP encBits :=
  ⟨0, fun _ => true, polyTime_const _ true, fun _ => by simp⟩

example : (∅ : Set (List Bool)) ∈ BPP encBits :=
  ⟨0, fun _ => false, polyTime_const _ false, fun _ => ⟨fun h => h.elim, fun _ => by
      simp only [Polynomial.eval_zero, pow_zero, mul_one]
      exact le_trans (by norm_num : 2 ≤ 3 * 1)
        (Nat.mul_le_mul_left 3 (Finset.card_pos.2
          ⟨fun _ => false, Finset.mem_filter.2 ⟨Finset.mem_univ _, trivial⟩⟩))⟩⟩

example : (∅ : Set (List Bool)) ∈ RP encBits :=
  ⟨0, fun _ => false, polyTime_const _ false, fun _ => ⟨fun h => h.elim, fun _ _ => rfl⟩⟩

/-- `P ⊆ P/poly` applies to a language in `P`. -/
example : (⊤ : Language Bool) ∈ PPoly :=
  PPoly.of_mem_P ⟨fun _ => true, polyTime_const _ true, fun _ => ⟨fun _ => rfl, fun _ => trivial⟩⟩

/-- `BPP ⊆ P/poly` applies to a language in `BPP`. -/
example : (⊥ : Language Bool) ∈ PPoly :=
  PPoly.of_mem_BPP ⟨0, fun _ => false, polyTime_const _ false,
    fun _ => ⟨fun h => h.elim, fun _ => by
      simp only [Polynomial.eval_zero, pow_zero, mul_one]
      exact le_trans (by norm_num : 2 ≤ 3 * 1)
        (Nat.mul_le_mul_left 3 (Finset.card_pos.2
          ⟨fun _ => false, Finset.mem_filter.2 ⟨Finset.mem_univ _, trivial⟩⟩))⟩⟩

/-- The monotone lower bound for cliques is about a finite complexity. -/
example : Cslib.Circuits.ecomplexity Cslib.Circuits.Monotone.interpretation
    (Cslib.Circuits.single (Cslib.Circuits.clique 16 2)) ≠ ⊤ :=
  Cslib.Circuits.Monotone.ecomplexity_clique_ne_top 16 2

/-- Schnorr's bound applies to the parity of three bits, which has De Morgan circuits. -/
example : 6 ≤ Cslib.Circuits.complexity Cslib.Circuits.Boolean.interpretation
    (Cslib.Circuits.single (Cslib.parity 3)) :=
  Cslib.Circuits.Boolean.three_mul_le_complexity_parity 3

/-- Khrapchenko's bound applies to the parity of four bits, which has a formula of leaf size 16. -/
example : ∃ F : Cslib.Circuits.Formula Cslib.Circuits.Boolean.signature (2 ^ 2),
    F.Computes Cslib.Circuits.Boolean.interpretation (Cslib.parity (2 ^ 2)) ∧
      F.leafSize = 16 :=
  Cslib.Circuits.Boolean.exists_formula_parity_two_pow 2

/-- The constant-depth classes are inhabited, by the constants. -/
example : (⊤ : Language Bool) ∈ Unbounded.AC0 ∧ (0 : Language Bool) ∈ Unbounded.AC0 :=
  ⟨Unbounded.AC0.top_mem, Unbounded.AC0.zero_mem⟩

example : (⊤ : Language Bool) ∈ MajorityBasis.TC0 :=
  MajorityBasis.AC0_subset_TC0 Unbounded.AC0.top_mem

example : (0 : Language Bool) ∈ ModBasis.AC0Mod 3 :=
  ModBasis.AC0_subset_AC0Mod 3 Unbounded.AC0.zero_mem

/-- The tidy normal form applies to upstream's machine for the identity, which is not tidy: it
leaves its input head at the end of the input. -/
example {α : Type} (enc : α ↪ List Bool) :
    ∃ c, ComputableTidilyInTimeAndSpace (id : α → α) enc enc
      (fun a => 2 * ((enc a).length + 1) + 3 * 0 + c) (fun _ => c * (0 + 1)) :=
  computableInTimeAndSpace_id.exists_computableTidilyInTimeAndSpace

end ComplexityTests.NonVacuity
