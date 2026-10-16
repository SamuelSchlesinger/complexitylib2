/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Tactic.PPT
import Complexity.Probability.BitString.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Mathlib.Logic.Relation

/-! Adaptive closed programs, invariant-based resource proofs and independent saved blocks. -/

namespace ComplexityTests.AdaptivePPT

open Cslib Cslib.Probability Turing.MultiTapeTM

example : BitString.listRows 3 2 [true, false, true] =
    [[true, false], [true, false], [false, false]] := by rfl

example : BitString.listRows 3 0 [true] = [[], [], []] := by rfl

example : BitString.listRows 0 4 [true] = [] := by rfl

-- Both dimensions are runtime values; short inputs are padded and all output cells are charged.
example : ComputableTidilyInPolyTime
    (fun p : (ℕ × ℕ) × List Bool => BitString.listRows p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary encUnary) encBits) (encList encBits) := by fun_prop

-- The joint law contains two independent fair bits, including the probability of disagreement.
example : (BitString.uniformList 2).map (BitString.listRows 2 1) =
    (PMF.uniformOfFintype (Fin 2 → BitString 1)).map
      (fun rows => List.ofFn (fun i => List.ofFn (rows i))) :=
  BitString.uniformList_listRows 2 1

private noncomputable def grow (state : List Bool) : ProbComp (List Bool) := do
  let bit ← ProbComp.uniform Bool
  return bit :: state

private theorem grow_ppt : IsPPTOn encBits encBits grow := by unfold grow; ppt

private theorem grow_length (state next : List Bool)
    (h : next ∈ (ProbComp.eval (grow state)).support) : next.length ≤ state.length + 1 := by
  simp only [grow, ProbComp.eval_bind, ProbComp.eval_pure] at h
  obtain ⟨bit, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  simp [← heq]

-- A full functional client certifies a quadratic number of state-dependent transitions.
example : IsPPTOn encUnary encBits (fun n => OracleComp.iterate (n * n) grow []) := by
  have hstep := grow_ppt
  have hgrowth := grow_length
  ppt

-- A polynomial iteration count alone cannot certify an exponentially growing output.
example : True := by
  fail_if_success
    have : IsPPTOn encUnary encUnary
        (fun n => OracleComp.iterate n (fun state => pure (2 * state)) n) := by ppt
  trivial

-- An implicit binary graph is supplied by an efficient transition function. The loop contract
-- certifies both its machine time and that every possible output is reachable from its input.
example (neighbor : List Bool → Bool → List Bool)
    (hefficient : ComputableTidilyInPolyTime (fun p : List Bool × Bool => neighbor p.1 p.2)
      (encPair encBits encBool) encBits)
    (hsize : ∀ state bit, (neighbor state bit).length ≤ state.length) :
    let step (state : List Bool) : ProbComp (List Bool) := do
      let bit ← ProbComp.uniform Bool
      return neighbor state bit
    IsPPTOn encBits encBits (fun start => OracleComp.iterate (start.length ^ 2) step start) ∧
      ∀ start final, final ∈
        (ProbComp.eval (OracleComp.iterate (start.length ^ 2) step start)).support →
        final.length ≤ start.length ∧
          Relation.ReflTransGen (fun a b => ∃ bit, neighbor a bit = b) start final := by
  dsimp only
  let step (state : List Bool) : ProbComp (List Bool) := do
    let bit ← ProbComp.uniform Bool
    return neighbor state bit
  have hstep : IsPPTOn encBits encBits step := by dsimp only [step]; ppt
  exact IsPPTOn.iterate_spec (by fun_prop) ComputableTidilyInPolyTime.id' hstep
    (fun start _ state => state.length ≤ start.length ∧
      Relation.ReflTransGen (fun a b => ∃ bit, neighbor a bit = b) start state)
    (fun _ => ⟨le_rfl, .refl⟩)
    (by
      intro start i state _ hstate next hnext
      simp only [step, ProbComp.eval_bind, ProbComp.eval_pure] at hnext
      obtain ⟨bit, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
      exact ⟨by simpa only [← heq] using (hsize state bit).trans hstate.1,
        hstate.2.tail ⟨bit, heq⟩⟩)
    (size := id) (by fun_prop) (fun _ _ _ _ h => h.1)

private noncomputable def cappedStep (limit state : ℕ) : ProbComp ℕ := do
  let bit ← ProbComp.uniform Bool
  return if bit && decide (state < limit) then state + 1 else state

-- Compound guards retain ordinary functional syntax through deterministic and PPT automation.
example : ComputableTidilyInPolyTime
    (fun p : (ℕ × ℕ) × Bool =>
      if p.2 && decide (p.1.2 < p.1.1) then p.1.2 + 1 else p.1.2)
    (encPair (encPair encUnary encUnary) encBool) encUnary := by fun_prop

example : ComputableTidilyInPolyTime
    (fun p : ℕ × ℕ => if p.1 ≤ p.2 ∧ p.2 < p.1 + 3 then p.1 + 1 else p.2)
    (encPair encUnary encUnary) encUnary := by polytime

-- Captured input affects every transition, while the invariant bounds only the changing state.
example : IsPPTOn encUnary encUnary
    (fun limit => OracleComp.iterate (limit * limit) (cappedStep limit) 0) ∧
    ∀ limit final,
      final ∈ (ProbComp.eval (OracleComp.iterate (limit * limit) (cappedStep limit) 0)).support →
      final ≤ limit := by
  have hstep : IsPPTOn (encPair encUnary encUnary) encUnary
      (fun p => cappedStep p.1 p.2) := by
    unfold cappedStep
    ppt
  exact IsPPTOn.iterateWith_spec (by fun_prop) (by fun_prop) hstep
    (fun limit _ state => state ≤ limit) (by simp)
    (by
      intro limit i state _ hstate next hnext
      simp only [cappedStep, ProbComp.eval_bind, ProbComp.eval_pure] at hnext
      obtain ⟨bit, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
      split
      · next hmove =>
          have := of_decide_eq_true (Bool.and_eq_true_iff.mp hmove).2
          lia
      · exact hstate)
    (size := id) (by fun_prop) (fun _ _ _ _ h => by simpa using h)

-- Zero iterations perform no transition, including for the captured-input client.
example : ProbComp.eval (OracleComp.iterate 0 (cappedStep 0) 0) = PMF.pure 0 := by simp

end ComplexityTests.AdaptivePPT
