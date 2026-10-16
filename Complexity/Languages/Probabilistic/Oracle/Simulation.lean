/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Oracle
import Complexity.Languages.Probabilistic.Simulation

/-!
# Stateful simulation with private randomness

An external oracle's invariant or state simulation remains valid when clients also draw private
randomness. Private draws leave oracle state untouched, and independent sampling commutes with
the distribution relating two state representations. These are specializations of the existing
`OracleComp` rules to the disjoint-sum interface, with no additional program induction.

## Main results

* `Cslib.ProbOracleComp.run_interpret_invariant`: external invariants survive private sampling.
* `Cslib.ProbOracleComp.run_interpret_simulation`: local joint-state simulation suffices.
* `Cslib.ProbOracleComp.run_interpret_map_state`: deterministic representation of oracle state.
* `Cslib.ProbOracleComp.run_interpret_readOnly`: preserve a fixed external environment.

## References

Adapts the cslib `crypto` branch's state simulation API at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` to the typed sum of sampling and external calls.
-/

@[expose] public section

namespace Cslib.ProbOracleComp

open Probability

variable {Query α State State' : Type} {spec : Query → Type}

/-- Reading a fixed external environment retains it, independently of the client's private draws. -/
theorem run_interpret_readOnly (oracle : (q : Query) → State → PMF (spec q))
    (program : ProbOracleComp spec α) (s : State) :
    (OracleComp.interpret
      (handler (fun n => StateT.lift (ProbComp.unifOracle n))
        (fun q state => (oracle q state).map (·, state))) program).run s =
      (OracleComp.interpret
        (handler ProbComp.unifOracle (fun q => oracle q s)) program).map (·, s) := by
  have hhandler : handler (fun n => StateT.lift (ProbComp.unifOracle n))
      (fun q state => (oracle q state).map (·, state)) =
      fun q state => (handler ProbComp.unifOracle (fun q => oracle q state) q).map (·, state) := by
    funext q state
    cases q <;> rfl
  rw [hhandler]
  exact OracleComp.run_interpret_readOnly
    (fun q state => handler ProbComp.unifOracle (fun q => oracle q state) q) program s

/-- An external oracle's invariant is unaffected by the client's private sampling. -/
theorem run_interpret_invariant (oracle : (q : Query) → StateT State PMF (spec q))
    (invariant : State → Prop)
    (step : ∀ q s, invariant s → ∀ a s', (a, s') ∈ (oracle q s).support → invariant s')
    (program : ProbOracleComp spec α) (s : State) (hs : invariant s) (result : α) (s' : State)
    (h : (result, s') ∈ ((OracleComp.interpret
      (handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) program).run s).support) :
    invariant s' := by
  apply OracleComp.run_interpret_invariant _ invariant ?_ program s hs result s' h
  intro q state hstate value next hnext
  cases q with
  | inl n =>
    change (value, next) ∈ ((ProbComp.unifOracle n).map (·, state)).support at hnext
    obtain ⟨_, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
    exact (Prod.mk.inj heq).2 ▸ hstate
  | inr q => exact step q state hstate value next hnext

/-- A local probabilistic state simulation extends to clients with fresh private samples. -/
theorem run_interpret_simulation (oracle : (q : Query) → StateT State PMF (spec q))
    (oracle' : (q : Query) → StateT State' PMF (spec q)) (relate : State → PMF State')
    (step : ∀ q s, (oracle q s).bind (fun (a, s') => (relate s').map (a, ·)) =
      (relate s).bind (oracle' q)) (program : ProbOracleComp spec α) (s : State) :
    ((OracleComp.interpret
      (handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) program).run s).bind
        (fun (a, s') => (relate s').map (a, ·)) =
      (relate s).bind (fun state => (OracleComp.interpret
        (handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle') program).run state) := by
  apply OracleComp.run_interpret_simulation
  intro q state
  cases q with
  | inl n =>
    change ((ProbComp.unifOracle n).map (·, state)).bind
      (fun (a, next) => (relate next).map (a, ·)) =
        (relate state).bind (fun next => (ProbComp.unifOracle n).map (·, next))
    simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
    exact PMF.bind_comm _ _ _
  | inr q => exact step q state

/-- A deterministic state representation commuting with external calls commutes with the whole
randomized adaptive program, retaining the result and represented private state. -/
theorem run_interpret_map_state (oracle : (q : Query) → StateT State PMF (spec q))
    (oracle' : (q : Query) → StateT State' PMF (spec q)) (represent : State → State')
    (step : ∀ q s, (oracle q s).map (fun (a, s') => (a, represent s')) =
      oracle' q (represent s)) (program : ProbOracleComp spec α) (s : State) :
    ((OracleComp.interpret
      (handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) program).run s).map
        (fun (a, s') => (a, represent s')) =
      (OracleComp.interpret
        (handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle') program).run
          (represent s) := by
  simpa only [PMF.pure_map, PMF.pure_bind, PMF.map, Function.comp_def] using
    run_interpret_simulation oracle oracle' (fun s => PMF.pure (represent s))
      (by simpa only [PMF.pure_map, PMF.pure_bind, PMF.map, Function.comp_def] using step)
      program s

end Cslib.ProbOracleComp
