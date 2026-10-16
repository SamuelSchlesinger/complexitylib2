/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Basic
import Complexity.Foundations.Control.Monad.IsMonadHom.StateT

/-!
# Stateful oracle simulation

Local simulation identities lift to arbitrary adaptive programs, retaining both the result and
the oracle's final private state. A simulation may randomly complete hidden state, as in the
lazy-sampling proof for a random function. The local identity only needs to hold at states
satisfying a preserved invariant.

These rules adapt `Languages/Probabilistic/Simulation.lean` from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` to the common `OracleComp.interpret` interface.
There is one oracle specification and one interpreter; stateful execution uses `StateT`.

## Main results

* `Cslib.OracleComp.run_interpret_invariant`: invariants of each call hold after execution.
* `Cslib.OracleComp.run_interpret_simulation_of_invariant`: probabilistic state simulation.
* `Cslib.OracleComp.run_interpret_map_state_of_invariant`: deterministic state representation.
* `Cslib.OracleComp.map_run_interpret`: a monad morphism commutes with stateful interpretation.
-/

@[expose] public section

namespace Cslib.OracleComp

universe u v

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {α State State' : Type v}

/-- An invariant preserved by supported oracle transitions holds after every adaptive program. -/
theorem run_interpret_invariant
    (oracle : (q : ι) → StateT State PMF (spec q)) (invariant : State → Prop)
    (step : ∀ q s, invariant s → ∀ a s', (a, s') ∈ (oracle q s).support → invariant s')
    (program : OracleComp spec α) (s : State) (hs : invariant s)
    (result : α) (s' : State)
    (h : (result, s') ∈ ((interpret oracle program).run s).support) : invariant s' := by
  induction program using PFunctor.FreeM.induction generalizing s with
  | pure a =>
    change (result, s') ∈ (PMF.pure (a, s)).support at h
    simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at h
    rwa [h.2]
  | lift_bind q cont ih =>
    change (result, s') ∈ ((interpret oracle (query q >>= cont)).run s).support at h
    simp only [interpret_bind, interpret_query, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at h
    obtain ⟨⟨a, next⟩, ha, h⟩ := h
    exact ih a next (step q s hs a next ha) h

/-- A probabilistic change of private state that commutes with calls on invariant states
commutes with an entire adaptive computation. Only supported transitions must preserve the
invariant, and the equality retains the joint result and final state. -/
theorem run_interpret_simulation_of_invariant
    (oracle : (q : ι) → StateT State PMF (spec q))
    (oracle' : (q : ι) → StateT State' PMF (spec q))
    (relate : State → PMF State') (invariant : State → Prop)
    (preserve : ∀ q s, invariant s → ∀ a s', (a, s') ∈ (oracle q s).support → invariant s')
    (step : ∀ q s, invariant s →
      (oracle q s).bind (fun (a, s') => (relate s').map (a, ·)) =
        (relate s).bind (oracle' q))
    (program : OracleComp spec α) (s : State) (hs : invariant s) :
    ((interpret oracle program).run s).bind (fun (a, s') => (relate s').map (a, ·)) =
      (relate s).bind (fun t => (interpret oracle' program).run t) := by
  induction program using PFunctor.FreeM.induction generalizing s with
  | pure a => simp [PMF.map, Function.comp_def]
  | lift_bind q cont ih =>
    change ((interpret oracle (query q >>= cont)).run s).bind _ =
      (relate s).bind (fun t => (interpret oracle' (query q >>= cont)).run t)
    simp only [interpret_bind, interpret_query, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, PMF.bind_bind]
    calc
      _ = (oracle q s).bind (fun (a, s') =>
          (relate s').bind (fun t => (interpret oracle' (cont a)).run t)) := by
        apply Probability.PMF.bind_congr_on_support
        rintro ⟨a, s'⟩ hnext
        exact ih a s' (preserve q s hs a s' hnext)
      _ = ((oracle q s).bind (fun (a, s') => (relate s').map (a, ·))).bind
          (fun (a, t) => (interpret oracle' (cont a)).run t) := by
        simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
      _ = _ := by
        rw [step q s hs, PMF.bind_bind]
        rfl

/-- A local probabilistic simulation lifts to every adaptive computation. -/
theorem run_interpret_simulation
    (oracle : (q : ι) → StateT State PMF (spec q))
    (oracle' : (q : ι) → StateT State' PMF (spec q))
    (relate : State → PMF State')
    (step : ∀ q s, (oracle q s).bind (fun (a, s') => (relate s').map (a, ·)) =
      (relate s).bind (oracle' q)) (program : OracleComp spec α) (s : State) :
    ((interpret oracle program).run s).bind (fun (a, s') => (relate s').map (a, ·)) =
      (relate s).bind (fun t => (interpret oracle' program).run t) :=
  run_interpret_simulation_of_invariant oracle oracle' relate (fun _ => True)
    (by simp) (fun q s _ => step q s) program s trivial

/-- Re-encoding private state preserves adaptive execution when calls agree on invariant states. -/
theorem run_interpret_map_state_of_invariant
    (oracle : (q : ι) → StateT State PMF (spec q))
    (oracle' : (q : ι) → StateT State' PMF (spec q))
    (represent : State → State') (invariant : State → Prop)
    (preserve : ∀ q s, invariant s → ∀ a s', (a, s') ∈ (oracle q s).support → invariant s')
    (step : ∀ q s, invariant s →
      (oracle q s).map (fun (a, s') => (a, represent s')) = oracle' q (represent s))
    (program : OracleComp spec α) (s : State) (hs : invariant s) :
    ((interpret oracle program).run s).map (fun (a, s') => (a, represent s')) =
      (interpret oracle' program).run (represent s) := by
  simpa only [PMF.pure_map, PMF.pure_bind, PMF.map, Function.comp_def] using
    run_interpret_simulation_of_invariant oracle oracle' (fun s => PMF.pure (represent s))
      invariant preserve
      (by simpa only [PMF.pure_map, PMF.pure_bind, PMF.map, Function.comp_def] using step)
      program s hs

/-- A deterministic representation commuting with each call preserves the complete execution. -/
theorem run_interpret_map_state
    (oracle : (q : ι) → StateT State PMF (spec q))
    (oracle' : (q : ι) → StateT State' PMF (spec q)) (represent : State → State')
    (step : ∀ q s, (oracle q s).map (fun (a, s') => (a, represent s')) =
      oracle' q (represent s)) (program : OracleComp spec α) (s : State) :
    ((interpret oracle program).run s).map (fun (a, s') => (a, represent s')) =
      (interpret oracle' program).run (represent s) :=
  run_interpret_map_state_of_invariant oracle oracle' represent (fun _ => True)
    (by simp) (fun q s _ => step q s) program s trivial

/-- Transforming the underlying monad commutes with stateful program interpretation, retaining
the joint result and private state. -/
theorem map_run_interpret {m n : Type v → Type*} [Monad m] [Monad n]
    [LawfulMonad m] [LawfulMonad n] {f : ∀ {β}, m β → n β}
    (hf : IsMonadHom m n f) (oracle : (q : ι) → StateT State m (spec q))
    (program : OracleComp spec α) (s : State) :
    f ((interpret oracle program).run s) =
      (interpret (m := StateT State n) (fun q state => f (oracle q state)) program).run s :=
  congrFun ((hf.stateT State).map_pfunctorFreeMLiftM (P := ⟨ι, spec⟩) oracle program) s

end Cslib.OracleComp
