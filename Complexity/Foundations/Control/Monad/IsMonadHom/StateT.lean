/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Foundations.Control.Monad.IsMonadHom

/-!
# Monad morphisms under private state

A monad morphism transforms a stateful computation by transforming its complete result/state
pair. It preserves sequencing without dropping or reinitializing the private state.

## Main results

* `Cslib.IsMonadHom.stateT`: lift a monad morphism pointwise under `StateT`.

## References

Uses the upstream `Cslib.IsMonadHom` interface and Lean's `StateT`.
-/

@[expose] public section

namespace Cslib

universe u v w

/-- Transforming the underlying effect while retaining state is a monad morphism. -/
theorem IsMonadHom.stateT {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    {f : ∀ {α}, m α → n α} (hf : IsMonadHom m n f) (State : Type u) :
    IsMonadHom (StateT State m) (StateT State n)
      (fun program state => f (program state)) :=
  .mk' (fun _ => funext fun _ => hf.map_pure _)
    (fun program next => funext fun state => hf.map_bind (program state)
      (fun (a, state') => next a state'))

end Cslib
