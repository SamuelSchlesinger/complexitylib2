/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Basic

/-!
# Private randomness with typed oracle calls

`ProbOracleComp spec` combines the existing finite-uniform sampling interface with `spec` by a
disjoint sum of query types. It is still an `OracleComp`, interpreted by `OracleComp.interpret`.
`sample` embeds a closed probabilistic program, and `query` calls the external oracle. A handler
can therefore draw fresh private coins while caching only the external queries.

The finite-uniform interface specifies distributions, not their computational efficiency.
Strict fair-coin realizability is certified separately; arbitrary exact finite-uniform sampling
is not automatically a strict PPT operation.

## Main definitions

* `Cslib.ProbOracleComp`: the sum of the uniform sampling and external oracle interfaces.
* `Cslib.ProbOracleComp.sample`, `.query`: closed sampling and typed external calls.
* `Cslib.ProbOracleComp.handler`: combine handlers without introducing another interpreter.

## Main results

* `Cslib.ProbOracleComp.interpret_sample`: embedded sampling uses only the sampling handler.
* `Cslib.ProbOracleComp.run_interpret_sample`: private sampling leaves oracle state unchanged.

## References

Uses the typed interface of cslib PR #1129, by Samuel Schlesinger and Devon Tuma, based on the
VCVio design credited in `Languages.Probabilistic.Basic`. This replaces the separate sampling
constructor used by the cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib

universe v

/-- A disjoint sum keeps fresh sampling requests separate from external oracle requests. -/
abbrev probOracleSpec {Query : Type} (spec : Query → Type) : ℕ ⊕ Query → Type
  | .inl n => unifSpec n
  | .inr q => spec q

/-- A program with separate finite-uniform samples and typed external queries. -/
abbrev ProbOracleComp {Query : Type} (spec : Query → Type) (α : Type) :=
  OracleComp (probOracleSpec spec) α

namespace ProbOracleComp

variable {Query α β State : Type} {spec : Query → Type}

/-- Embed a closed probabilistic program; its calls remain separate from the external oracle. -/
def sample (program : ProbComp α) : ProbOracleComp spec α :=
  OracleComp.interpret (spec := unifSpec)
    (fun n => OracleComp.query (spec := probOracleSpec spec) (Sum.inl n)) program

/-- Make one external call, whose reply may determine later sampling or queries. -/
def query (q : Query) : ProbOracleComp spec (spec q) := OracleComp.query (Sum.inr q)

/-- Combine the two handlers. In particular, memoizing `oracle` does not memoize `random`. -/
def handler {m : Type → Type v} (random : (n : ℕ) → m (Fin (n + 1)))
    (oracle : (q : Query) → m (spec q)) :
    (q : ℕ ⊕ Query) → m (probOracleSpec spec q)
  | .inl n => random n
  | .inr q => oracle q

variable {m : Type → Type v} [Monad m] [LawfulMonad m]

/-- The combined handler answers a single external query through its external component. -/
@[simp] theorem interpret_query (random : (n : ℕ) → m (Fin (n + 1)))
    (oracle : (q : Query) → m (spec q)) (q : Query) :
    OracleComp.interpret (handler random oracle) (query q) = oracle q :=
  OracleComp.interpret_query _ _

/-- Embedded closed programs use only the sampling component of the combined handler. -/
@[simp] theorem interpret_sample (random : (n : ℕ) → m (Fin (n + 1)))
    (oracle : (q : Query) → m (spec q)) (program : ProbComp α) :
    OracleComp.interpret (handler random oracle) (sample program) =
      OracleComp.interpret random program := by
  simp [sample, OracleComp.interpret_interpret, handler]

/-- Sampling preserves ordinary functional sequencing before any interpretation. -/
@[simp] theorem sample_bind (program : ProbComp α) (next : α → ProbComp β) :
    sample (spec := spec) (program >>= next) = (sample program >>= fun a => sample (next a)) :=
  OracleComp.interpret_bind _ _ _

/-- Sampling a returned value makes no call. -/
@[simp] theorem sample_pure (a : α) : sample (spec := spec) (pure a) = pure a := rfl

/-- Deterministic postprocessing stays inside the embedded closed program. -/
@[simp] theorem sample_map (f : α → β) (program : ProbComp α) :
    sample (spec := spec) (f <$> program) = f <$> sample program :=
  OracleComp.interpret_map _ _ _

/-- Private sampling is fresh and leaves the complete external oracle state unchanged. -/
theorem run_interpret_sample (oracle : (q : Query) → StateT State PMF (spec q))
    (program : ProbComp α) (s : State) :
    (OracleComp.interpret
      (handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) (sample program)).run s =
        (ProbComp.eval program).map (·, s) := by
  rw [interpret_sample]
  exact OracleComp.run_interpret_stateless ProbComp.unifOracle program s

end ProbOracleComp

end Cslib
