/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.GGM.Hybrid
import Complexity.Tactic.PPT

/-! GGM's evaluator, adaptive prefix games and machine certificates, including short expansions,
empty seeds and noncanonical caches. These examples do not assert cryptographic security. -/

namespace ComplexityTests.GGM

open Turing.MultiTapeTM Cslib Cslib.Crypto Cslib.Probability

example : GGM.eval (fun seed => seed ++ seed.reverse ++ [true]) [false, true] [true, false] =
    [true, false] := by decide

example (query : List Bool) : GGM.eval (fun _ => [true]) [] query = [] := by
  exact List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (GGM.length_eval_le _ [] query))

-- Duplicating the seed is a concrete efficient generator, though it is not pseudorandom.
example : ComputableTidilyInPolyTime
    (fun p : List Bool × List Bool => GGM.eval (fun seed => seed ++ seed) p.1 p.2)
    (encPair encBits encBits) encBits := by fun_prop

-- A shrinking expansion is allowed: efficiency does not require a PRG or a length hypothesis.
example : ComputableTidilyInPolyTime
    (fun p : List Bool × List Bool => GGM.eval List.tail p.1 p.2)
    (encPair encBits encBits) encBits := by fun_prop

example (generator : List Bool → List Bool)
    (hgenerator : ComputableTidilyInPolyTime generator encBits encBits) :
    ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool => GGM.eval generator p.1 (p.2 ++ p.2))
      (encPair encBits encBits) encBits := by fun_prop

-- Computed inputs and a nonempty cache use the same registered handler rule.
example : IsPPTOn (encPair encUnary encBits) (encPair encBits GGM.cacheEncoding)
    (fun pair => GGM.frontierOracle (fun seed => seed ++ seed) pair.1 (pair.1 + 1)
      pair.2.reverse [(pair.2, pair.2)]) := by fun_prop

-- The ordinary monadic spelling exposes no machine or tape-layout details.
example : IsPPTOn (encPair encUnary encBits) (encPair encBits GGM.cacheEncoding)
    (fun pair => if pair.2.length = pair.1 then do
      let (seed, cache) ← memoize (fun _ => BitString.sampleList pair.1)
        (pair.2.take (pair.1 + 1)) []
      return (GGM.eval List.tail seed (pair.2.drop (pair.1 + 1)), cache)
    else pure ([], [])) := by
  unfold GGM.cacheEncoding
  ppt

-- The full-game certificate has concrete inhabitants without a cryptographic assumption.
example : IsPPTOn (encPair encUnary encUnary) encBool
    (fun pair => GGM.hybridGame (fun seed => seed ++ seed)
      (fun n input => pure (decide (input.length ≤ n))) pair.1 pair.2) :=
  GGM.isPPTOn_hybridGame (by fun_prop) (by fun_prop)

-- An empty seed and query still create exactly one empty root entry.
example (generator : List Bool → List Bool) :
    GGM.frontierOracle generator 0 0 [] [] = pure ([], [([], [])]) := by
  simp [GGM.frontierOracle, memoize, BitString.sampleList]

-- Rejection does not touch arbitrary preassigned private state.
example (generator : List Bool → List Bool) (depth : ℕ) (cache : GGM.Cache) :
    GGM.frontierOracle generator 1 depth [] cache = pure ([], cache) := by
  simp [GGM.frontierOracle]

-- Repeated keys use the first entry; depths past the query length are also well defined.
example (generator : List Bool → List Bool) :
    GGM.frontierOracle generator 1 3 [false] [([false], [true]), ([false], [false])] =
      pure ([true], [([false], [true]), ([false], [false])]) := by
  simp [GGM.frontierOracle, memoize]

-- When the client makes no queries, lazily deferring the root draw preserves its private coin.
example (generator : List Bool → List Bool) (n : ℕ) :
    ProbComp.eval (GGM.hybridGame generator
      (fun _ _ => ProbOracleComp.sample (ProbComp.uniform Bool)) n 0) =
        PMF.uniformOfFintype Bool := by
  rw [GGM.hybridGame_zero]
  simp only [prfRealGame, ProbComp.eval_bind, ProbOracleComp.eval_interpret]
  simpa [ProbOracleComp.interpret_sample] using
    (show OracleComp.interpret ProbComp.unifOracle (ProbComp.uniform Bool) =
      PMF.uniformOfFintype Bool from ProbComp.eval_uniform Bool)

end ComplexityTests.GGM
