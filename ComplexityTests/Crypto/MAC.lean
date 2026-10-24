/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.MAC

/-!
# Tests for uniform symmetric MAC schemes and the PRF-to-MAC construction

Provides concrete instantiations of `MACScheme` (both a trivial scheme and `prfMAC` applied to the
identity-keyed evaluator `fun _ m => m`), verifies that `OneTimeEUFCMA` and `EUFCMA` reject the
trivial scheme via an explicit zero-query PPT forger, checks `prfMAC` tagging/verification and
`macToPrfDistinguisher` on concrete inputs, and audits the axiom dependencies of the headline
theorems in `Complexity.Crypto.Computational.MAC`.
-/

namespace ComplexityTests.Crypto.MAC

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-- Concrete trivial MAC scheme where every tag is accepted. Used to witness that the `MACScheme`
fields are jointly satisfiable and to verify that `OneTimeEUFCMA` and `EUFCMA` reject insecure
schemes. -/
noncomputable def trivialMACScheme : MACScheme where
  keyGen _ := pure []
  sign _ msg := pure msg
  verify _ _ _ := true
  keyGen_ppt := by ppt
  sign_ppt := by ppt
  verify_polyTime := by polytime
  verify_sign := by
    intro _ _ _ _ _ _ _
    rfl

/-- Concrete instantiation of `prfMAC` on the message-echo family `fun _ msg => msg`. -/
noncomputable def echoPrfMAC : MACScheme :=
  prfMAC (fun _ msg => msg) (.of_tidy (ComputableTidilyInPolyTime.snd _ _))

-- Matching key and message lengths produce a valid tag accepted by `verify`.
example : echoPrfMAC.sign [true, false] [false, true] = pure [false, true] := by
  rfl

example : echoPrfMAC.verify [true, false] [false, true] [false, true] = true := by
  rfl

-- A wrong tag or wrong message length is rejected by `verify`.
example : echoPrfMAC.verify [true, false] [false, true] [true, true] = false := by
  rfl

example : echoPrfMAC.verify [true, false] [false] [false] = false := by
  rfl

-- A wrong-length query to `echoPrfMAC.oneTimeSigningOracle` returns `[]` and consumes the single
-- query slot.
example : echoPrfMAC.oneTimeSigningOracle [true, false] ((), [true]) [] =
    pure ([], [[true]]) := by
  rfl

example : echoPrfMAC.oneTimeSigningOracle [true, false] ((), [false, true]) [[true]] =
    pure ([], [[true]]) := by
  rfl

-- Even an always-accepting verifier cannot bypass the game's n-bit message check.
example (n : ℕ) : trivialMACScheme.eufOneTimeGame
      (fun _ _ => ProbOracleComp.sample (pure ([], []))) (n + 1) = pure false := by
  simp [MACScheme.eufOneTimeGame, trivialMACScheme]

-- A wrong-length candidate forgery causes `macToPrfDistinguisher` to reject without making a
-- verification query.
example (n : ℕ) : macToPrfDistinguisher
      (fun _ _ => ProbOracleComp.sample (pure ([], []))) (n + 1) [] = pure false := by
  simp [macToPrfDistinguisher]

/-- The trivial MAC scheme is not one-time EUF-CMA secure: a zero-query PPT forger that outputs
`(0^n, [])` succeeds with probability `1`. -/
theorem not_oneTimeEUFCMA_trivialMACScheme :
    ¬ trivialMACScheme.OneTimeEUFCMA := by
  intro hsec
  let forger : Forger := fun n _ =>
    ProbOracleComp.sample (pure (List.replicate n false, []))
  have hforgerBody : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p : ℕ × List Bool => (pure (List.replicate p.1 false, []) :
        ProbComp (List Bool × List Bool))) := by
    have hpair : ComputableTidilyInPolyTime
        (fun p : ℕ × List Bool => (List.replicate p.1 false, ([] : List Bool)))
        (encPair encUnary encBits) (encPair encBits encBits) := by polytime
    exact hpair.isPPTOn
  have hforger : IsOraclePPT (encPair encBits encBits) forger :=
    hforgerBody.isOraclePPTOn.isOraclePPT
  have hneg := hsec.negligible forger hforger
  have heval (n : ℕ) :
      Game.succProbability
        (ProbComp.eval (trivialMACScheme.eufOneTimeGame forger n)) = 1 := by
    simp [MACScheme.eufOneTimeGame, trivialMACScheme, forger, Game.succProbability]
  simp only [heval] at hneg
  exact not_negligible_const one_ne_zero hneg

/-- The trivial MAC scheme is not EUF-CMA secure. -/
theorem not_eufCMA_trivialMACScheme :
    ¬ trivialMACScheme.EUFCMA :=
  fun h => not_oneTimeEUFCMA_trivialMACScheme h.oneTimeEUFCMA

/--
info: 'Cslib.Crypto.MACScheme.EUFCMA.oneTimeEUFCMA' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.MACScheme.EUFCMA.oneTimeEUFCMA

/--
info: 'Cslib.Crypto.isOraclePPT_macToPrfDistinguisher' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.isOraclePPT_macToPrfDistinguisher

/--
info: 'Cslib.Crypto.eval_prfRealGame_macToPrfDistinguisher' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.eval_prfRealGame_macToPrfDistinguisher

/--
info: 'Cslib.Crypto.succProbability_prfIdealGame_macToPrfDistinguisher_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.succProbability_prfIdealGame_macToPrfDistinguisher_le

/--
info: 'Cslib.Crypto.succProbability_eufCmaGame_prfMAC_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.succProbability_eufCmaGame_prfMAC_le

/--
info: 'Cslib.Crypto.PseudorandomFunction.eufCma_prfMAC' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PseudorandomFunction.eufCma_prfMAC

/--
info: 'Cslib.Crypto.PseudorandomFunction.oneTimeEUFCMA_prfMAC' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PseudorandomFunction.oneTimeEUFCMA_prfMAC

end ComplexityTests.Crypto.MAC
