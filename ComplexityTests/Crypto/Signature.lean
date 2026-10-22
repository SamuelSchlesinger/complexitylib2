/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.OneWayToSignature
import Complexity.Crypto.Computational.Signature

/-!
# Tests for digital signature schemes, Lamport's one-time signature scheme, and OWF reductions

Provides concrete instantiations of `SignatureScheme` (both a trivial scheme and `lamportScheme`
applied to the identity function), verifies that `OneTimeEUFCMA` and `EUFCMA` reject the trivial
scheme via an explicit zero-query PPT forger, and audits the axiom dependencies of the headline
theorems in `Complexity.Crypto.Computational.Signature` and
`Complexity.Crypto.Computational.OneWayToSignature`.
-/

namespace ComplexityTests.Crypto.Signature

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-- Concrete trivial signature scheme where every signature is accepted. Used to witness that the
`SignatureScheme` fields are jointly satisfiable and to verify that `OneTimeEUFCMA` and `EUFCMA`
reject insecure schemes. -/
noncomputable def trivialSignatureScheme : SignatureScheme where
  keyGen _ := pure ([], [])
  sign _ msg := pure msg
  verify _ _ _ := true
  keyGen_ppt := by ppt
  sign_ppt := by ppt
  verify_polyTime := by polytime
  verify_sign := by
    intro _ _ _ _ _ _ _
    rfl

/-- Concrete instantiation of `lamportScheme` on the identity function. -/
noncomputable def idLamportScheme : SignatureScheme :=
  lamportScheme (fun x => x) .id'

/-- The trivial signature scheme is not one-time EUF-CMA secure: a zero-query PPT forger that
outputs `(0^n, [])` succeeds with probability `1`. -/
theorem not_oneTimeEUFCMA_trivialSignatureScheme :
    ¬ trivialSignatureScheme.OneTimeEUFCMA := by
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
        (ProbComp.eval (trivialSignatureScheme.eufOneTimeGame forger n)) = 1 := by
    simp [SignatureScheme.eufOneTimeGame, trivialSignatureScheme, forger, Game.succProbability]
  simp only [heval] at hneg
  exact not_negligible_const one_ne_zero hneg

/-- The trivial signature scheme is not EUF-CMA secure. -/
theorem not_eufCMA_trivialSignatureScheme :
    ¬ trivialSignatureScheme.EUFCMA :=
  fun h => not_oneTimeEUFCMA_trivialSignatureScheme h.oneTimeEUFCMA

/--
info: 'Cslib.Crypto.SignatureScheme.EUFCMA.oneTimeEUFCMA' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.SignatureScheme.EUFCMA.oneTimeEUFCMA

/--
info: 'Cslib.Crypto.SignatureScheme.OneTimeEUFCMA.exists_oneWay' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.SignatureScheme.OneTimeEUFCMA.exists_oneWay

/--
info: 'Cslib.Crypto.SignatureScheme.EUFCMA.exists_oneWay' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.SignatureScheme.EUFCMA.exists_oneWay

/--
info: 'Cslib.Crypto.OneWay.oneTimeEUFCMA_lamport' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.OneWay.oneTimeEUFCMA_lamport

/--
info: 'Cslib.Crypto.OneWay.exists_oneTimeSignature' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.OneWay.exists_oneTimeSignature

/--
info: 'Cslib.Crypto.exists_oneWay_iff_exists_oneTimeSignature' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.exists_oneWay_iff_exists_oneTimeSignature

end ComplexityTests.Crypto.Signature
