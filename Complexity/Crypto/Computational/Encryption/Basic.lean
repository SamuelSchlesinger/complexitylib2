/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.Parameter
public import Complexity.Crypto.Game

/-!
# Chosen-message security for bit encryption

The adversary receives the public key, chooses two bits and saves a finite state, then receives
an encryption of the selected bit. Both stages are single uniform strict PPT algorithms. Their
clocks charge the unary security parameter and the complete encoded input, including the saved
state. The adversary may retain the public key in that state.

This is the single-challenge public-key experiment of
[Boneh and Shoup, Section 11.2, Attack Game 11.1][BonehShoup2023], specialized to bit messages.
For public-key encryption, further encryptions can be computed from the public key. The separate
multi-challenge equivalence of their Theorem 11.1 is not formalized here. Encryption correctness
and efficiency of the honest algorithms remain separate properties.

## Main definitions

* `Cslib.Crypto.Encryption.Adversary`: message selection and guessing with explicit saved state.
* `Cslib.Crypto.Encryption.Adversary.IsPPT`: native uniform admissibility of both stages.
* `Cslib.Crypto.Encryption.game`: the actual key-generation and challenge-encryption experiment.
* `Cslib.Crypto.Encryption.INDCPA`: negligible distinguishing advantage for every admissible
  adversary, fixed before the security parameter.

## Main results

* `Cslib.Crypto.Encryption.eval_game`: the experiment depends only on the public-key marginal.
* `Cslib.Crypto.Encryption.INDCPA.congr`: distributionally equal honest algorithms have the same
  security guarantee.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 11.2 and Section 11.3.2.
-/

@[expose] public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM

/-- A chosen-message adversary. The saved word contains all data retained between stages. -/
structure Adversary where
  /-- Receive the public key, choose the two challenge messages, and save a state. -/
  choose : ℕ → List Bool → ProbComp ((Bool × Bool) × List Bool)
  /-- Receive the saved state and challenge ciphertext, then return a distinguishing bit. -/
  guess : ℕ → List Bool → List Bool → ProbComp Bool

/-- One finite-machine certificate for each whole stage, including the full saved-state cost.
There is no parameter-dependent advice or separate algorithm for each security parameter. -/
structure Adversary.IsPPT (adversary : Adversary) : Prop where
  /-- Message selection is uniform strict PPT on the parameter and public key. -/
  choose : Probability.IsPPT (encPair (encPair encBool encBool) encBits) adversary.choose
  /-- Guessing is uniform strict PPT on the parameter, saved state, and challenge ciphertext. -/
  guess : IsPPTOn (encPair encUnary (encPair encBits encBits)) encBool
    (fun p => adversary.guess p.1 p.2.1 p.2.2)

/-- Sample the key pair and the chosen challenge encryption using the honest algorithms.
The secret key is never passed to the adversary. -/
def game (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : Adversary) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let choice ← adversary.choose n keys.1
  let ciphertext ← encrypt n keys.1 (if bit then choice.1.2 else choice.1.1)
  adversary.guess n choice.2 ciphertext

/-- Single-challenge IND-CPA for bit encryption against every uniform strict PPT adversary.
The negligible bound may depend on the adversary, which is fixed before the parameter. -/
def INDCPA (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (game keyGen encrypt adversary false n))
    (fun adversary n => ProbComp.eval (game keyGen encrypt adversary true n)) Adversary.IsPPT

/-- Only the public-key marginal of key generation is observed by the experiment. -/
theorem eval_game (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : Adversary) (bit : Bool) (n : ℕ) :
    ProbComp.eval (game keyGen encrypt adversary bit n) =
      ((ProbComp.eval (keyGen n)).map Prod.fst).bind (fun pk =>
        (ProbComp.eval (adversary.choose n pk)).bind (fun choice =>
          (ProbComp.eval (encrypt n pk (if bit then choice.1.2 else choice.1.1))).bind
            (fun ciphertext => ProbComp.eval (adversary.guess n choice.2 ciphertext)))) := by
  simp only [game, ProbComp.eval_bind, PMF.bind_map, Function.comp_def]

/-- Equal public-key marginals and equal encryption laws preserve security. -/
theorem INDCPA.congr {keyGen keyGen' : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt encrypt' : ℕ → List Bool → Bool → ProbComp (List Bool)}
    (h : INDCPA keyGen encrypt)
    (hkeyGen : ∀ n, (ProbComp.eval (keyGen n)).map Prod.fst =
      (ProbComp.eval (keyGen' n)).map Prod.fst)
    (hencrypt : ∀ n pk bit, ProbComp.eval (encrypt n pk bit) =
      ProbComp.eval (encrypt' n pk bit)) : INDCPA keyGen' encrypt' := by
  intro adversary hadversary
  simpa only [eval_game, hkeyGen, hencrypt] using h adversary hadversary

end Cslib.Crypto.Encryption
