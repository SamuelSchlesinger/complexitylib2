/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.Leveled.Basic
public import Complexity.Crypto.Computational.Homomorphic.KeyChain.Hybrid
public import Complexity.Crypto.Computational.Encryption.Basic

/-!
# Chosen-message experiments for the leveled construction

The public-artifact experiment lets the adversary choose its messages after receiving the entire
serialized key chain. The zero-link reduction places the base challenge public key first and
generates every later key itself. A generated secret supplies the first zero link's length;
when the chain has no links, that length is unused. Its guessing stage retains the adversary's
exact state and adds the ordinary fresh-ciphertext tag to the base challenge.

## Main definitions

* `Cslib.Crypto.Homomorphic.Leveled.publicKeyGame`: adaptive message selection on a public artifact.
* `Cslib.Crypto.Homomorphic.Leveled.zeroLinkAdversary`: the actual two-stage base reduction.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2][Gentry2009]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Section 11.2][BonehShoup2023]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Leveled

/-- Choose both messages after seeing every public key and encrypted link, then give the tagged
challenge ciphertext to the guessing stage together with its unchanged saved state. -/
def publicKeyGame (E : Scheme) (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ)
    (artifact : List (List Bool) × List (List (List Bool))) : ProbComp Bool := do
  let choice ← adversary.choose n (encPublicKey artifact)
  let ciphertext ← E.encrypt n (artifact.1.getD 0 [])
    (if bit then choice.1.2 else choice.1.1)
  adversary.guess n choice.2 (false :: ciphertext)

/-- Simulate the all-zero chain using the challenge key as its initial public key. The unknown
challenge secret is never read or saved; only independently generated secrets supply lengths. -/
def zeroLinkAdversary (E : Scheme) (depth : ℕ → ℕ)
    (adversary : Encryption.Adversary) : Encryption.Adversary where
  choose n challengePk := do
    let rest ← OracleComp.replicate (depth n) (E.keyGen n)
    let links ← E.encryptZeroKeyLinks n
      ((challengePk, (rest.headD ([], [])).2) :: rest)
    adversary.choose n (encPublicKey (challengePk :: rest.map Prod.fst, links))
  guess n state ciphertext := adversary.guess n state (false :: ciphertext)

end Cslib.Crypto.Homomorphic.Leveled
