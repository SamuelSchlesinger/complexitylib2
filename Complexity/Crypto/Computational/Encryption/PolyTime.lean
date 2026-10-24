/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Encryption.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Tactic.PPT

/-!
# Native runtime of the chosen-message experiment

The actual experiment composes key generation, message selection, encryption and guessing.
Native certificates charge the complete sampled public key, saved adversary state and challenge
ciphertext; no independent bound on those intermediate values is assumed.

## Main results

* `Cslib.Crypto.Encryption.isPPTOn_game`: the experiment is uniform strict PPT when its inputs
  are efficiently computed and the honest algorithms and adversary have native certificates.
* `Cslib.Crypto.Encryption.exists_keyLength_bound`: key generation supplies an executable unary
  polynomial bounding all supported public and secret keys.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 11.2, Attack Game 11.1.
-/

@[expose] public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM

/-- The actual chosen-message experiment has a strict clock in the full encoded caller input. -/
@[fun_prop]
theorem isPPTOn_game {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    {adversary : Adversary} (hadversary : adversary.IsPPT)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {bit : α → Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hbit : ComputableInPolyTime bit input encBool) :
    IsPPTOn input encBool (fun a => game keyGen encrypt adversary (bit a) (n a)) := by
  have hchoose := hadversary.choose
  have hguess := hadversary.guess
  unfold game
  ppt

/-- Strict PPT key generation supplies an executable unary polynomial bounding the total public
and secret key material on every supported execution. No width function is assumed computable. -/
theorem exists_keyLength_bound {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen) :
    ∃ c d : ℕ,
      ComputableTidilyInPolyTime (fun n => c * (n + 1) ^ d) encUnary encUnary ∧
      ∀ n keys, keys ∈ (ProbComp.eval (keyGen n)).support →
        keys.1.length + keys.2.length ≤ c * (n + 1) ^ d := by
  obtain ⟨c, d, hlength⟩ := hkeyGen.length_le
  refine ⟨c, d, ComputableInPolyTime.tidy (by fun_prop), fun n keys hkeys => ?_⟩
  have hbound := hlength n keys hkeys
  simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate] at hbound
  omega

end Cslib.Crypto.Encryption
