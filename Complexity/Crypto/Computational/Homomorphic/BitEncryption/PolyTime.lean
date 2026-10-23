/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.BitEncryption
public import Complexity.Crypto.Computational.Homomorphic.Efficiency
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Tactic.PPT

/-!
# Native runtime of bit-encryption hybrids

The certificates construct the zero prefix, encrypt the surrounding words, and copy the supplied
challenge ciphertext into its final position. All supplied data and every output ciphertext are
charged. No semantic correctness or width assumption is needed.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.isPPTOn_encryptBitsHybrid`: encrypt the actual mixed word.
* `Cslib.Crypto.Homomorphic.Scheme.isPPTOn_spliceEncryptedBit`: insert an encrypted challenge
  between independently encrypted surrounding words.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Scheme

open Probability Turing.MultiTapeTM

variable {E : Scheme}
  (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => E.encrypt p.1 p.2.1 p.2.2))
  {α : Type} {input : α ↪ List Bool} {n cut before : α → ℕ}
  {pk bits after challenge : α → List Bool}

include hencrypt

/-- Encrypt the mixed word, preserving its length even when the unary cut exceeds it. -/
@[fun_prop]
theorem isPPTOn_encryptBitsHybrid
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hpk : ComputableTidilyInPolyTime pk input encBits)
    (hbits : ComputableTidilyInPolyTime bits input encBits)
    (hcut : ComputableTidilyInPolyTime cut input encUnary) :
    IsPPTOn input (encList encBits)
      (fun a => E.encryptBitsHybrid (n a) (pk a) (bits a) (cut a)) := by
  apply isPPTOn_encryptBits hencrypt hn hpk
  fun_prop

/-- Copy the full supplied ciphertext between independently encrypted zero and original words. -/
@[fun_prop]
theorem isPPTOn_spliceEncryptedBit
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hpk : ComputableTidilyInPolyTime pk input encBits)
    (hbefore : ComputableTidilyInPolyTime before input encUnary)
    (hafter : ComputableTidilyInPolyTime after input encBits)
    (hchallenge : ComputableTidilyInPolyTime challenge input encBits) :
    IsPPTOn input (encList encBits)
      (fun a => E.spliceEncryptedBit (n a) (pk a) (before a) (after a) (challenge a)) := by
  have hfront := isPPTOn_encryptBits hencrypt hn hpk
    (show ComputableTidilyInPolyTime (fun a => List.replicate (before a) false)
      input encBits by fun_prop)
  have hback := isPPTOn_encryptBits hencrypt hn hpk hafter
  unfold spliceEncryptedBit
  ppt

end Cslib.Crypto.Homomorphic.Scheme
