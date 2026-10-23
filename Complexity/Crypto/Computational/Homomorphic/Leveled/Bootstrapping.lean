/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.Leveled.Correctness
public import Complexity.Crypto.Computational.Homomorphic.Leveled.Security
public import Complexity.Crypto.Computational.Homomorphic.Leveled.PolyTime

/-!
# Correct, compact and secure acyclic leveled encryption

The independently proved correctness, exact width, native runtime and IND-CPA results apply to
the same constructed scheme. This module assembles correctness, budget-independent polynomial
widths and security without assuming those conclusions for the output scheme. Native certificates
for its algorithms remain available in `Leveled.PolyTime`.

The contract evaluates fresh ciphertexts under an efficiently computed unary depth budget. It
does not promise arbitrary reuse of evaluated wrapper ciphertexts, circuit privacy, a concrete
base scheme, or fixed-key evaluation without a predetermined budget.

## Main results

* `Cslib.Crypto.Homomorphic.Leveled.correct_fixedWidth_indCPA`: a correct, secure constructed
  scheme with exact polynomial secret and ciphertext widths independent of the depth budget.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2,
  Theorems 3 and 4][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Leveled

open Circuits Probability Turing.MultiTapeTM

/-- Assemble the actual construction's correctness, exact compact widths and IND-CPA security.
The native decryption-circuit generator bounds both widths; no output property is an input
hypothesis. Evaluation runtime additionally uses the base evaluator certificate, as stated by
`isPPTOn_scheme_evaluate`. -/
theorem correct_fixedWidth_indCPA {E : Scheme} {secretWidth ciphertextWidth budget : ℕ → ℕ}
    (D : DecryptionCircuits E secretWidth ciphertextWidth)
    (hE : E.Correct) (hwidth : E.FixedWidth secretWidth ciphertextWidth)
    (hboot : Scheme.Bootstrappable D)
    (hsecure : Encryption.INDCPA E.keyGen E.encrypt)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun p => E.encrypt p.1 p.2.1 p.2.2))
    (hD : ComputableTidilyInPolyTime
      (fun n => (⟨_, D.circuit n⟩ : Σ m, Circuit Boolean.signature m 1))
      encUnary (Boolean.encCircuit 1))
    (hbudget : ComputableTidilyInPolyTime budget encUnary encUnary) :
    (scheme D budget).Correct ∧
      (scheme D budget).FixedWidth (fun n => 3 * secretWidth n + 1)
        (fun n => ciphertextWidth n + 1) ∧
      PolynomiallyBounded (fun n => 3 * secretWidth n + 1) ∧
      PolynomiallyBounded (fun n => ciphertextWidth n + 1) ∧
      Encryption.INDCPA (scheme D budget).keyGen (scheme D budget).encrypt :=
  ⟨correct D hE hwidth hboot budget, fixedWidth D hE hwidth hboot budget,
    (polynomiallyBounded_widths D hD).1, (polynomiallyBounded_widths D hD).2,
    indCPA_scheme hsecure hkeyGen hencrypt hwidth.secret_length hbudget D⟩

end Cslib.Crypto.Homomorphic.Leveled
