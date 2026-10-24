/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.DiffieHellman
public import Complexity.Crypto.Computational.Encryption.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Crypto.Negligible.Basic
import Complexity.Probability.PMF
import Complexity.Tactic.PPT
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite

/-!
# ElGamal encryption and IND-CPA security under DDH

Over a `PrimeOrderGroupFamily`, ElGamal public-key encryption ([BonehShoup2023], Section 11.4) uses
a group description `d`, a secret exponent `α : ZMod (F.order d)`, and the public key `u = α • g`.
To encrypt a group element `m : F.Carrier d` with randomness `β : ZMod (F.order d)`, the sender
forms the ciphertext `(v, e) = (β • g, β • u + m) = (β • g, (α * β) • g + m)`. Decryption recovers
`e - α • v = m`, and encoded decryption (`decodeElGamal`) computes this in polynomial time from
`(d, a, encode v, encode e)` using `F.order`, `F.smul`, and `F.add`.

For bit encryption, `false` and `true` are embedded as the distinct group elements `0` and `g`
(`bitElement`, encoded in polynomial time by `encodeBit`). In the chosen-plaintext experiment
(`elGamalCPAGame`), an `Encryption.Adversary` receives the encoded public key `(d, encode (α • g))`,
chooses two challenge bits with a saved state word, and receives an ElGamal encryption of the
selected challenge bit. Replacing the Diffie–Hellman mask `(α * β) • g` with an independent uniform
`γ • g` masks the message perfectly (`uniform_smul_generator_add`), reducing IND-CPA security of
ElGamal encryption directly to the Decisional Diffie–Hellman assumption (`DDH.elGamalINDCPA`,
[BonehShoup2023], Theorem 11.1).

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalDecrypt`: algebraic ElGamal encryption and decryption.
* `Cslib.Crypto.PrimeOrderGroupFamily.decodeElGamal`: polynomial-time decryption on encoded group
  elements.
* `Cslib.Crypto.PrimeOrderGroupFamily.bitElement`, `Cslib.Crypto.PrimeOrderGroupFamily.encodeBit`:
  embedding and polynomial-time encoding of message bits as group elements.
* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalCPAGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalINDCPA`: the IND-CPA experiment and security property
  for ElGamal bit encryption.
* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalToDDHDistinguisher`: the DDH reduction distinguisher.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalDecrypt_elGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.decodeElGamal_encode`: decryption correctness.
* `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_decodeElGamal`: encoded decryption is
  computable in polynomial time.
* `Cslib.Crypto.PrimeOrderGroupFamily.smul_generator_surjective`,
  `Cslib.Crypto.PrimeOrderGroupFamily.uniform_smul_generator_add`: `α ↦ α • g` is surjective and
  `γ • g + m` is uniformly distributed over `F.Carrier d`.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_elGamalCPAGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_elGamalToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.elGamalINDCPA`: ElGamal IND-CPA security under DDH
  ([BonehShoup2023], Theorem 11.1).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 11.4, Theorem 11.1.
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM

variable (F : PrimeOrderGroupFamily)

/-! ### Group-element ElGamal encryption and decryption -/

/-- Algebraic ElGamal encryption of a group element `m : F.Carrier d` under public key
`u : F.Carrier d` with randomness `β : ZMod (F.order d)`. -/
def elGamalEncrypt (d : F.Desc) (u m : F.Carrier d) (β : ZMod (F.order d)) :
    F.Carrier d × F.Carrier d :=
  (β • F.generator d, β • u + m)

/-- Under a genuine public key `u = α • g`, the second ciphertext component is
`(α * β) • g + m`. -/
theorem elGamalEncrypt_smul_generator (d : F.Desc) (α β : ZMod (F.order d)) (m : F.Carrier d) :
    F.elGamalEncrypt d (α • F.generator d) m β =
      (β • F.generator d, (α * β) • F.generator d + m) := by
  simp only [elGamalEncrypt, smul_smul, mul_comm β α]

/-- Algebraic ElGamal decryption of a ciphertext pair `(v, e)` using secret key
`α : ZMod (F.order d)`. -/
def elGamalDecrypt (d : F.Desc) (α : ZMod (F.order d)) (ct : F.Carrier d × F.Carrier d) :
    F.Carrier d :=
  ct.2 - α • ct.1

/-- **ElGamal decryption correctness**: decrypting an encryption under `u = α • g` with secret key
`α` recovers the message `m`. -/
@[simp] theorem elGamalDecrypt_elGamalEncrypt (d : F.Desc) (α β : ZMod (F.order d))
    (m : F.Carrier d) :
    F.elGamalDecrypt d α (F.elGamalEncrypt d (α • F.generator d) m β) = m := by
  simp only [elGamalDecrypt, elGamalEncrypt, smul_smul, mul_comm β α, add_sub_cancel_left]

/-- Decryption on encoded group elements: given `(d, a, encode v, encode e)`, compute
`encode (e - a • v)` as `F.add (d, encode e, F.smul (d, F.order d - a % F.order d, encode v))`. -/
def decodeElGamal (input : F.Desc × ℕ × List Bool × List Bool) : List Bool :=
  F.add (input.1, input.2.2.2,
    F.smul (input.1, F.order input.1 - input.2.1 % F.order input.1, input.2.2.1))

/-- `decodeElGamal` computes `encode (elGamalDecrypt d a (v, e))` on encoded group elements. -/
theorem decodeElGamal_encode (d : F.Desc) (a : ℕ) (v e : F.Carrier d) :
    F.decodeElGamal (d, a, F.encode d v, F.encode d e) =
      F.encode d (F.elGamalDecrypt d (a : ZMod (F.order d)) (v, e)) := by
  have hneg : ((F.order d - a % F.order d : ℕ) : ZMod (F.order d)) = -(a : ZMod (F.order d)) := by
    rw [Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt _ (F.prime_order d).pos)), ZMod.natCast_self,
      ZMod.natCast_mod, zero_sub]
  simp only [decodeElGamal, F.smul_encode, hneg, neg_smul, F.add_encode, elGamalDecrypt,
    sub_eq_add_neg]

/-- Encoded ElGamal decryption of an honest encryption recovers the encoded message. -/
@[simp] theorem decodeElGamal_elGamalEncrypt (d : F.Desc) (a : ℕ) (β : ZMod (F.order d))
    (m : F.Carrier d) :
    F.decodeElGamal (d, a,
      F.encode d (F.elGamalEncrypt d ((a : ZMod (F.order d)) • F.generator d) m β).1,
      F.encode d (F.elGamalEncrypt d ((a : ZMod (F.order d)) • F.generator d) m β).2) =
      F.encode d m := by
  rw [F.decodeElGamal_encode, F.elGamalDecrypt_elGamalEncrypt]

/-- Encoded ElGamal decryption is computable in polynomial time. -/
theorem computableInPolyTime_decodeElGamal :
    ComputableInPolyTime F.decodeElGamal
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encBits := by
  have hd : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => input.1)
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) F.encDesc := by fun_prop
  have ha : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => input.2.1)
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encNat := by fun_prop
  have hv : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => input.2.2.1)
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encBits := by fun_prop
  have he : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => input.2.2.2)
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encBits := by fun_prop
  have horder : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => F.order input.1)
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encNat :=
    F.computableInPolyTime_order.tidy.comp hd
  have hexp : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool =>
        F.order input.1 - input.2.1 % F.order input.1)
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encNat :=
    .binary_sub' horder (.binary_mod' ha horder)
  have hsmul := F.computableInPolyTime_smul.tidy.comp (hd.prod (hexp.prod hv))
  exact ComputableInPolyTime.of_tidy
    (F.computableInPolyTime_add.tidy.comp (hd.prod (he.prod hsmul)))

/-! ### Surjectivity of the generator map and the one-time group mask -/

/-- Every element of `F.Carrier d` is a scalar multiple of the generator: `α ↦ α • g` is
surjective. -/
theorem smul_generator_surjective (d : F.Desc) :
    Function.Surjective fun α : ZMod (F.order d) => α • F.generator d := by
  have : Finite (F.Carrier d) :=
    Nat.finite_of_card_ne_zero (by rw [F.card_carrier d]; exact (F.prime_order d).ne_zero)
  exact ((F.smul_generator_injective d).bijective_of_nat_card_le
    (by rw [F.card_carrier, Nat.card_zmod])).2

/-- **One-time group mask**: for any group element `m : F.Carrier d`, masking `m` by `γ • g` for a
uniform `γ : ZMod (F.order d)` has the same distribution as `γ • g` itself. -/
theorem uniform_smul_generator_add {α : Type*} (d : F.Desc) (m : F.Carrier d)
    (f : F.Carrier d → PMF α) :
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ => f (γ • F.generator d + m)) =
      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ => f (γ • F.generator d) := by
  obtain ⟨μ, rfl⟩ := F.smul_generator_surjective d m
  simp only [← add_smul]
  change (PMF.uniformOfFintype (ZMod (F.order d))).bind
      ((fun γ => f (γ • F.generator d)) ∘ Equiv.addRight μ) =
    (PMF.uniformOfFintype (ZMod (F.order d))).bind (fun γ => f (γ • F.generator d))
  rw [← PMF.bind_map, PMF.uniformOfFintype_map_equiv]

/-! ### Bit encryption and IND-CPA security under DDH -/

/-- Embed a message bit `b : Bool` into `F.Carrier d` as `0` (for `false`) or `g` (for `true`). -/
def bitElement (d : F.Desc) (b : Bool) : F.Carrier d :=
  if b then F.generator d else 0

/-- Distinct message bits map to distinct group elements. -/
theorem bitElement_injective (d : F.Desc) : Function.Injective (F.bitElement d) := by
  intro b₁ b₂ h
  cases b₁ <;> cases b₂
  · rfl
  · exact absurd h.symm (F.generator_ne_zero d)
  · exact absurd h (F.generator_ne_zero d)
  · rfl

/-- Encode a message bit `b : Bool` as an encoded element of `F.Carrier d` using `F.smul`. -/
def encodeBit (d : F.Desc) (b : Bool) : List Bool :=
  F.smul (d, if b then 1 else 0, F.encode d (F.generator d))

/-- `encodeBit` computes the group encoding of `bitElement`. -/
@[simp] theorem encodeBit_eq_encode_bitElement (d : F.Desc) (b : Bool) :
    F.encodeBit d b = F.encode d (F.bitElement d b) := by
  cases b <;> simp [encodeBit, bitElement, F.smul_encode]

/-- `encodeBit` is computable in polynomial time from the group description and the bit. -/
theorem computableInPolyTime_encodeBit :
    ComputableInPolyTime (fun p : F.Desc × Bool => F.encodeBit p.1 p.2)
      (encPair F.encDesc encBool) encBits := by
  have hd : ComputableTidilyInPolyTime (fun p : F.Desc × Bool => p.1)
      (encPair F.encDesc encBool) F.encDesc := by fun_prop
  have hgen : ComputableTidilyInPolyTime
      (fun p : F.Desc × Bool => F.encode p.1 (F.generator p.1))
      (encPair F.encDesc encBool) encBits :=
    F.computableInPolyTime_generator.tidy.comp hd
  have hbit : ComputableTidilyInPolyTime (fun p : F.Desc × Bool => if p.2 then 1 else 0)
      (encPair F.encDesc encBool) encNat :=
    (ComputableTidilyInPolyTime.snd _ _).cond
      (ComputableTidilyInPolyTime.const 1) (ComputableTidilyInPolyTime.const 0)
  exact ComputableInPolyTime.of_tidy
    (F.computableInPolyTime_smul.tidy.comp (hd.prod (hbit.prod hgen)))

/-- The IND-CPA experiment for ElGamal bit encryption ([BonehShoup2023], Section 11.4): draw `d`
from `setup n` and a uniform secret key `α : ZMod (F.order d)`, pass the encoded public key
`(d, encode (α • g))` to `adversary.choose`, encrypt the selected challenge bit under a fresh
uniform exponent `β : ZMod (F.order d)`, and pass the saved state and encoded ciphertext to
`adversary.guess`. -/
noncomputable def elGamalCPAGame (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
  let choice ← ProbComp.eval (adversary.choose n pk)
  let m := if bit then choice.1.2 else choice.1.1
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let ct := encPair encBits encBits
    (F.encode d (β • F.generator d),
      F.encode d ((α * β) • F.generator d + F.bitElement d m))
  ProbComp.eval (adversary.guess n choice.2 ct)

/-- IND-CPA security of ElGamal bit encryption over `F` for a setup law `setup`: every uniform
strict PPT `Encryption.Adversary` has negligible distinguishing advantage between challenge bit
`false` and challenge bit `true`. -/
def elGamalINDCPA (setup : ℕ → PMF F.Desc) : Prop :=
  Game.Indistinguishable
    (fun adversary n => F.elGamalCPAGame setup adversary false n)
    (fun adversary n => F.elGamalCPAGame setup adversary true n)
    Encryption.Adversary.IsPPT

/-- The DDH distinguisher constructed from an IND-CPA adversary ([BonehShoup2023], proof of
Theorem 11.1): given `(d, u, v, w)`, pass `(d, u)` as the public key, encrypt the selected
challenge bit by masking with `w`, and return the adversary's guess. -/
def elGamalToDDHDistinguisher (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool := do
  let pk := encPair F.encDesc encBits (input.1, input.2.1)
  let choice ← adversary.choose n pk
  let m := if bit then choice.1.2 else choice.1.1
  let ct := encPair encBits encBits
    (input.2.2.1, F.add (input.1, input.2.2.2, F.encodeBit input.1 m))
  adversary.guess n choice.2 ct

/-- In the real DDH game, `elGamalToDDHDistinguisher` simulates `elGamalCPAGame` exactly. -/
@[simp] theorem ddhRealGame_elGamalToDDHDistinguisher (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    F.ddhRealGame setup (F.elGamalToDDHDistinguisher adversary bit) n =
      F.elGamalCPAGame setup adversary bit n := by
  simp only [ddhRealGame, elGamalToDDHDistinguisher, elGamalCPAGame, ProbComp.eval_bind,
    PMF.monad_bind_eq_bind, F.encodeBit_eq_encode_bitElement, F.add_encode]
  congr 1; funext d
  congr 1; funext α
  rw [PMF.bind_comm]

/-- In the ideal DDH game, the uniform element `γ • g` perfectly masks the challenge bit, so the
experiments for `bit = false` and `bit = true` are identical. -/
theorem ddhIdealGame_elGamalToDDHDistinguisher_false_eq_true (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.Adversary) (n : ℕ) :
    F.ddhIdealGame setup (F.elGamalToDDHDistinguisher adversary false) n =
      F.ddhIdealGame setup (F.elGamalToDDHDistinguisher adversary true) n := by
  simp only [ddhIdealGame, elGamalToDDHDistinguisher, ProbComp.eval_bind, PMF.monad_bind_eq_bind,
    F.encodeBit_eq_encode_bitElement, F.add_encode, Bool.false_eq_true, ↓reduceIte]
  congr 1; funext d
  congr 1; funext α
  congr 1; funext β
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  congr 1; funext choice
  exact (F.uniform_smul_generator_add d (F.bitElement d choice.1.1)
    (fun x => ProbComp.eval (adversary.guess n choice.2
      (encPair encBits encBits (F.encode d (β • F.generator d), F.encode d x))))).trans
    (F.uniform_smul_generator_add d (F.bitElement d choice.1.2)
      (fun x => ProbComp.eval (adversary.guess n choice.2
        (encPair encBits encBits (F.encode d (β • F.generator d), F.encode d x))))).symm

/-- **Quantitative reduction of ElGamal IND-CPA to DDH** ([BonehShoup2023], Theorem 11.1): the
IND-CPA distinguishing advantage of `adversary` is bounded by the sum of the DDH advantages of
`elGamalToDDHDistinguisher adversary false` and `elGamalToDDHDistinguisher adversary true`. -/
theorem advantage_elGamalCPAGame_le (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.Adversary) (n : ℕ) :
    Game.advantage (F.elGamalCPAGame setup adversary false n)
      (F.elGamalCPAGame setup adversary true n) ≤
      Game.advantage (F.ddhRealGame setup (F.elGamalToDDHDistinguisher adversary false) n)
        (F.ddhIdealGame setup (F.elGamalToDDHDistinguisher adversary false) n) +
      Game.advantage (F.ddhRealGame setup (F.elGamalToDDHDistinguisher adversary true) n)
        (F.ddhIdealGame setup (F.elGamalToDDHDistinguisher adversary true) n) := by
  rw [← F.ddhRealGame_elGamalToDDHDistinguisher setup adversary false n,
    ← F.ddhRealGame_elGamalToDDHDistinguisher setup adversary true n]
  refine (Game.advantage_triangle _
    (F.ddhIdealGame setup (F.elGamalToDDHDistinguisher adversary false) n) _).trans ?_
  rw [F.ddhIdealGame_elGamalToDDHDistinguisher_false_eq_true setup adversary n,
    Game.advantage_comm (F.ddhIdealGame setup (F.elGamalToDDHDistinguisher adversary true) n)]

/-- `elGamalToDDHDistinguisher` is uniform strict PPT whenever `adversary` is. -/
theorem isPPTOn_elGamalToDDHDistinguisher {adversary : Encryption.Adversary}
    (hA : adversary.IsPPT) (bit : Bool) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => F.elGamalToDDHDistinguisher adversary bit input.1 input.2) := by
  have hchoose := hA.choose
  have hguess := hA.guess
  have hadd := F.computableInPolyTime_add.tidy
  have hencBit := F.computableInPolyTime_encodeBit.tidy
  have hpk : ComputableTidilyInPolyTime
      (fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
        encPair F.encDesc encBits (input.2.1, input.2.2.1))
      (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBits :=
    (ComputableTidilyInPolyTime.encode (encPair F.encDesc encBits)).comp (by fun_prop)
  have hm : ComputableTidilyInPolyTime
      (fun p : (ℕ × F.Desc × List Bool × List Bool × List Bool) × (Bool × Bool) × List Bool =>
        if bit then p.2.1.2 else p.2.1.1)
      (encPair (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
        (encPair (encPair encBool encBool) encBits))
      encBool := by
    cases bit <;> fun_prop
  have hct : ComputableTidilyInPolyTime
      (fun p : (ℕ × F.Desc × List Bool × List Bool × List Bool) × (Bool × Bool) × List Bool =>
        (p.1.1, p.2.2, encPair encBits encBits
          (p.1.2.2.2.1,
            F.add (p.1.2.1, p.1.2.2.2.2,
              F.encodeBit p.1.2.1 (if bit then p.2.1.2 else p.2.1.1)))))
      (encPair (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
        (encPair (encPair encBool encBool) encBits))
      (encPair encUnary (encPair encBits encBits)) := by
    refine ComputableTidilyInPolyTime.prod (by fun_prop) ?_
    refine ComputableTidilyInPolyTime.prod (by fun_prop) ?_
    exact (ComputableTidilyInPolyTime.encode (encPair encBits encBits)).comp (by fun_prop)
  unfold elGamalToDDHDistinguisher
  exact (hchoose.preprocess (by fun_prop) hpk).bind_with (hguess.preprocess hct)

/-- **ElGamal bit encryption is IND-CPA secure under the DDH assumption**
([BonehShoup2023], Theorem 11.1). -/
theorem DDH.elGamalINDCPA {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (hDDH : F.DDH setup) : F.elGamalINDCPA setup := by
  intro adversary hA
  exact negligible_of_le
    ((hDDH _ (F.isPPTOn_elGamalToDDHDistinguisher hA false)).add
      (hDDH _ (F.isPPTOn_elGamalToDDHDistinguisher hA true)))
    (F.advantage_elGamalCPAGame_le setup adversary)

end Cslib.Crypto.PrimeOrderGroupFamily
