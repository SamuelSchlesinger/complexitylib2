/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Game
public import Complexity.Foundations.Data.BitString.Basic
public import Complexity.Languages.Probabilistic.QueryCount
public import Complexity.Languages.Probabilistic.Sum
public import Mathlib.Data.Fintype.Perm
import Complexity.Probability.BitString
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Uniform
import Complexity.Probability.Uniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Even–Mansour cipher in the ideal-permutation model

The Even–Mansour construction ([BonehShoup2023], Section 4.7; [EvenMansour1997]) builds a block
cipher from a single public permutation `π : Equiv.Perm G` on a finite group `G` by XORing (or
adding in `G`) independent pre-whitening and post-whitening keys `(k₀, k₁) ∈ G × G`:
$$E((k_0, k_1), x) = \pi(x + k_0) + k_1, \qquad D((k_0, k_1), y) = \pi^{-1}(y - k_1) - k_0.$$
In the single-key variant ([DunkelmanKellerShamir2012]), `k₀ = k₁ = k`.

We formalize four aspects of the Even–Mansour construction:

1. **Algebraic structure and one-query secrecy**: `evenMansourEquiv π k₀ k₁ : Equiv.Perm G`
   bundles encryption and decryption as a permutation of `G`, satisfies the inverse-cipher
   conjugation law `(evenMansourEquiv π k₀ k₁).symm = evenMansourEquiv π.symm (-k₁) (-k₀)` (which
   swaps `k₀` and `k₁` over any group of exponent two such as `BitString n`), acts as a bijection
   on `Equiv.Perm G` for every fixed key pair (`evenMansourPermEquiv`), and achieves perfect
   one-query secrecy for any fixed `π` (`map_prod_evenMansourEncrypt_uniformOfFintype`).
2. **Necessity of both whitening keys ([BonehShoup2023], Section 4.7)**: omitting post-whitening
   (`preWhitenEquiv π k₀ x = π (x + k₀)`) or pre-whitening (`postWhitenEquiv π k₁ x = π x + k₁`)
   allows an explicit 2-query adversary (making `1` cipher query and `1` primitive permutation
   query, `IsCallBounded _ 1 1`) to recover the secret key with probability `1` and achieve
   key-recovery game advantage `1 - |G|⁻¹` against an independent uniform permutation and uniform
   target key (`advantage_preWhitenKeyRecoveryGame_eq`, `advantage_postWhitenKeyRecoveryGame_eq`).
3. **One-sided query security**: because `evenMansourPermEquiv k₀ k₁` is a bijection on
   `Equiv.Perm G`, any adversary that queries only the cipher oracle (`liftLeft`) or only the
   primitive permutation oracle (`liftRight`) has zero distinguishing advantage between the real
   Even–Mansour game and two independent uniform permutations
   (`advantage_evenMansourRealGame_liftLeft_eq_zero`,
   `advantage_evenMansourRealGame_liftRight_eq_zero`).
4. **Bad-key transcript intersection bound ([BonehShoup2023], Theorem 4.10)**: given a cipher
   transcript `T_e : List (G × G)` and a primitive permutation transcript `T_π : List (G × G)`, a
   key `(k₀, k₁)` is bad (`isBadEvenMansourKey T_e T_π k`) when some `(x, y) ∈ T_e` and
   `(u, v) ∈ T_π` collide on the internal permutation input (`x + k₀ = u`) or output
   (`y - k₁ = v`). Outside this bad set, the internal permutation queries made through the cipher
   are disjoint in both domain and range from the direct queries to `π`
   (`disjoint_of_isBadEvenMansourKey_eq_false`), and when `T_e` and `T_π` are consistent with
   `evenMansourEquiv π k₀ k₁` and `π`, output collisions reduce to input collisions
   (`isBadKeyPair_eq_decide_of_evenMansourEquiv`). Under a uniform two-key `(k₀, k₁)` or single
   key `k`, the bad-key probability is at most `2 * |T_e| * |T_π| / |G|`
   (`toOuterMeasure_isBadEvenMansourKey_toReal_le`,
   `toOuterMeasure_isBadSingleKeyEvenMansour_toReal_le`). For any adaptive distinguisher satisfying
   `IsCallBounded program Q_e Q_π`, `OracleComp.IsCostBounded.transcript_cost_le` bounds every
   supported transcript by `|T_e| ≤ Q_e` and `|T_π| ≤ Q_π`, yielding the `2 * Q_e * Q_π / |G|`
   bad-key bound on every supported execution path (`IsCallBounded.badEvenMansourKey_toReal_le`,
   `IsCallBounded.badSingleKeyEvenMansour_toReal_le`). The lazy-sampled bidirectional
   random-permutation coupling step connecting this bad-key intersection bound to full two-sided
   `Game.advantage (evenMansourRealGame program) (evenMansourIdealGame program)` remains open.

## Main definitions

* `Cslib.Crypto.EvenMansour.evenMansourEncrypt`, `evenMansourDecrypt`, `evenMansourEquiv`,
  `singleKeyEvenMansourEquiv`: Even–Mansour encryption, decryption, and bundled permutations.
* `Cslib.Crypto.EvenMansour.preWhitenEquiv`, `postWhitenEquiv`, `preWhitenKeyRecoveryAttack`,
  `postWhitenKeyRecoveryAttack`: single-whitening variants and 2-query key-recovery attacks.
* `Cslib.Crypto.EvenMansour.PermQuery`, `PermOracleSpec`, `EvenMansourSpec`, `IsCallBounded`:
  bidirectional cipher and primitive permutation oracle interface and separate query budgets.
* `Cslib.Crypto.EvenMansour.evenMansourRealGame`, `singleKeyEvenMansourRealGame`,
  `evenMansourIdealGame`: real and ideal bidirectional permutation games.
* `Cslib.Crypto.EvenMansour.isBadKeyPair`, `isBadEvenMansourKey`, `isBadSingleKeyEvenMansour`,
  `transcriptCipher`, `transcriptPerm`: bad-key collision predicates and transcript projections.

## Main results

* `Cslib.Crypto.EvenMansour.map_prod_evenMansourEncrypt_uniformOfFintype`: one-query perfect
  secrecy and independence from the pre-whitening key `k₀`.
* `Cslib.Crypto.EvenMansour.advantage_preWhitenKeyRecoveryGame_eq`,
  `Cslib.Crypto.EvenMansour.advantage_postWhitenKeyRecoveryGame_eq`: 2-query attacks achieve
  key-recovery game advantage `1 - |G|⁻¹` when either whitening key is omitted.
* `Cslib.Crypto.EvenMansour.advantage_evenMansourRealGame_liftLeft_eq_zero`,
  `Cslib.Crypto.EvenMansour.advantage_evenMansourRealGame_liftRight_eq_zero`: zero advantage when
  queries are restricted to one oracle.
* `Cslib.Crypto.EvenMansour.toOuterMeasure_isBadEvenMansourKey_toReal_le`,
  `Cslib.Crypto.EvenMansour.toOuterMeasure_isBadSingleKeyEvenMansour_toReal_le`,
  `Cslib.Crypto.EvenMansour.IsCallBounded.badEvenMansourKey_toReal_le`,
  `Cslib.Crypto.EvenMansour.IsCallBounded.badSingleKeyEvenMansour_toReal_le`:
  Boneh–Shoup Theorem 4.10 bad-key probability bound `2 * Q_e * Q_π / |G|`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 4.7 (Theorem 4.10).
* [S. Even, Y. Mansour, *A Construction of a Cipher from a Single Pseudorandom
  Permutation*][EvenMansour1997].
* [O. Dunkelman, N. Keller, A. Shamir, *Minimalism in Cryptography: The Even–Mansour Scheme
  Revisited*][DunkelmanKellerShamir2012].
-/

@[expose] public section

namespace Cslib.Crypto.EvenMansour

open Probability OracleComp
open scoped ENNReal NNReal BigOperators

/-! ### Algebraic Even–Mansour cipher over an additive group -/

section Algebraic

variable {G : Type*} [AddGroup G]

/-- Even–Mansour encryption ([BonehShoup2023], Section 4.7; [EvenMansour1997]): pre-whiten by adding
`k₀`, apply the public permutation `π`, and post-whiten by adding `k₁`. -/
def evenMansourEncrypt (π : G → G) (k₀ k₁ x : G) : G :=
  π (x + k₀) + k₁

/-- Even–Mansour decryption: remove post-whitening key `k₁`, apply the inverse permutation `π_inv`,
and remove pre-whitening key `k₀`. -/
def evenMansourDecrypt (π_inv : G → G) (k₀ k₁ y : G) : G :=
  π_inv (y - k₁) - k₀

/-- Decryption inverts encryption whenever `π_inv` is a left inverse of `π`. -/
@[simp] theorem evenMansourDecrypt_evenMansourEncrypt {π π_inv : G → G}
    (h : Function.LeftInverse π_inv π) (k₀ k₁ x : G) :
    evenMansourDecrypt π_inv k₀ k₁ (evenMansourEncrypt π k₀ k₁ x) = x := by
  simp [evenMansourEncrypt, evenMansourDecrypt, h (x + k₀)]

/-- Encryption inverts decryption whenever `π_inv` is a right inverse of `π`. -/
@[simp] theorem evenMansourEncrypt_evenMansourDecrypt {π π_inv : G → G}
    (h : Function.RightInverse π_inv π) (k₀ k₁ y : G) :
    evenMansourEncrypt π k₀ k₁ (evenMansourDecrypt π_inv k₀ k₁ y) = y := by
  simp [evenMansourEncrypt, evenMansourDecrypt, h (y - k₁)]

/-- The Even–Mansour cipher bundled as a permutation `Equiv.Perm G`. -/
def evenMansourEquiv (π : Equiv.Perm G) (k₀ k₁ : G) : Equiv.Perm G where
  toFun := evenMansourEncrypt π k₀ k₁
  invFun := evenMansourDecrypt π.symm k₀ k₁
  left_inv := evenMansourDecrypt_evenMansourEncrypt π.left_inv k₀ k₁
  right_inv := evenMansourEncrypt_evenMansourDecrypt π.right_inv k₀ k₁

@[simp] theorem evenMansourEquiv_apply (π : Equiv.Perm G) (k₀ k₁ x : G) :
    evenMansourEquiv π k₀ k₁ x = π (x + k₀) + k₁ := rfl

@[simp] theorem evenMansourEquiv_symm_apply (π : Equiv.Perm G) (k₀ k₁ y : G) :
    (evenMansourEquiv π k₀ k₁).symm y = π.symm (y - k₁) - k₀ := rfl

/-- With zero whitening keys, the Even–Mansour cipher is the underlying permutation `π`. -/
@[simp] theorem evenMansourEquiv_zero (π : Equiv.Perm G) :
    evenMansourEquiv π 0 0 = π := by
  ext x
  simp

/-- Composing two Even–Mansour wrappers with the same permutation adds the whitening keys. -/
theorem evenMansourEquiv_evenMansourEquiv (π : Equiv.Perm G) (k₀ k₁ k₀' k₁' : G) :
    evenMansourEquiv (evenMansourEquiv π k₀ k₁) k₀' k₁' =
      evenMansourEquiv π (k₀' + k₀) (k₁ + k₁') := by
  ext x
  simp [add_assoc]

/-- The inverse of an Even–Mansour cipher with keys `(k₀, k₁)` and permutation `π` is an
Even–Mansour cipher with keys `(-k₁, -k₀)` and inverse permutation `π.symm`. -/
theorem evenMansourEquiv_symm (π : Equiv.Perm G) (k₀ k₁ : G) :
    (evenMansourEquiv π k₀ k₁).symm = evenMansourEquiv π.symm (-k₁) (-k₀) := by
  ext y
  simp [sub_eq_add_neg]

/-- Single-key Even–Mansour cipher (`k₀ = k₁ = k`, [DunkelmanKellerShamir2012]). -/
abbrev singleKeyEvenMansourEquiv (π : Equiv.Perm G) (k : G) : Equiv.Perm G :=
  evenMansourEquiv π k k

/-- Over a group of exponent two (`∀ x : G, -x = x`), Even–Mansour decryption is encryption under
the inverse permutation with the two keys swapped. -/
theorem evenMansourDecrypt_eq_of_neg_eq_self (hneg : ∀ x : G, -x = x) (π_inv : G → G)
    (k₀ k₁ y : G) :
    evenMansourDecrypt π_inv k₀ k₁ y = evenMansourEncrypt π_inv k₁ k₀ y := by
  simp [evenMansourDecrypt, evenMansourEncrypt, sub_eq_add_neg, hneg]

/-- Over a group of exponent two (`∀ x : G, -x = x`), inverting the Even–Mansour permutation swaps
the pre-whitening and post-whitening keys. -/
theorem evenMansourEquiv_symm_eq_of_neg_eq_self (hneg : ∀ x : G, -x = x) (π : Equiv.Perm G)
    (k₀ k₁ : G) :
    (evenMansourEquiv π k₀ k₁).symm = evenMansourEquiv π.symm k₁ k₀ := by
  rw [evenMansourEquiv_symm, hneg, hneg]

/-- Over `BitString n`, inverting the Even–Mansour permutation swaps `k₀` and `k₁`. -/
theorem evenMansourEquiv_symm_bitString {n : ℕ} (π : Equiv.Perm (BitString n))
    (k₀ k₁ : BitString n) :
    (evenMansourEquiv π k₀ k₁).symm = evenMansourEquiv π.symm k₁ k₀ :=
  evenMansourEquiv_symm_eq_of_neg_eq_self
    (fun x => neg_eq_iff_add_eq_zero.mpr (BitString.add_self x)) π k₀ k₁

/-- For any fixed keys `(k₀, k₁)`, wrapping a permutation `π` in Even–Mansour is a bijection on
`Equiv.Perm G`. -/
def evenMansourPermEquiv (k₀ k₁ : G) : Equiv.Perm (Equiv.Perm G) where
  toFun π := evenMansourEquiv π k₀ k₁
  invFun π := evenMansourEquiv π (-k₀) (-k₁)
  left_inv π := by
    dsimp
    rw [evenMansourEquiv_evenMansourEquiv, neg_add_cancel, add_neg_cancel, evenMansourEquiv_zero]
  right_inv π := by
    dsimp
    rw [evenMansourEquiv_evenMansourEquiv, add_neg_cancel, neg_add_cancel, evenMansourEquiv_zero]

@[simp] theorem evenMansourPermEquiv_apply (k₀ k₁ : G) (π : Equiv.Perm G) :
    evenMansourPermEquiv k₀ k₁ π = evenMansourEquiv π k₀ k₁ := rfl

/-! ### One-query perfect secrecy -/

/-- For any fixed function `π : G → G` and input `x : G`, the map `(k₀, k₁) ↦ (k₀, π(x + k₀) + k₁)`
is a bijection on `G × G`. -/
def oneQueryKeyEquiv (π : G → G) (x : G) : Equiv.Perm (G × G) where
  toFun k := (k.1, evenMansourEncrypt π k.1 k.2 x)
  invFun p := (p.1, -π (x + p.1) + p.2)
  left_inv k := by
    ext <;> simp [evenMansourEncrypt]
  right_inv p := by
    ext <;> simp [evenMansourEncrypt]

/-- **One-query perfect secrecy**: for any fixed `π : G → G` and plaintext `x : G`, under uniform
independent keys `(k₀, k₁)`, the pre-whitening key `k₀` and the ciphertext
`evenMansourEncrypt π k₀ k₁ x` are independent and uniformly distributed on `G × G`. -/
theorem map_prod_evenMansourEncrypt_uniformOfFintype [Fintype G] [Nonempty G]
    (π : G → G) (x : G) :
    (PMF.uniformOfFintype (G × G)).map (fun k => (k.1, evenMansourEncrypt π k.1 k.2 x)) =
      PMF.uniformOfFintype (G × G) :=
  PMF.uniformOfFintype_map_equiv (oneQueryKeyEquiv π x)

/-- Under uniform independent keys `(k₀, k₁)`, a single Even–Mansour encryption of `x` is uniformly
distributed on `G` for every fixed `π : G → G`. -/
theorem map_evenMansourEncrypt_uniformOfFintype [Fintype G] [Nonempty G]
    (π : G → G) (x : G) :
    (PMF.uniformOfFintype (G × G)).map (fun k => evenMansourEncrypt π k.1 k.2 x) =
      PMF.uniformOfFintype G := by
  have h := congrArg (PMF.map Prod.snd) (map_prod_evenMansourEncrypt_uniformOfFintype π x)
  rw [PMF.map_comp] at h
  calc (PMF.uniformOfFintype (G × G)).map (fun k => evenMansourEncrypt π k.1 k.2 x)
      = (PMF.uniformOfFintype (G × G)).map Prod.snd := h
    _ = (PMF.uniformOfFintype (G × G)).map (Prod.fst ∘ Equiv.prodComm G G) := rfl
    _ = ((PMF.uniformOfFintype (G × G)).map (Equiv.prodComm G G)).map Prod.fst := by
        rw [PMF.map_comp]
    _ = PMF.uniformOfFintype G := by
        rw [PMF.uniformOfFintype_map_equiv, PMF.uniformOfFintype_prod_map_fst]

/-! ### Necessity of both whitening keys (algebraic recovery) -/

/-- Even–Mansour with pre-whitening only (`k₁ = 0`): `E(k₀, x) = π(x + k₀)`
([BonehShoup2023], Section 4.7). -/
abbrev preWhitenEquiv (π : Equiv.Perm G) (k₀ : G) : Equiv.Perm G :=
  evenMansourEquiv π k₀ 0

/-- Even–Mansour with post-whitening only (`k₀ = 0`): `E(k₁, x) = π(x) + k₁`
([BonehShoup2023], Section 4.7). -/
abbrev postWhitenEquiv (π : Equiv.Perm G) (k₁ : G) : Equiv.Perm G :=
  evenMansourEquiv π 0 k₁

/-- Key recovery for `preWhitenEquiv`: given `y = E(k₀, x)` and `u = π⁻¹(y)`, recover
`k₀ = -x + u`. -/
def preWhitenKeyRecovery (pi_inv_enc_x x : G) : G :=
  -x + pi_inv_enc_x

/-- A single encryption query `y = preWhitenEquiv π k₀ x` and inverse permutation query `π.symm y`
recover `k₀` deterministically. -/
theorem preWhitenKeyRecovery_spec (π : Equiv.Perm G) (k₀ x : G) :
    preWhitenKeyRecovery (π.symm (preWhitenEquiv π k₀ x)) x = k₀ := by
  simp [preWhitenKeyRecovery, preWhitenEquiv]

/-- Key recovery for `postWhitenEquiv`: given `y = E(k₁, x)` and `v = π(x)`, recover
`k₁ = -v + y`. -/
def postWhitenKeyRecovery (enc_x pi_x : G) : G :=
  -pi_x + enc_x

/-- A single encryption query `y = postWhitenEquiv π k₁ x` and forward permutation query `π x`
recover `k₁` deterministically. -/
theorem postWhitenKeyRecovery_spec (π : Equiv.Perm G) (k₁ x : G) :
    postWhitenKeyRecovery (postWhitenEquiv π k₁ x) (π x) = k₁ := by
  simp [postWhitenKeyRecovery, postWhitenEquiv]

end Algebraic

/-! ### Bidirectional ideal-permutation oracle interface and games -/

/-- A bidirectional query to a permutation on `G`: either evaluate in the forward direction or
evaluate the inverse permutation. -/
inductive PermQuery (G : Type) where
  /-- Forward query `x ↦ P(x)`. -/
  | forward (x : G)
  /-- Inverse query `y ↦ P⁻¹(y)`. -/
  | inverse (y : G)
  deriving DecidableEq

/-- The oracle specification of a bidirectional permutation on `G`. -/
abbrev PermOracleSpec (G : Type) : OracleSpec (PermQuery G) :=
  fun _ => G

/-- Answer a bidirectional permutation query using `P : Equiv.Perm G`. -/
def evalPerm {G : Type} (P : Equiv.Perm G) : PermQuery G → G
  | .forward x => P x
  | .inverse y => P.symm y

@[simp] theorem evalPerm_forward {G : Type} (P : Equiv.Perm G) (x : G) :
    evalPerm P (.forward x) = P x := rfl

@[simp] theorem evalPerm_inverse {G : Type} (P : Equiv.Perm G) (y : G) :
    evalPerm P (.inverse y) = P.symm y := rfl

/-- The combined oracle interface in the Even–Mansour security experiment ([BonehShoup2023],
Section 4.7): left queries (`.inl`) call the cipher permutation `E` and right queries (`.inr`)
call the public primitive permutation `π`. -/
abbrev EvenMansourSpec (G : Type) : OracleSpec (PermQuery G ⊕ PermQuery G) :=
  PermOracleSpec G ⊕ₒ PermOracleSpec G

/-- Cost function counting cipher oracle calls (`1` for `.inl`, `0` for `.inr`). -/
def cipherCost {G : Type} : PermQuery G ⊕ PermQuery G → ℕ
  | .inl _ => 1
  | .inr _ => 0

/-- Cost function counting primitive permutation oracle calls (`0` for `.inl`, `1` for `.inr`). -/
def permCost {G : Type} : PermQuery G ⊕ PermQuery G → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- An adversary `program` makes at most `Q_e` cipher queries and at most `Q_π` primitive
permutation queries on every execution path. -/
def IsCallBounded {G α : Type} (program : OracleComp (EvenMansourSpec G) α) (Q_e Q_π : ℕ) :
    Prop :=
  IsCostBounded cipherCost program Q_e ∧ IsCostBounded permCost program Q_π

/-- A program making at most `Q_e` cipher queries and `Q_π` primitive queries makes at most
`Q_e + Q_π` total queries. -/
theorem IsCallBounded.isQueryBounded {G α : Type} {program : OracleComp (EvenMansourSpec G) α}
    {Q_e Q_π : ℕ} (h : IsCallBounded program Q_e Q_π) :
    IsQueryBounded program (Q_e + Q_π) :=
  (h.1.add h.2).of_le fun q => by cases q <;> simp [cipherCost, permCost]

/-- Query the cipher permutation in the forward direction (`x ↦ E(x)`). -/
def queryCipherForward {G : Type} (x : G) : OracleComp (EvenMansourSpec G) G :=
  liftLeft (query (spec := PermOracleSpec G) (.forward x))

/-- Query the cipher permutation in the inverse direction (`y ↦ E⁻¹(y)`). -/
def queryCipherInverse {G : Type} (y : G) : OracleComp (EvenMansourSpec G) G :=
  liftLeft (query (spec := PermOracleSpec G) (.inverse y))

/-- Query the public primitive permutation in the forward direction (`u ↦ π(u)`). -/
def queryPermForward {G : Type} (u : G) : OracleComp (EvenMansourSpec G) G :=
  liftRight (query (spec := PermOracleSpec G) (.forward u))

/-- Query the public primitive permutation in the inverse direction (`v ↦ π⁻¹(v)`). -/
def queryPermInverse {G : Type} (v : G) : OracleComp (EvenMansourSpec G) G :=
  liftRight (query (spec := PermOracleSpec G) (.inverse v))

theorem isCallBounded_queryCipherForward {G : Type} (x : G) :
    IsCallBounded (queryCipherForward x) 1 0 :=
  ⟨IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inl (.forward x)),
    IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inl (.forward x))⟩

theorem isCallBounded_queryCipherInverse {G : Type} (y : G) :
    IsCallBounded (queryCipherInverse y) 1 0 :=
  ⟨IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inl (.inverse y)),
    IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inl (.inverse y))⟩

theorem isCallBounded_queryPermForward {G : Type} (u : G) :
    IsCallBounded (queryPermForward u) 0 1 :=
  ⟨IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inr (.forward u)),
    IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inr (.forward u))⟩

theorem isCallBounded_queryPermInverse {G : Type} (v : G) :
    IsCallBounded (queryPermInverse v) 0 1 :=
  ⟨IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inr (.inverse v)),
    IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inr (.inverse v))⟩

/-- Deterministically evaluate a program against cipher permutation `E` and primitive permutation
`π`. -/
def evalTwoPerms {G α : Type} (E π : Equiv.Perm G)
    (program : OracleComp (EvenMansourSpec G) α) : α :=
  (interpret (sumHandler (fun q => (evalPerm E q : Id G)) (fun q => (evalPerm π q : Id G)))
    program).run

@[simp] theorem evalTwoPerms_pure {G α : Type} (E π : Equiv.Perm G) (a : α) :
    evalTwoPerms E π (pure a) = a := rfl

@[simp] theorem evalTwoPerms_map {G α β : Type} (E π : Equiv.Perm G)
    (f : α → β) (program : OracleComp (EvenMansourSpec G) α) :
    evalTwoPerms E π (f <$> program) = f (evalTwoPerms E π program) := by
  simp [evalTwoPerms]

@[simp] theorem evalTwoPerms_bind {G α β : Type} (E π : Equiv.Perm G)
    (program : OracleComp (EvenMansourSpec G) α)
    (next : α → OracleComp (EvenMansourSpec G) β) :
    evalTwoPerms E π (program >>= next) =
      evalTwoPerms E π (next (evalTwoPerms E π program)) := by
  simp [evalTwoPerms]

@[simp] theorem evalTwoPerms_queryCipherForward {G : Type} (E π : Equiv.Perm G) (x : G) :
    evalTwoPerms E π (queryCipherForward x) = E x := rfl

@[simp] theorem evalTwoPerms_queryCipherInverse {G : Type} (E π : Equiv.Perm G) (y : G) :
    evalTwoPerms E π (queryCipherInverse y) = E.symm y := rfl

@[simp] theorem evalTwoPerms_queryPermForward {G : Type} (E π : Equiv.Perm G) (u : G) :
    evalTwoPerms E π (queryPermForward u) = π u := rfl

@[simp] theorem evalTwoPerms_queryPermInverse {G : Type} (E π : Equiv.Perm G) (v : G) :
    evalTwoPerms E π (queryPermInverse v) = π.symm v := rfl

theorem evalTwoPerms_liftLeft {G α : Type} (E π π' : Equiv.Perm G)
    (program : OracleComp (PermOracleSpec G) α) :
    evalTwoPerms E π (liftLeft program) = evalTwoPerms E π' (liftLeft program) := by
  simp [evalTwoPerms]

theorem evalTwoPerms_liftRight {G α : Type} (E E' π : Equiv.Perm G)
    (program : OracleComp (PermOracleSpec G) α) :
    evalTwoPerms E π (liftRight program) = evalTwoPerms E' π (liftRight program) := by
  simp [evalTwoPerms]

/-- Deterministically evaluate a program in the real Even–Mansour world with public permutation `π`
and keys `(k₀, k₁)`. -/
def evalEvenMansour {G α : Type} [AddGroup G] (π : Equiv.Perm G) (k₀ k₁ : G)
    (program : OracleComp (EvenMansourSpec G) α) : α :=
  evalTwoPerms (evenMansourEquiv π k₀ k₁) π program

section Attacks

variable {G : Type} [AddGroup G]

/-- Oracle attack recovering `k₀` from `preWhitenEquiv π k₀` in `1` cipher query and `1` primitive
query: query `y ← E(x)` and `u ← π⁻¹(y)`, then return `-x + u`. -/
def preWhitenKeyRecoveryAttack (x : G) : OracleComp (EvenMansourSpec G) G := do
  let y ← queryCipherForward x
  let u ← queryPermInverse y
  return preWhitenKeyRecovery u x

/-- `preWhitenKeyRecoveryAttack x` makes at most `1` cipher query and `1` primitive query. -/
theorem isCallBounded_preWhitenKeyRecoveryAttack (x : G) :
    IsCallBounded (preWhitenKeyRecoveryAttack x) 1 1 := by
  constructor
  · simpa [preWhitenKeyRecoveryAttack] using
      (isCallBounded_queryCipherForward x).1.bind fun y =>
        (isCallBounded_queryPermInverse y).1.bind fun u => IsCostBounded.pure _ 0
  · simpa [preWhitenKeyRecoveryAttack] using
      (isCallBounded_queryCipherForward x).2.bind fun y =>
        (isCallBounded_queryPermInverse y).2.bind fun u => IsCostBounded.pure _ 0

/-- Against `preWhitenEquiv π k₀` and `π`, `preWhitenKeyRecoveryAttack x` deterministically returns
`k₀`. -/
@[simp] theorem evalTwoPerms_preWhitenKeyRecoveryAttack (π : Equiv.Perm G) (k₀ x : G) :
    evalTwoPerms (preWhitenEquiv π k₀) π (preWhitenKeyRecoveryAttack x) = k₀ := by
  simp [preWhitenKeyRecoveryAttack, preWhitenKeyRecovery]

/-- Oracle attack recovering `k₁` from `postWhitenEquiv π k₁` in `1` cipher query and `1` primitive
query: query `y ← E(x)` and `v ← π(x)`, then return `-v + y`. -/
def postWhitenKeyRecoveryAttack (x : G) : OracleComp (EvenMansourSpec G) G := do
  let y ← queryCipherForward x
  let v ← queryPermForward x
  return postWhitenKeyRecovery y v

/-- `postWhitenKeyRecoveryAttack x` makes at most `1` cipher query and `1` primitive query. -/
theorem isCallBounded_postWhitenKeyRecoveryAttack (x : G) :
    IsCallBounded (postWhitenKeyRecoveryAttack x) 1 1 := by
  constructor
  · simpa [postWhitenKeyRecoveryAttack] using
      (isCallBounded_queryCipherForward x).1.bind fun y =>
        (isCallBounded_queryPermForward x).1.bind fun v => IsCostBounded.pure _ 0
  · simpa [postWhitenKeyRecoveryAttack] using
      (isCallBounded_queryCipherForward x).2.bind fun y =>
        (isCallBounded_queryPermForward x).2.bind fun v => IsCostBounded.pure _ 0

/-- Against `postWhitenEquiv π k₁` and `π`, `postWhitenKeyRecoveryAttack x` deterministically
returns `k₁`. -/
@[simp] theorem evalTwoPerms_postWhitenKeyRecoveryAttack (π : Equiv.Perm G) (k₁ x : G) :
    evalTwoPerms (postWhitenEquiv π k₁) π (postWhitenKeyRecoveryAttack x) = k₁ := by
  simp [postWhitenKeyRecoveryAttack, postWhitenKeyRecovery]

end Attacks

section Games

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]

/-- The real Even–Mansour security experiment ([BonehShoup2023], Section 4.7): sample a uniform
permutation `π ← Equiv.Perm G` and uniform independent keys `(k₀, k₁) ← G × G`, and run `program`
against `evenMansourEquiv π k₀ k₁` and `π`. -/
noncomputable def evenMansourRealGame (program : OracleComp (EvenMansourSpec G) Bool) : Game := do
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  let k ← PMF.uniformOfFintype (G × G)
  return evalEvenMansour π k.1 k.2 program

/-- The single-key Even–Mansour security experiment ([DunkelmanKellerShamir2012]): sample a uniform
permutation `π ← Equiv.Perm G` and a single uniform key `k ← G`, and run `program` against
`singleKeyEvenMansourEquiv π k` and `π`. -/
noncomputable def singleKeyEvenMansourRealGame
    (program : OracleComp (EvenMansourSpec G) Bool) : Game := do
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  let k ← PMF.uniformOfFintype G
  return evalEvenMansour π k k program

/-- The ideal Even–Mansour security experiment: sample two independent uniform permutations
`E, π ← Equiv.Perm G` and run `program` against `E` and `π`. -/
noncomputable def evenMansourIdealGame (program : OracleComp (EvenMansourSpec G) Bool) : Game := do
  let E ← PMF.uniformOfFintype (Equiv.Perm G)
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  return evalTwoPerms E π program

/-- For any adversary `program` that queries only the cipher oracle (`liftLeft program`), the real
Even–Mansour game is identically distributed to the ideal game. -/
theorem evenMansourRealGame_liftLeft_eq_ideal (program : OracleComp (PermOracleSpec G) Bool) :
    evenMansourRealGame (liftLeft program) = evenMansourIdealGame (liftLeft program) := by
  have hkey (k₀ k₁ : G) :
      ((PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
        PMF.pure (evalTwoPerms (evenMansourEquiv π k₀ k₁) (1 : Equiv.Perm G) (liftLeft program))) =
      ((PMF.uniformOfFintype (Equiv.Perm G)).bind fun E =>
        PMF.pure (evalTwoPerms E (1 : Equiv.Perm G) (liftLeft program))) := by
    have h1 : ((PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
        PMF.pure (evalTwoPerms (evenMansourEquiv π k₀ k₁) (1 : Equiv.Perm G) (liftLeft program))) =
      ((PMF.uniformOfFintype (Equiv.Perm G)).map (evenMansourPermEquiv k₀ k₁)).bind (fun E =>
        PMF.pure (evalTwoPerms E (1 : Equiv.Perm G) (liftLeft program))) := by
      rw [PMF.bind_map]
      rfl
    rw [h1, PMF.uniformOfFintype_map_equiv]
  simp only [evenMansourRealGame, evenMansourIdealGame, evalEvenMansour,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [PMF.bind_comm]
  calc (PMF.uniformOfFintype (G × G)).bind (fun k =>
        (PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
          PMF.pure (evalTwoPerms (evenMansourEquiv π k.1 k.2) π (liftLeft program)))
      = (PMF.uniformOfFintype (G × G)).bind (fun k =>
        (PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
          PMF.pure (evalTwoPerms (evenMansourEquiv π k.1 k.2) (1 : Equiv.Perm G)
            (liftLeft program))) := by
        congr 1; funext k; congr 1; funext π
        rw [evalTwoPerms_liftLeft _ π 1 program]
    _ = (PMF.uniformOfFintype (G × G)).bind (fun _ =>
        (PMF.uniformOfFintype (Equiv.Perm G)).bind fun E =>
          PMF.pure (evalTwoPerms E (1 : Equiv.Perm G) (liftLeft program))) := by
        congr 1; funext k
        exact hkey k.1 k.2
    _ = (PMF.uniformOfFintype (Equiv.Perm G)).bind (fun E =>
          PMF.pure (evalTwoPerms E (1 : Equiv.Perm G) (liftLeft program))) := PMF.bind_const _ _
    _ = (PMF.uniformOfFintype (Equiv.Perm G)).bind (fun E =>
        (PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
          PMF.pure (evalTwoPerms E π (liftLeft program))) := by
        congr 1; funext E
        symm
        calc (PMF.uniformOfFintype (Equiv.Perm G)).bind (fun π =>
              PMF.pure (evalTwoPerms E π (liftLeft program)))
            = (PMF.uniformOfFintype (Equiv.Perm G)).bind (fun _ =>
              PMF.pure (evalTwoPerms E (1 : Equiv.Perm G) (liftLeft program))) := by
              congr 1; funext π
              rw [evalTwoPerms_liftLeft E π 1 program]
          _ = PMF.pure (evalTwoPerms E (1 : Equiv.Perm G) (liftLeft program)) :=
              PMF.bind_const _ _

/-- Any adversary that queries only the cipher oracle (`liftLeft`) has zero advantage between the
real Even–Mansour game and the ideal game. -/
@[simp] theorem advantage_evenMansourRealGame_liftLeft_eq_zero
    (program : OracleComp (PermOracleSpec G) Bool) :
    Game.advantage (evenMansourRealGame (liftLeft program))
      (evenMansourIdealGame (liftLeft program)) = 0 := by
  rw [evenMansourRealGame_liftLeft_eq_ideal, Game.advantage_self]

/-- For any adversary `program` that queries only the primitive permutation oracle
(`liftRight program`), the real Even–Mansour game is identically distributed to the ideal game. -/
theorem evenMansourRealGame_liftRight_eq_ideal (program : OracleComp (PermOracleSpec G) Bool) :
    evenMansourRealGame (liftRight program) = evenMansourIdealGame (liftRight program) := by
  simp only [evenMansourRealGame, evenMansourIdealGame, evalEvenMansour,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  calc (PMF.uniformOfFintype (Equiv.Perm G)).bind (fun π =>
        (PMF.uniformOfFintype (G × G)).bind fun k =>
          PMF.pure (evalTwoPerms (evenMansourEquiv π k.1 k.2) π (liftRight program)))
      = (PMF.uniformOfFintype (Equiv.Perm G)).bind (fun π =>
        (PMF.uniformOfFintype (G × G)).bind fun _ =>
          PMF.pure (evalTwoPerms (1 : Equiv.Perm G) π (liftRight program))) := by
        congr 1; funext π; congr 1; funext k
        rw [evalTwoPerms_liftRight _ 1 π program]
    _ = (PMF.uniformOfFintype (Equiv.Perm G)).bind (fun π =>
          PMF.pure (evalTwoPerms (1 : Equiv.Perm G) π (liftRight program))) := by
        simp [PMF.bind_const]
    _ = (PMF.uniformOfFintype (Equiv.Perm G)).bind (fun E =>
        (PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
          PMF.pure (evalTwoPerms E π (liftRight program))) := by
        symm
        calc (PMF.uniformOfFintype (Equiv.Perm G)).bind (fun E =>
              (PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
                PMF.pure (evalTwoPerms E π (liftRight program)))
            = (PMF.uniformOfFintype (Equiv.Perm G)).bind (fun _ =>
              (PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
                PMF.pure (evalTwoPerms (1 : Equiv.Perm G) π (liftRight program))) := by
              congr 1; funext E; congr 1; funext π
              rw [evalTwoPerms_liftRight E 1 π program]
          _ = _ := PMF.bind_const _ _

/-- Any adversary that queries only the primitive permutation oracle (`liftRight`) has zero
advantage between the real Even–Mansour game and the ideal game. -/
@[simp] theorem advantage_evenMansourRealGame_liftRight_eq_zero
    (program : OracleComp (PermOracleSpec G) Bool) :
    Game.advantage (evenMansourRealGame (liftRight program))
      (evenMansourIdealGame (liftRight program)) = 0 := by
  rw [evenMansourRealGame_liftRight_eq_ideal, Game.advantage_self]

/-! ### 2-query oracle attacks when either whitening key is omitted -/

/-- Key-recovery game for pre-whitening-only Even–Mansour: draw `π ← Equiv.Perm G` and
`k₀ ← G`, run `preWhitenKeyRecoveryAttack x` against `preWhitenEquiv π k₀` and `π`, and test
whether it outputs `k₀`. -/
noncomputable def preWhitenKeyRecoveryRealGame (x : G) : Game := do
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  let k₀ ← PMF.uniformOfFintype G
  return decide (evalTwoPerms (preWhitenEquiv π k₀) π (preWhitenKeyRecoveryAttack x) = k₀)

/-- Ideal comparison game for `preWhitenKeyRecoveryAttack`: draw independent uniform permutations
`E, π ← Equiv.Perm G` and a uniform target key `k₀ ← G`, and test whether
`preWhitenKeyRecoveryAttack x` outputs `k₀`. -/
noncomputable def preWhitenKeyRecoveryIdealGame (x : G) : Game := do
  let E ← PMF.uniformOfFintype (Equiv.Perm G)
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  let k₀ ← PMF.uniformOfFintype G
  return decide (evalTwoPerms E π (preWhitenKeyRecoveryAttack x) = k₀)

/-- In the real pre-whitened game, `preWhitenKeyRecoveryAttack x` succeeds with probability `1`. -/
@[simp] theorem preWhitenKeyRecoveryRealGame_eq_pure_true (x : G) :
    preWhitenKeyRecoveryRealGame x = PMF.pure true := by
  simp [preWhitenKeyRecoveryRealGame, PMF.bind_const]

/-- In the ideal game, `preWhitenKeyRecoveryAttack x` outputs the uniform target `k₀` with
probability `|G|⁻¹`. -/
theorem preWhitenKeyRecoveryIdealGame_true_toReal (x : G) :
    (preWhitenKeyRecoveryIdealGame x true).toReal = (Fintype.card G : ℝ)⁻¹ := by
  simp only [preWhitenKeyRecoveryIdealGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  have hconst (E π : Equiv.Perm G) :
      ((PMF.uniformOfFintype G).bind fun k₀ =>
        PMF.pure (decide (evalTwoPerms E π (preWhitenKeyRecoveryAttack x) = k₀))) true =
      (Fintype.card G : ℝ≥0∞)⁻¹ := by
    classical
    have hmap : ((PMF.uniformOfFintype G).bind fun k₀ =>
        PMF.pure (decide (evalTwoPerms E π (preWhitenKeyRecoveryAttack x) = k₀))) =
      (PMF.uniformOfFintype G).map (fun k₀ =>
        decide (evalTwoPerms E π (preWhitenKeyRecoveryAttack x) = k₀)) :=
      (PMF.bind_pure_comp _ _).symm
    rw [hmap, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      PMF.toOuterMeasure_uniformOfFintype]
    have hfilter : Finset.univ.filter (fun k₀ : G =>
        k₀ ∈ (fun k₀ => decide (evalTwoPerms E π (preWhitenKeyRecoveryAttack x) = k₀)) ⁻¹'
          ({true} : Set Bool)) = {evalTwoPerms E π (preWhitenKeyRecoveryAttack x)} := by
      ext k₀
      simp [eq_comm]
    rw [hfilter, Finset.card_singleton, Nat.cast_one, one_mul]
  rw [PMF.bind_apply_of_forall _ fun E => PMF.bind_apply_of_forall _ fun π => hconst E π,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- **2-query break of pre-whitening-only Even–Mansour** ([BonehShoup2023], Section 4.7):
omitting post-whitening (`k₁ = 0`) allows a 2-query attack (`1` cipher query + `1` primitive query)
to achieve key-recovery game advantage `1 - |G|⁻¹`. -/
theorem advantage_preWhitenKeyRecoveryGame_eq (x : G) :
    (Game.advantage (preWhitenKeyRecoveryRealGame x) (preWhitenKeyRecoveryIdealGame x) : ℝ) =
      1 - (Fintype.card G : ℝ)⁻¹ := by
  rw [Game.coe_advantage, Game.coe_succProbability, Game.coe_succProbability,
    preWhitenKeyRecoveryRealGame_eq_pure_true, preWhitenKeyRecoveryIdealGame_true_toReal]
  simp only [PMF.pure_apply, ↓reduceIte, ENNReal.toReal_one]
  have hle : (Fintype.card G : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos)
  exact abs_of_nonneg (by linarith)

/-- Key-recovery game for post-whitening-only Even–Mansour: draw `π ← Equiv.Perm G` and
`k₁ ← G`, run `postWhitenKeyRecoveryAttack x` against `postWhitenEquiv π k₁` and `π`, and test
whether it outputs `k₁`. -/
noncomputable def postWhitenKeyRecoveryRealGame (x : G) : Game := do
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  let k₁ ← PMF.uniformOfFintype G
  return decide (evalTwoPerms (postWhitenEquiv π k₁) π (postWhitenKeyRecoveryAttack x) = k₁)

/-- Ideal comparison game for `postWhitenKeyRecoveryAttack`: draw independent uniform permutations
`E, π ← Equiv.Perm G` and a uniform target key `k₁ ← G`, and test whether
`postWhitenKeyRecoveryAttack x` outputs `k₁`. -/
noncomputable def postWhitenKeyRecoveryIdealGame (x : G) : Game := do
  let E ← PMF.uniformOfFintype (Equiv.Perm G)
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  let k₁ ← PMF.uniformOfFintype G
  return decide (evalTwoPerms E π (postWhitenKeyRecoveryAttack x) = k₁)

/-- In the real post-whitened game, `postWhitenKeyRecoveryAttack x` succeeds with probability
`1`. -/
@[simp] theorem postWhitenKeyRecoveryRealGame_eq_pure_true (x : G) :
    postWhitenKeyRecoveryRealGame x = PMF.pure true := by
  simp [postWhitenKeyRecoveryRealGame, PMF.bind_const]

/-- In the ideal game, `postWhitenKeyRecoveryAttack x` outputs the uniform target `k₁` with
probability `|G|⁻¹`. -/
theorem postWhitenKeyRecoveryIdealGame_true_toReal (x : G) :
    (postWhitenKeyRecoveryIdealGame x true).toReal = (Fintype.card G : ℝ)⁻¹ := by
  simp only [postWhitenKeyRecoveryIdealGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  have hconst (E π : Equiv.Perm G) :
      ((PMF.uniformOfFintype G).bind fun k₁ =>
        PMF.pure (decide (evalTwoPerms E π (postWhitenKeyRecoveryAttack x) = k₁))) true =
      (Fintype.card G : ℝ≥0∞)⁻¹ := by
    classical
    have hmap : ((PMF.uniformOfFintype G).bind fun k₁ =>
        PMF.pure (decide (evalTwoPerms E π (postWhitenKeyRecoveryAttack x) = k₁))) =
      (PMF.uniformOfFintype G).map (fun k₁ =>
        decide (evalTwoPerms E π (postWhitenKeyRecoveryAttack x) = k₁)) :=
      (PMF.bind_pure_comp _ _).symm
    rw [hmap, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      PMF.toOuterMeasure_uniformOfFintype]
    have hfilter : Finset.univ.filter (fun k₁ : G =>
        k₁ ∈ (fun k₁ => decide (evalTwoPerms E π (postWhitenKeyRecoveryAttack x) = k₁)) ⁻¹'
          ({true} : Set Bool)) = {evalTwoPerms E π (postWhitenKeyRecoveryAttack x)} := by
      ext k₁
      simp [eq_comm]
    rw [hfilter, Finset.card_singleton, Nat.cast_one, one_mul]
  rw [PMF.bind_apply_of_forall _ fun E => PMF.bind_apply_of_forall _ fun π => hconst E π,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- **2-query break of post-whitening-only Even–Mansour** ([BonehShoup2023], Section 4.7):
omitting pre-whitening (`k₀ = 0`) allows a 2-query attack (`1` cipher query + `1` primitive query)
to achieve key-recovery game advantage `1 - |G|⁻¹`. -/
theorem advantage_postWhitenKeyRecoveryGame_eq (x : G) :
    (Game.advantage (postWhitenKeyRecoveryRealGame x) (postWhitenKeyRecoveryIdealGame x) : ℝ) =
      1 - (Fintype.card G : ℝ)⁻¹ := by
  rw [Game.coe_advantage, Game.coe_succProbability, Game.coe_succProbability,
    postWhitenKeyRecoveryRealGame_eq_pure_true, postWhitenKeyRecoveryIdealGame_true_toReal]
  simp only [PMF.pure_apply, ↓reduceIte, ENNReal.toReal_one]
  have hle : (Fintype.card G : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos)
  exact abs_of_nonneg (by linarith)

end Games

/-! ### Bad-key transcript intersection analysis (Boneh–Shoup Theorem 4.10) -/

section BadKeys

variable {G : Type} [AddGroup G] [DecidableEq G]

/-- A key pair `k = (k₀, k₁)` is bad for a cipher input-output pair `e = (x, y)` and a primitive
permutation input-output pair `p = (u, v)` if the internal permutation input `x + k₀` collides with
`u` or the internal permutation output `y - k₁` collides with `v`
([BonehShoup2023], Section 4.7, Theorem 4.10). -/
def isBadKeyPair (e p : G × G) (k : G × G) : Bool :=
  decide (e.1 + k.1 = p.1) || decide (e.2 - k.2 = p.2)

/-- A key pair `k = (k₀, k₁)` is bad for a cipher transcript `T_e : List (G × G)` and a primitive
permutation transcript `T_π : List (G × G)` if some `e ∈ T_e` and `p ∈ T_π` collide on the
internal permutation input or output ([BonehShoup2023], Section 4.7, Theorem 4.10). -/
def isBadEvenMansourKey (T_e T_π : List (G × G)) (k : G × G) : Bool :=
  T_e.any fun e => T_π.any fun p => isBadKeyPair e p k

/-- Single-key specialization (`k₀ = k₁ = k`, [DunkelmanKellerShamir2012]) of the Even–Mansour
bad-key predicate. -/
def isBadSingleKeyEvenMansour (T_e T_π : List (G × G)) (k : G) : Bool :=
  isBadEvenMansourKey T_e T_π (k, k)

/-- Input-only bad-key predicate (`x + k₀ = u` for some `(x, y) ∈ T_e` and `(u, v) ∈ T_π`), which
captures all collisions in the real Even–Mansour world where `y = π(x + k₀) + k₁` and
`v = π(u)`. -/
def isBadInputKey (T_e T_π : List (G × G)) (k₀ : G) : Bool :=
  T_e.any fun e => T_π.any fun p => decide (e.1 + k₀ = p.1)

@[simp] theorem isBadKeyPair_eq_true_iff (e p k : G × G) :
    isBadKeyPair e p k = true ↔ e.1 + k.1 = p.1 ∨ e.2 - k.2 = p.2 := by
  simp [isBadKeyPair]

@[simp] theorem isBadEvenMansourKey_eq_true_iff (T_e T_π : List (G × G)) (k : G × G) :
    isBadEvenMansourKey T_e T_π k = true ↔
      ∃ e ∈ T_e, ∃ p ∈ T_π, e.1 + k.1 = p.1 ∨ e.2 - k.2 = p.2 := by
  simp [isBadEvenMansourKey]

/-- **Domain and range disjointness outside bad keys**: when
`isBadEvenMansourKey T_e T_π k = false`, every cipher pair `(x, y) ∈ T_e` has internal permutation
input `x + k₀` distinct from every primitive query input `u` in `T_π`, and internal permutation
output `y - k₁` distinct from every primitive query output `v` in `T_π`. -/
theorem disjoint_of_isBadEvenMansourKey_eq_false {T_e T_π : List (G × G)} {k : G × G}
    (hgood : isBadEvenMansourKey T_e T_π k = false) {e p : G × G}
    (he : e ∈ T_e) (hp : p ∈ T_π) :
    e.1 + k.1 ≠ p.1 ∧ e.2 - k.2 ≠ p.2 := by
  have hnot : ¬isBadEvenMansourKey T_e T_π k = true := by simp [hgood]
  rw [isBadEvenMansourKey_eq_true_iff] at hnot
  push Not at hnot
  exact hnot e he p hp

omit [DecidableEq G] in
/-- When `e = (x, y)` is consistent with `evenMansourEquiv π k₀ k₁` (`π (x + k₀) + k₁ = y`) and
`p = (u, v)` is consistent with `π` (`π u = v`), an output collision `y - k₁ = v` is equivalent to
an input collision `x + k₀ = u`. -/
theorem input_collision_iff_output_collision (π : Equiv.Perm G) (k : G × G) {e p : G × G}
    (he : evenMansourEquiv π k.1 k.2 e.1 = e.2) (hp : π p.1 = p.2) :
    e.1 + k.1 = p.1 ↔ e.2 - k.2 = p.2 := by
  have he' : e.2 - k.2 = π (e.1 + k.1) := by
    rw [← he, evenMansourEquiv_apply, add_sub_cancel_right]
  rw [he', ← hp, π.injective.eq_iff]

/-- On a pair `(e, p)` consistent with `evenMansourEquiv π k.1 k.2` and `π`, `isBadKeyPair e p k`
reduces to the input collision `decide (e.1 + k.1 = p.1)`. -/
theorem isBadKeyPair_eq_decide_of_evenMansourEquiv (π : Equiv.Perm G) (k : G × G) {e p : G × G}
    (he : evenMansourEquiv π k.1 k.2 e.1 = e.2) (hp : π p.1 = p.2) :
    isBadKeyPair e p k = decide (e.1 + k.1 = p.1) := by
  rw [Bool.eq_iff_iff, isBadKeyPair_eq_true_iff, decide_eq_true_eq,
    ← input_collision_iff_output_collision π k he hp, or_self]

/-- On transcripts `T_e` and `T_π` consistent with `evenMansourEquiv π k.1 k.2` and `π`,
`isBadEvenMansourKey T_e T_π k` equals `isBadInputKey T_e T_π k.1`. -/
theorem isBadEvenMansourKey_eq_isBadInputKey_of_evenMansourEquiv (π : Equiv.Perm G) (k : G × G)
    {T_e T_π : List (G × G)} (hT_e : ∀ e ∈ T_e, evenMansourEquiv π k.1 k.2 e.1 = e.2)
    (hT_π : ∀ p ∈ T_π, π p.1 = p.2) :
    isBadEvenMansourKey T_e T_π k = isBadInputKey T_e T_π k.1 := by
  rw [Bool.eq_iff_iff]
  simp only [isBadEvenMansourKey, isBadInputKey, List.any_eq_true]
  refine exists_congr fun e => and_congr_right fun he => ?_
  refine exists_congr fun p => and_congr_right fun hp => ?_
  rw [isBadKeyPair_eq_decide_of_evenMansourEquiv π k (hT_e e he) (hT_π p hp)]

/-! ### Exact single-pair collision probabilities and multi-query union bounds -/

variable [Fintype G] [Nonempty G]

/-- Under a uniform key `k₀ ← G`, the probability of an input collision `x + k₀ = u` is exactly
`|G|⁻¹`. -/
private theorem toOuterMeasure_input_collision (x u : G) :
    (PMF.uniformOfFintype G).toOuterMeasure {k₀ : G | decide (x + k₀ = u) = true} =
      (Fintype.card G : ℝ≥0∞)⁻¹ := by
  rw [PMF.toOuterMeasure_uniformOfFintype]
  have hfilter : Finset.univ.filter (· ∈ {k₀ : G | decide (x + k₀ = u) = true}) = {-x + u} := by
    ext k₀
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      decide_eq_true_eq, Finset.mem_singleton]
    exact ⟨fun h => by rw [← h, neg_add_cancel_left], fun h => by rw [h, add_neg_cancel_left]⟩
  rw [hfilter, Finset.card_singleton, Nat.cast_one, one_mul]

/-- Under a uniform key `k₁ ← G`, the probability of an output collision `y - k₁ = v` is exactly
`|G|⁻¹`. -/
private theorem toOuterMeasure_output_collision (y v : G) :
    (PMF.uniformOfFintype G).toOuterMeasure {k₁ : G | decide (y - k₁ = v) = true} =
      (Fintype.card G : ℝ≥0∞)⁻¹ := by
  rw [PMF.toOuterMeasure_uniformOfFintype]
  have hfilter : Finset.univ.filter (· ∈ {k₁ : G | decide (y - k₁ = v) = true}) = {-v + y} := by
    ext k₁
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      decide_eq_true_eq, Finset.mem_singleton]
    rw [← neg_inj, neg_sub, sub_eq_iff_eq_add]
  rw [hfilter, Finset.card_singleton, Nat.cast_one, one_mul]

/-- Under uniform independent keys `(k₀, k₁) ← G × G`, the probability of an input collision
`e.1 + k.1 = p.1` is `|G|⁻¹`. -/
private theorem toOuterMeasure_prod_input_collision (e p : G × G) :
    (PMF.uniformOfFintype (G × G)).toOuterMeasure {k : G × G | decide (e.1 + k.1 = p.1) = true} =
      (Fintype.card G : ℝ≥0∞)⁻¹ := by
  have hpre : {k : G × G | decide (e.1 + k.1 = p.1) = true} =
      Prod.fst ⁻¹' {k₀ : G | decide (e.1 + k₀ = p.1) = true} := rfl
  rw [hpre, ← PMF.toOuterMeasure_map_apply, PMF.uniformOfFintype_prod_map_fst,
    toOuterMeasure_input_collision]

/-- Under uniform independent keys `(k₀, k₁) ← G × G`, the probability of an output collision
`e.2 - k.2 = p.2` is `|G|⁻¹`. -/
private theorem toOuterMeasure_prod_output_collision (e p : G × G) :
    (PMF.uniformOfFintype (G × G)).toOuterMeasure {k : G × G | decide (e.2 - k.2 = p.2) = true} =
      (Fintype.card G : ℝ≥0∞)⁻¹ := by
  have hsnd : (PMF.uniformOfFintype (G × G)).map Prod.snd = PMF.uniformOfFintype G := by
    calc (PMF.uniformOfFintype (G × G)).map Prod.snd
        = ((PMF.uniformOfFintype (G × G)).map (Equiv.prodComm G G)).map Prod.fst := by
          rw [PMF.map_comp]; rfl
      _ = PMF.uniformOfFintype G := by
          rw [PMF.uniformOfFintype_map_equiv, PMF.uniformOfFintype_prod_map_fst]
  have hpre : {k : G × G | decide (e.2 - k.2 = p.2) = true} =
      Prod.snd ⁻¹' {k₁ : G | decide (e.2 - k₁ = p.2) = true} := rfl
  rw [hpre, ← PMF.toOuterMeasure_map_apply, hsnd, toOuterMeasure_output_collision]

/-- For a single pair `(e, p)`, a uniform key pair `k ← G × G` satisfies `isBadKeyPair e p k` with
probability at most `2 * |G|⁻¹`. -/
theorem toOuterMeasure_isBadKeyPair_le (e p : G × G) :
    (PMF.uniformOfFintype (G × G)).toOuterMeasure {k | isBadKeyPair e p k = true} ≤
      2 * (Fintype.card G : ℝ≥0∞)⁻¹ := by
  have hset : {k | isBadKeyPair e p k = true} =
      {k : G × G | decide (e.1 + k.1 = p.1) = true} ∪
        {k : G × G | decide (e.2 - k.2 = p.2) = true} := by
    ext k
    simp [isBadKeyPair]
  rw [hset]
  exact (MeasureTheory.measure_union_le _ _).trans_eq (by
    rw [toOuterMeasure_prod_input_collision, toOuterMeasure_prod_output_collision, two_mul])

/-- For a single pair `(e, p)`, a single uniform key `k ← G` satisfies `isBadKeyPair e p (k, k)`
with probability at most `2 * |G|⁻¹`. -/
theorem toOuterMeasure_isBadKeyPair_singleKey_le (e p : G × G) :
    (PMF.uniformOfFintype G).toOuterMeasure {k | isBadKeyPair e p (k, k) = true} ≤
      2 * (Fintype.card G : ℝ≥0∞)⁻¹ := by
  have hset : {k | isBadKeyPair e p (k, k) = true} =
      {k : G | decide (e.1 + k = p.1) = true} ∪
        {k : G | decide (e.2 - k = p.2) = true} := by
    ext k
    simp [isBadKeyPair]
  rw [hset]
  exact (MeasureTheory.measure_union_le _ _).trans_eq (by
    rw [toOuterMeasure_input_collision, toOuterMeasure_output_collision, two_mul])

/-- **Boneh–Shoup Theorem 4.10 bad-key union bound (`ℝ≥0∞`)**: for any cipher transcript `T_e` and
primitive permutation transcript `T_π`, a uniform key pair `(k₀, k₁) ← G × G` is bad with
probability at most `2 * |T_e| * |T_π| * |G|⁻¹`. -/
theorem toOuterMeasure_isBadEvenMansourKey_le (T_e T_π : List (G × G)) :
    (PMF.uniformOfFintype (G × G)).toOuterMeasure {k | isBadEvenMansourKey T_e T_π k = true} ≤
      2 * T_e.length * T_π.length * (Fintype.card G : ℝ≥0∞)⁻¹ := by
  have hset : {k | isBadEvenMansourKey T_e T_π k = true} =
      ⋃ x ∈ T_e.toFinset ×ˢ T_π.toFinset, {k | isBadKeyPair x.1 x.2 k = true} := by
    ext k
    simp only [Set.mem_ofPred_eq, isBadEvenMansourKey_eq_true_iff, Set.mem_iUnion,
      Finset.mem_product, List.mem_toFinset, isBadKeyPair_eq_true_iff, Prod.exists, exists_prop]
    exact ⟨fun ⟨a, b, hab, c, d, hcd, h⟩ => ⟨a, b, c, d, ⟨hab, hcd⟩, h⟩,
      fun ⟨a, b, c, d, ⟨hab, hcd⟩, h⟩ => ⟨a, b, hab, c, d, hcd, h⟩⟩
  rw [hset]
  calc (PMF.uniformOfFintype (G × G)).toOuterMeasure
        (⋃ x ∈ T_e.toFinset ×ˢ T_π.toFinset, {k | isBadKeyPair x.1 x.2 k = true})
      ≤ ∑ x ∈ T_e.toFinset ×ˢ T_π.toFinset,
          (PMF.uniformOfFintype (G × G)).toOuterMeasure {k | isBadKeyPair x.1 x.2 k = true} :=
        MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ (T_e.toFinset ×ˢ T_π.toFinset).card • (2 * (Fintype.card G : ℝ≥0∞)⁻¹) :=
        Finset.sum_le_card_nsmul _ _ _ fun x _ => toOuterMeasure_isBadKeyPair_le x.1 x.2
    _ = (T_e.toFinset.card : ℝ≥0∞) * T_π.toFinset.card * (2 * (Fintype.card G : ℝ≥0∞)⁻¹) := by
        rw [Finset.card_product, nsmul_eq_mul, Nat.cast_mul]
    _ ≤ (T_e.length : ℝ≥0∞) * T_π.length * (2 * (Fintype.card G : ℝ≥0∞)⁻¹) :=
        mul_le_mul' (mul_le_mul' (Nat.cast_le.mpr (List.toFinset_card_le T_e))
          (Nat.cast_le.mpr (List.toFinset_card_le T_π))) le_rfl
    _ = 2 * T_e.length * T_π.length * (Fintype.card G : ℝ≥0∞)⁻¹ := by ring

/-- **Boneh–Shoup Theorem 4.10 bad-key union bound (`ℝ`)**: for any cipher transcript `T_e` and
primitive permutation transcript `T_π`, a uniform key pair `(k₀, k₁) ← G × G` is bad with real
probability at most `2 * |T_e| * |T_π| / |G|`. -/
theorem toOuterMeasure_isBadEvenMansourKey_toReal_le (T_e T_π : List (G × G)) :
    ((PMF.uniformOfFintype (G × G)).toOuterMeasure
      {k | isBadEvenMansourKey T_e T_π k = true}).toReal ≤
      2 * (T_e.length : ℝ) * (T_π.length : ℝ) / (Fintype.card G : ℝ) := by
  have h := toOuterMeasure_isBadEvenMansourKey_le T_e T_π
  have hne : (2 : ℝ≥0∞) * T_e.length * T_π.length * (Fintype.card G : ℝ≥0∞)⁻¹ ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.natCast_ne_top _)) (ENNReal.natCast_ne_top _)) ?_
    simp [Fintype.card_ne_zero]
  have hreal := ENNReal.toReal_mono hne h
  simpa [ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv] using hreal

/-- **Single-key Even–Mansour bad-key union bound (`ℝ≥0∞`, [DunkelmanKellerShamir2012])**: for any
cipher transcript `T_e` and primitive permutation transcript `T_π`, a single uniform key `k ← G` is
bad with probability at most `2 * |T_e| * |T_π| * |G|⁻¹`. -/
theorem toOuterMeasure_isBadSingleKeyEvenMansour_le (T_e T_π : List (G × G)) :
    (PMF.uniformOfFintype G).toOuterMeasure {k | isBadSingleKeyEvenMansour T_e T_π k = true} ≤
      2 * T_e.length * T_π.length * (Fintype.card G : ℝ≥0∞)⁻¹ := by
  have hset : {k | isBadSingleKeyEvenMansour T_e T_π k = true} =
      ⋃ x ∈ T_e.toFinset ×ˢ T_π.toFinset, {k | isBadKeyPair x.1 x.2 (k, k) = true} := by
    ext k
    simp only [Set.mem_ofPred_eq, isBadSingleKeyEvenMansour, isBadEvenMansourKey_eq_true_iff,
      Set.mem_iUnion, Finset.mem_product, List.mem_toFinset, isBadKeyPair_eq_true_iff, Prod.exists,
      exists_prop]
    exact ⟨fun ⟨a, b, hab, c, d, hcd, h⟩ => ⟨a, b, c, d, ⟨hab, hcd⟩, h⟩,
      fun ⟨a, b, c, d, ⟨hab, hcd⟩, h⟩ => ⟨a, b, hab, c, d, hcd, h⟩⟩
  rw [hset]
  calc (PMF.uniformOfFintype G).toOuterMeasure
        (⋃ x ∈ T_e.toFinset ×ˢ T_π.toFinset, {k | isBadKeyPair x.1 x.2 (k, k) = true})
      ≤ ∑ x ∈ T_e.toFinset ×ˢ T_π.toFinset,
          (PMF.uniformOfFintype G).toOuterMeasure {k | isBadKeyPair x.1 x.2 (k, k) = true} :=
        MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ (T_e.toFinset ×ˢ T_π.toFinset).card • (2 * (Fintype.card G : ℝ≥0∞)⁻¹) :=
        Finset.sum_le_card_nsmul _ _ _ fun x _ => toOuterMeasure_isBadKeyPair_singleKey_le x.1 x.2
    _ = (T_e.toFinset.card : ℝ≥0∞) * T_π.toFinset.card * (2 * (Fintype.card G : ℝ≥0∞)⁻¹) := by
        rw [Finset.card_product, nsmul_eq_mul, Nat.cast_mul]
    _ ≤ (T_e.length : ℝ≥0∞) * T_π.length * (2 * (Fintype.card G : ℝ≥0∞)⁻¹) :=
        mul_le_mul' (mul_le_mul' (Nat.cast_le.mpr (List.toFinset_card_le T_e))
          (Nat.cast_le.mpr (List.toFinset_card_le T_π))) le_rfl
    _ = 2 * T_e.length * T_π.length * (Fintype.card G : ℝ≥0∞)⁻¹ := by ring

/-- **Single-key Even–Mansour bad-key union bound (`ℝ`, [DunkelmanKellerShamir2012])**: for any
cipher transcript `T_e` and primitive permutation transcript `T_π`, a single uniform key `k ← G` is
bad with real probability at most `2 * |T_e| * |T_π| / |G|`. -/
theorem toOuterMeasure_isBadSingleKeyEvenMansour_toReal_le (T_e T_π : List (G × G)) :
    ((PMF.uniformOfFintype G).toOuterMeasure
      {k | isBadSingleKeyEvenMansour T_e T_π k = true}).toReal ≤
      2 * (T_e.length : ℝ) * (T_π.length : ℝ) / (Fintype.card G : ℝ) := by
  have h := toOuterMeasure_isBadSingleKeyEvenMansour_le T_e T_π
  have hne : (2 : ℝ≥0∞) * T_e.length * T_π.length * (Fintype.card G : ℝ≥0∞)⁻¹ ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.natCast_ne_top _)) (ENNReal.natCast_ne_top _)) ?_
    simp [Fintype.card_ne_zero]
  have hreal := ENNReal.toReal_mono hne h
  simpa [ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv] using hreal

/-- **Input-collision union bound (`ℝ`)**: for any cipher transcript `T_e` and primitive transcript
`T_π`, a uniform pre-whitening key `k₀ ← G` triggers an input collision `isBadInputKey T_e T_π k₀`
with real probability at most `|T_e| * |T_π| / |G|`. -/
theorem toOuterMeasure_isBadInputKey_toReal_le (T_e T_π : List (G × G)) :
    ((PMF.uniformOfFintype G).toOuterMeasure {k₀ | isBadInputKey T_e T_π k₀ = true}).toReal ≤
      (T_e.length : ℝ) * (T_π.length : ℝ) / (Fintype.card G : ℝ) := by
  have hset : {k₀ | isBadInputKey T_e T_π k₀ = true} =
      ⋃ x ∈ T_e.toFinset ×ˢ T_π.toFinset, {k₀ | decide (x.1.1 + k₀ = x.2.1) = true} := by
    ext k₀
    simp only [Set.mem_ofPred_eq, isBadInputKey, List.any_eq_true, Set.mem_iUnion,
      Finset.mem_product, List.mem_toFinset, Prod.exists, exists_prop]
    exact ⟨fun ⟨a, b, hab, c, d, hcd, h⟩ => ⟨a, b, c, d, ⟨hab, hcd⟩, h⟩,
      fun ⟨a, b, c, d, ⟨hab, hcd⟩, h⟩ => ⟨a, b, hab, c, d, hcd, h⟩⟩
  have h : (PMF.uniformOfFintype G).toOuterMeasure {k₀ | isBadInputKey T_e T_π k₀ = true} ≤
      T_e.length * (T_π.length * (Fintype.card G : ℝ≥0∞)⁻¹) := by
    rw [hset]
    calc (PMF.uniformOfFintype G).toOuterMeasure
          (⋃ x ∈ T_e.toFinset ×ˢ T_π.toFinset, {k₀ | decide (x.1.1 + k₀ = x.2.1) = true})
        ≤ ∑ x ∈ T_e.toFinset ×ˢ T_π.toFinset,
            (PMF.uniformOfFintype G).toOuterMeasure {k₀ | decide (x.1.1 + k₀ = x.2.1) = true} :=
          MeasureTheory.measure_biUnion_finset_le _ _
      _ ≤ (T_e.toFinset ×ˢ T_π.toFinset).card • (Fintype.card G : ℝ≥0∞)⁻¹ :=
          Finset.sum_le_card_nsmul _ _ _ fun x _ => (toOuterMeasure_input_collision x.1.1 x.2.1).le
      _ = (T_e.toFinset.card : ℝ≥0∞) * (T_π.toFinset.card * (Fintype.card G : ℝ≥0∞)⁻¹) := by
          rw [Finset.card_product, nsmul_eq_mul, Nat.cast_mul, mul_assoc]
      _ ≤ (T_e.length : ℝ≥0∞) * (T_π.length * (Fintype.card G : ℝ≥0∞)⁻¹) :=
          mul_le_mul' (Nat.cast_le.mpr (List.toFinset_card_le T_e))
            (mul_le_mul' (Nat.cast_le.mpr (List.toFinset_card_le T_π)) le_rfl)
  have hne : (T_e.length : ℝ≥0∞) * (T_π.length * (Fintype.card G : ℝ≥0∞)⁻¹) ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top _) ?_)
    simp [Fintype.card_ne_zero]
  have hreal := ENNReal.toReal_mono hne h
  simpa [ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv, mul_assoc] using hreal

end BadKeys

/-! ### Adaptive distinguisher transcript bounds via `IsCallBounded` -/

section TranscriptBounds

/-- Project a logged `EvenMansourSpec G` query-response entry onto its cipher input-output pair
`(x, y)` (turning `.inverse y` with answer `x` into `(x, y)`), or `none` for primitive queries. -/
def transcriptCipherEntry {G : Type}
    (entry : (q : PermQuery G ⊕ PermQuery G) × EvenMansourSpec G q) : Option (G × G) :=
  match entry.1, entry.2 with
  | .inl (.forward x), y => some (x, y)
  | .inl (.inverse y), x => some (x, y)
  | .inr _, _ => none

/-- Project a logged `EvenMansourSpec G` query-response entry onto its primitive permutation
input-output pair `(u, v)` (turning `.inverse v` with answer `u` into `(u, v)`), or `none` for
cipher queries. -/
def transcriptPermEntry {G : Type}
    (entry : (q : PermQuery G ⊕ PermQuery G) × EvenMansourSpec G q) : Option (G × G) :=
  match entry.1, entry.2 with
  | .inl _, _ => none
  | .inr (.forward u), v => some (u, v)
  | .inr (.inverse v), u => some (u, v)

/-- The list of cipher input-output pairs recorded in a bidirectional interaction transcript. -/
def transcriptCipher {G : Type} (T : Transcript (EvenMansourSpec G)) : List (G × G) :=
  T.filterMap transcriptCipherEntry

/-- The list of primitive permutation input-output pairs recorded in a bidirectional interaction
transcript. -/
def transcriptPerm {G : Type} (T : Transcript (EvenMansourSpec G)) : List (G × G) :=
  T.filterMap transcriptPermEntry

/-- The length of `transcriptCipher T` equals the total `cipherCost` of `T`. -/
@[simp] theorem length_transcriptCipher_eq_sum_cipherCost {G : Type}
    (T : Transcript (EvenMansourSpec G)) :
    (transcriptCipher T).length = (T.map fun entry => cipherCost entry.1).sum := by
  induction T with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨(x | y) | (u | v), ans⟩ <;>
      simpa [transcriptCipher, transcriptCipherEntry, List.filterMap_cons, cipherCost,
        Nat.add_comm] using ih

/-- The length of `transcriptPerm T` equals the total `permCost` of `T`. -/
@[simp] theorem length_transcriptPerm_eq_sum_permCost {G : Type}
    (T : Transcript (EvenMansourSpec G)) :
    (transcriptPerm T).length = (T.map fun entry => permCost entry.1).sum := by
  induction T with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨(x | y) | (u | v), ans⟩ <;>
      simpa [transcriptPerm, transcriptPermEntry, List.filterMap_cons, permCost,
        Nat.add_comm] using ih

/-- Against any stateful bidirectional oracle, a supported run of `program` with
`IsCallBounded program Q_e Q_π` records at most `Q_e` cipher pairs. -/
theorem IsCallBounded.length_transcriptCipher_le {G State γ : Type}
    {program : OracleComp (EvenMansourSpec G) γ} {Q_e Q_π : ℕ}
    (h : IsCallBounded program Q_e Q_π)
    (oracle : (q : PermQuery G ⊕ PermQuery G) → StateT State PMF (EvenMansourSpec G q))
    {s s' : State} {result : γ} {T : Transcript (EvenMansourSpec G)}
    (hmem : (result, s', T) ∈
      ((OracleComp.interpret (withTranscript oracle) program).run (s, [])).support) :
    (transcriptCipher T).length ≤ Q_e := by
  rw [length_transcriptCipher_eq_sum_cipherCost]
  exact h.1.transcript_cost_le oracle hmem

/-- Against any stateful bidirectional oracle, a supported run of `program` with
`IsCallBounded program Q_e Q_π` records at most `Q_π` primitive permutation pairs. -/
theorem IsCallBounded.length_transcriptPerm_le {G State γ : Type}
    {program : OracleComp (EvenMansourSpec G) γ} {Q_e Q_π : ℕ}
    (h : IsCallBounded program Q_e Q_π)
    (oracle : (q : PermQuery G ⊕ PermQuery G) → StateT State PMF (EvenMansourSpec G q))
    {s s' : State} {result : γ} {T : Transcript (EvenMansourSpec G)}
    (hmem : (result, s', T) ∈
      ((OracleComp.interpret (withTranscript oracle) program).run (s, [])).support) :
    (transcriptPerm T).length ≤ Q_π := by
  rw [length_transcriptPerm_eq_sum_permCost]
  exact h.2.transcript_cost_le oracle hmem

variable {G : Type} [AddGroup G] [DecidableEq G] [Fintype G] [Nonempty G]

/-- **Boneh–Shoup Theorem 4.10 for adaptive call-bounded distinguishers (two-key)**: on any
supported transcript `T` of a distinguisher satisfying `IsCallBounded program Q_e Q_π`, a uniform
key pair `(k₀, k₁) ← G × G` is bad with real probability at most `2 * Q_e * Q_π / |G|`. -/
theorem IsCallBounded.badEvenMansourKey_toReal_le {State γ : Type}
    {program : OracleComp (EvenMansourSpec G) γ} {Q_e Q_π : ℕ}
    (h : IsCallBounded program Q_e Q_π)
    (oracle : (q : PermQuery G ⊕ PermQuery G) → StateT State PMF (EvenMansourSpec G q))
    {s s' : State} {result : γ} {T : Transcript (EvenMansourSpec G)}
    (hmem : (result, s', T) ∈
      ((OracleComp.interpret (withTranscript oracle) program).run (s, [])).support) :
    ((PMF.uniformOfFintype (G × G)).toOuterMeasure
      {k | isBadEvenMansourKey (transcriptCipher T) (transcriptPerm T) k = true}).toReal ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (Fintype.card G : ℝ) := by
  have hlen_e : ((transcriptCipher T).length : ℝ) ≤ Q_e :=
    Nat.cast_le.mpr (h.length_transcriptCipher_le oracle hmem)
  have hlen_π : ((transcriptPerm T).length : ℝ) ≤ Q_π :=
    Nat.cast_le.mpr (h.length_transcriptPerm_le oracle hmem)
  refine (toOuterMeasure_isBadEvenMansourKey_toReal_le (transcriptCipher T)
    (transcriptPerm T)).trans ?_
  gcongr

/-- **Boneh–Shoup Theorem 4.10 for adaptive call-bounded distinguishers (single-key)**: on any
supported transcript `T` of a distinguisher satisfying `IsCallBounded program Q_e Q_π`, a single
uniform key `k ← G` is bad with real probability at most `2 * Q_e * Q_π / |G|`. -/
theorem IsCallBounded.badSingleKeyEvenMansour_toReal_le {State γ : Type}
    {program : OracleComp (EvenMansourSpec G) γ} {Q_e Q_π : ℕ}
    (h : IsCallBounded program Q_e Q_π)
    (oracle : (q : PermQuery G ⊕ PermQuery G) → StateT State PMF (EvenMansourSpec G q))
    {s s' : State} {result : γ} {T : Transcript (EvenMansourSpec G)}
    (hmem : (result, s', T) ∈
      ((OracleComp.interpret (withTranscript oracle) program).run (s, [])).support) :
    ((PMF.uniformOfFintype G).toOuterMeasure
      {k | isBadSingleKeyEvenMansour (transcriptCipher T) (transcriptPerm T) k = true}).toReal ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (Fintype.card G : ℝ) := by
  have hlen_e : ((transcriptCipher T).length : ℝ) ≤ Q_e :=
    Nat.cast_le.mpr (h.length_transcriptCipher_le oracle hmem)
  have hlen_π : ((transcriptPerm T).length : ℝ) ≤ Q_π :=
    Nat.cast_le.mpr (h.length_transcriptPerm_le oracle hmem)
  refine (toOuterMeasure_isBadSingleKeyEvenMansour_toReal_le (transcriptCipher T)
    (transcriptPerm T)).trans ?_
  gcongr

end TranscriptBounds

end Cslib.Crypto.EvenMansour
