/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Communication.Discrepancy
import Complexity.Computability.Communication.Functions
import Complexity.Computability.Communication.Newman
import Complexity.Probability.PMF

/-!
Regression clients for randomized communication complexity: public- and private-coin protocols,
the averaging argument, Newman's theorem, the weighted area bound, the discrepancy bound, and the
`Ω(n)` lower bound for the inner product.
-/

open Cslib Cslib.Communication Finset

namespace CommunicationComplexity2Tests

/-! ### Protocols on transformed inputs and the function form -/

example : (Protocol.comap (fun n : ℕ => decide (n = 0)) id
    (.alice id (.output 0) (.output 1) : Protocol Bool Bool ℕ)).run 0 true = 1 := rfl

example : Protocol.ecomplexityFun (fun (x : Bool) (_ : Unit) => x) ≤ 1 :=
  Protocol.ecomplexityFun_le_iff.mpr ⟨.alice id (.output false) (.output true),
    funext₂ fun x _ => by cases x <;> rfl, le_rfl⟩

/-! ### A public-coin protocol for equality with two bits -/

/-- With shared random bits `r`, Alice sends `x ⬝ᵥ r` and Bob announces whether `y ⬝ᵥ r` agrees. -/
private def eqProtocol {n : ℕ} (r : BitString n) : Protocol (BitString n) (BitString n) Bool :=
  .alice (fun x => x ⬝ᵥ r) (.bob (fun y => y ⬝ᵥ r) (.output true) (.output false))
    (.bob (fun y => y ⬝ᵥ r) (.output false) (.output true))

private theorem run_eqProtocol {n : ℕ} (r x y : BitString n) :
    (eqProtocol r).run x y = decide (x ⬝ᵥ r = y ⬝ᵥ r) := by
  simp only [eqProtocol, Protocol.run_alice, Protocol.run_bob, Protocol.run_output]
  cases x ⬝ᵥ r <;> cases y ⬝ᵥ r <;> rfl

/-- The random-parity protocol for equality. -/
private noncomputable def eqPublicCoin (n : ℕ) : PublicCoin (BitString n) (BitString n) Bool :=
  (Probability.PMF.uniformOfFintype (BitString n)).map eqProtocol

private theorem depth_eqPublicCoin (n : ℕ) : PublicCoin.depth (eqPublicCoin n) ≤ 2 := by
  refine PublicCoin.depth_le_iff.mpr fun p hp => ?_
  obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  simp [eqProtocol]

/-- Two distinct bit strings have the same parity on exactly half of all subsets. -/
private theorem card_agree_mul_two {n : ℕ} {x y : BitString n} (hxy : x ≠ y) :
    #{r : BitString n | x ⬝ᵥ r = y ⬝ᵥ r} * 2 = 2 ^ n := by
  have hv : x + y ≠ 0 := fun h => hxy (by
    have := congrArg (· + y) h
    simpa [add_assoc] using this)
  have hcount := two_mul_card_dotProduct_eq_true_add (x + y)
  simp only [hv, ↓reduceIte, add_zero, Fintype.card_fin] at hcount
  have hagree : #{r : BitString n | x ⬝ᵥ r = y ⬝ᵥ r} =
      #{r : BitString n | ¬(x + y) ⬝ᵥ r = true} := by
    congr 1
    ext r
    simp only [mem_filter, mem_univ, true_and, add_dotProduct]
    cases x ⬝ᵥ r <;> cases y ⬝ᵥ r <;> decide
  have := card_filter_add_card_filter_not (s := univ) fun r : BitString n => (x + y) ⬝ᵥ r = true
  rw [card_univ, BitString.card] at this
  set a := #{r : BitString n | (x + y) ⬝ᵥ r = true}
  set b := #{r : BitString n | ¬(x + y) ⬝ᵥ r = true}
  omega

/-- The random-parity protocol errs only on unequal inputs, with probability one half. -/
private theorem solves_eqPublicCoin (n : ℕ) :
    PublicCoin.Solves (eqPublicCoin n) (1 / 2) (fun x y b => equality x y = b) Set.univ
      Set.univ := by
  classical
  intro x _ y _
  rw [PublicCoin.errorProb, eqPublicCoin, PMF.toOuterMeasure_map_apply,
    Probability.PMF.toOuterMeasure_apply_toReal, ← sum_filter]
  simp only [Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    BitString.card, Set.mem_preimage, Set.mem_ofPred_eq, run_eqProtocol, equality]
  rw [sum_const, nsmul_eq_mul]
  by_cases hxy : x = y
  · simp [hxy]
  · have hset : #{r : BitString n | ¬decide (x = y) = decide (x ⬝ᵥ r = y ⬝ᵥ r)} =
        #{r : BitString n | x ⬝ᵥ r = y ⬝ᵥ r} := by
      congr 1
      ext r
      simp [hxy]
    rw [hset, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    have : (#{r : BitString n | x ⬝ᵥ r = y ⬝ᵥ r} : ℝ) * 2 = 2 ^ n := by
      exact_mod_cast card_agree_mul_two hxy
    push_cast
    linarith

-- Equality has public-coin complexity at most two with error one half. A coin flip with no
-- communication also has error one half, so this only checks the protocol.
example (n : ℕ) : PublicCoin.ecomplexityFun (1 / 2) (equality : BitString n → BitString n → Bool)
    ≤ 2 :=
  (PublicCoin.ecomplexity_le_depth (solves_eqPublicCoin n)).trans (depth_eqPublicCoin n)

/-! ### Equality with error one quarter -/

/-- Bob announces whether his parities agree with the parities `a` and `b` that Alice sent. -/
private def eqCheck {n : ℕ} (r : BitString n × BitString n) (a b : Bool) :
    Protocol (BitString n) (BitString n) Bool :=
  .bob (fun y => decide (y ⬝ᵥ r.1 = a ∧ y ⬝ᵥ r.2 = b)) (.output false) (.output true)

/-- With shared random bits `r`, Alice sends `x ⬝ᵥ r.1` and `x ⬝ᵥ r.2`, and Bob announces whether
`y ⬝ᵥ r.1` and `y ⬝ᵥ r.2` agree with them. -/
private def eqProtocol₂ {n : ℕ} (r : BitString n × BitString n) :
    Protocol (BitString n) (BitString n) Bool :=
  .alice (fun x => x ⬝ᵥ r.1)
    (.alice (fun x => x ⬝ᵥ r.2) (eqCheck r false false) (eqCheck r false true))
    (.alice (fun x => x ⬝ᵥ r.2) (eqCheck r true false) (eqCheck r true true))

private theorem run_eqProtocol₂ {n : ℕ} (r : BitString n × BitString n) (x y : BitString n) :
    (eqProtocol₂ r).run x y = decide (x ⬝ᵥ r.1 = y ⬝ᵥ r.1 ∧ x ⬝ᵥ r.2 = y ⬝ᵥ r.2) := by
  simp only [eqProtocol₂, eqCheck, Protocol.run_alice, Protocol.run_bob, Protocol.run_output]
  cases x ⬝ᵥ r.1 <;> cases x ⬝ᵥ r.2 <;> cases y ⬝ᵥ r.1 <;> cases y ⬝ᵥ r.2 <;> rfl

/-- Two independent random parities for equality. -/
private noncomputable def eqPublicCoin₂ (n : ℕ) : PublicCoin (BitString n) (BitString n) Bool :=
  (Probability.PMF.uniformOfFintype (BitString n × BitString n)).map eqProtocol₂

private theorem depth_eqPublicCoin₂ (n : ℕ) : PublicCoin.depth (eqPublicCoin₂ n) ≤ 3 := by
  refine PublicCoin.depth_le_iff.mpr fun p hp => ?_
  obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  simp [eqProtocol₂, eqCheck]

/-- Two independent random parities err only on unequal inputs, with probability one quarter. -/
private theorem solves_eqPublicCoin₂ (n : ℕ) :
    PublicCoin.Solves (eqPublicCoin₂ n) (1 / 4) (fun x y b => equality x y = b) Set.univ
      Set.univ := by
  classical
  intro x _ y _
  rw [PublicCoin.errorProb, eqPublicCoin₂, PMF.toOuterMeasure_map_apply,
    Probability.PMF.toOuterMeasure_apply_toReal, ← sum_filter]
  simp only [Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Fintype.card_prod, BitString.card, Set.mem_preimage, Set.mem_ofPred_eq, run_eqProtocol₂,
    equality]
  rw [sum_const, nsmul_eq_mul]
  by_cases hxy : x = y
  · simp [hxy]
  · have hset : #{r : BitString n × BitString n |
          ¬decide (x = y) = decide (x ⬝ᵥ r.1 = y ⬝ᵥ r.1 ∧ x ⬝ᵥ r.2 = y ⬝ᵥ r.2)} =
        #(({r : BitString n | x ⬝ᵥ r = y ⬝ᵥ r} : Finset _) ×ˢ
          ({r : BitString n | x ⬝ᵥ r = y ⬝ᵥ r} : Finset _)) := by
      congr 1
      ext r
      simp [hxy]
    rw [hset, card_product, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    have : (#{r : BitString n | x ⬝ᵥ r = y ⬝ᵥ r} : ℝ) * 2 = 2 ^ n := by
      exact_mod_cast card_agree_mul_two hxy
    push_cast
    nlinarith

-- Equality has public-coin complexity at most three with error one quarter, against `n + 1`
-- deterministically.
example (n : ℕ) : PublicCoin.ecomplexityFun (1 / 4) (equality : BitString n → BitString n → Bool)
    ≤ 3 :=
  (PublicCoin.ecomplexity_le_depth (solves_eqPublicCoin₂ n)).trans (depth_eqPublicCoin₂ n)

example : Protocol.ecomplexityFun (equality : BitString 3 → BitString 3 → Bool) = 4 :=
  ecomplexity_equality (by decide)

-- The averaging argument picks, for inputs drawn from any distribution, one protocol that errs
-- with probability at most one half.
example (n : ℕ) (ν : PMF (BitString n × BitString n)) :
    ∃ p ∈ (eqPublicCoin n).support,
      p.distributionalError ν (fun x y b => equality x y = b) ≤ 1 / 2 :=
  (solves_eqPublicCoin n).exists_distributionalError_le ν fun _ _ => ⟨trivial, trivial⟩

/-! ### Deterministic and private-coin protocols -/

example {X Y Z : Type*} {R : X → Y → Z → Prop} {A : Set X} {B : Set Y} :
    PublicCoin.ecomplexity (1 / 3) R A B ≤ PrivateCoin.ecomplexity (1 / 3) R A B ∧
      PrivateCoin.ecomplexity (1 / 3) R A B ≤ Protocol.ecomplexity R A B :=
  ⟨PublicCoin.ecomplexity_le_privateCoin, PrivateCoin.ecomplexity_le_protocol (by norm_num)⟩

-- A deterministic protocol, run while ignoring the random bits, errs with probability zero.
example (x : BitString 2) (y : BitString 2) :
    PrivateCoin.errorProb ((eqProtocol 1).comap Prod.fst Prod.fst : PrivateCoin 3 1 _ _ _)
      (fun x y b => (eqProtocol 1).run x y = b) x y = 0 := by
  simp [PrivateCoin.errorProb]

/-! ### Newman's theorem -/

example {Z : Type*} (n : ℕ) {R : BitString n → BitString n → Z → Prop} {ε δ : ℝ} (hδ : 0 < δ) :
    PrivateCoin.ecomplexity (ε + δ) R Set.univ Set.univ ≤
      PublicCoin.ecomplexity ε R Set.univ Set.univ + Nat.clog 2 ⌈n / δ ^ 2⌉₊ :=
  PrivateCoin.ecomplexity_le_add_clog (n := n) (by simp) (by simp) hδ

-- Equality with private coins and error `3 / 8` needs at most `3 + ⌈log₂ 64 n⌉` bits.
example (n : ℕ) :
    PrivateCoin.ecomplexityFun (1 / 4 + 1 / 8) (equality : BitString n → BitString n → Bool) ≤
      3 + Nat.clog 2 ⌈n / (1 / 8 : ℝ) ^ 2⌉₊ :=
  (PrivateCoin.ecomplexity_le_add_clog (n := n) (by simp) (by simp) (by norm_num)).trans
    (by
      gcongr
      exact (PublicCoin.ecomplexity_le_depth (solves_eqPublicCoin₂ n)).trans
        (depth_eqPublicCoin₂ n))

/-! ### The weighted area bound -/

-- Unit weights give back the area bound.
example {X Y : Type*} [Fintype X] [Fintype Y] (p : Protocol X Y Bool) :
    (#{q : X × Y | p.run q.1 q.2 = true} : ℝ) ≤
      #{i | p.leafOutput i = true} * (Fintype.card X * Fintype.card Y) := by
  have h := Protocol.sum_filter_le_mul (p := p) rfl true (fun _ _ => (1 : ℝ))
    (K := Fintype.card X * Fintype.card Y) fun A B _ => by
      simp only [sum_const, nsmul_eq_mul, mul_one]
      exact mul_le_mul (by exact_mod_cast card_le_univ A) (by exact_mod_cast card_le_univ B)
        (by positivity) (by positivity)
  simpa using h

/-! ### Discrepancy and the inner product -/

example {X Y : Type*} [Fintype X] [Fintype Y] (ν : PMF (X × Y)) (f : X → Y → Bool) :
    0 ≤ discrepancy ν f :=
  discrepancy_nonneg

-- The squared discrepancy bound for the inner product on three bits.
example : discrepancy (Probability.PMF.uniformOfFintype (BitString 3 × BitString 3))
    (fun x y => x ⬝ᵥ y) ^ 2 * 2 ^ 3 ≤ 1 :=
  discrepancy_dotProduct_sq_mul_two_pow_le 3

-- With error `1 / 3`, the inner product of ten bits needs at least four bits, with public or
-- private coins.
example : 4 ≤ PublicCoin.ecomplexityFun (1 / 3) (fun x y : BitString 10 => x ⬝ᵥ y) := by
  have h := PublicCoin.le_two_mul_ecomplexityFun_dotProduct_add_three 10
  cases hc : PublicCoin.ecomplexityFun (1 / 3) (fun x y : BitString 10 => x ⬝ᵥ y)
    using ENat.recTopCoe with
  | top => simp
  | coe c =>
    rw [hc] at h
    have : 10 ≤ 2 * c + 3 := by exact_mod_cast h
    exact_mod_cast (by omega : 4 ≤ c)

example (n : ℕ) :
    (n : ℕ∞) ≤ 2 * PrivateCoin.ecomplexityFun (1 / 3) (fun x y : BitString n => x ⬝ᵥ y) + 3 :=
  PrivateCoin.le_two_mul_ecomplexityFun_dotProduct_add_three n

-- The general error trade-off: error `1 / 2 - γ` with `c` bits forces `(2 γ)² 2 ^ n ≤ 4 ^ c`.
example (n c : ℕ) {γ : ℝ} (hγ : 0 ≤ γ)
    (h : PublicCoin.ecomplexityFun (1 / 2 - γ) (fun x y : BitString n => x ⬝ᵥ y) ≤ c) :
    (2 * γ) ^ 2 * 2 ^ n ≤ 4 ^ c := by
  obtain ⟨μ, hμ, hc⟩ := PublicCoin.ecomplexity_le_iff.mp h
  exact hμ.sq_mul_two_pow_le_four_pow_of_dotProduct hc hγ

/-! ### Axiom guards -/

/--
info: 'Cslib.Communication.PublicCoin.Solves.exists_distributionalError_le' depends on axioms:
[propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PublicCoin.Solves.exists_distributionalError_le

/-- info: 'Cslib.Communication.PublicCoin.ecomplexity_le_privateCoin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PublicCoin.ecomplexity_le_privateCoin

/-- info: 'Cslib.Communication.PublicCoin.Solves.exists_privateCoin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PublicCoin.Solves.exists_privateCoin

/-- info: 'Cslib.Communication.PrivateCoin.ecomplexity_le_add' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PrivateCoin.ecomplexity_le_add

/-- info: 'Cslib.Communication.PrivateCoin.ecomplexity_le_add_clog' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PrivateCoin.ecomplexity_le_add_clog

/-- info: 'Cslib.Communication.Protocol.sum_filter_le_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Protocol.sum_filter_le_mul

/--
info: 'Cslib.Communication.Protocol.two_mul_le_two_pow_mul_discrepancy' depends on axioms:
[propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Protocol.two_mul_le_two_pow_mul_discrepancy

/--
info: 'Cslib.Communication.PublicCoin.two_mul_le_two_pow_mul_discrepancy' depends on axioms:
[propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PublicCoin.two_mul_le_two_pow_mul_discrepancy

/--
info: 'Cslib.Communication.discrepancy_dotProduct_sq_mul_two_pow_le' depends on axioms:
[propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms discrepancy_dotProduct_sq_mul_two_pow_le

/--
info: 'Cslib.Communication.PublicCoin.le_two_mul_ecomplexityFun_dotProduct_add_three' depends on
axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PublicCoin.le_two_mul_ecomplexityFun_dotProduct_add_three

/--
info: 'Cslib.Communication.PrivateCoin.le_two_mul_ecomplexityFun_dotProduct_add_three' depends
on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PrivateCoin.le_two_mul_ecomplexityFun_dotProduct_add_three

end CommunicationComplexity2Tests
