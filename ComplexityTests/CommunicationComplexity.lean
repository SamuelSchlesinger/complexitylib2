/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Communication.Functions
import Complexity.Computability.Communication.Rank

/-!
Regression clients for deterministic communication complexity: leaf rectangles, fooling sets, the
rank bound, and the `n + 1` lower bounds for equality, greater-than, inner product and
disjointness.
-/

open Cslib Cslib.Communication

namespace CommunicationComplexityTests

/-! ### Leaf rectangles -/

/-- Alice sends her bit; on `true`, Bob sends his. -/
private def small : Protocol Bool Bool (Fin 3) :=
  .alice id (.output 0) (.bob id (.output 1) (.output 2))

example : small.leaves = 3 := rfl
example : small.depth = 2 := rfl
example : (small.leaf false true).val = 0 := rfl
example : (small.leaf true false).val = 1 := rfl
example : (small.leaf true true).val = 2 := rfl

/-- The last leaf. -/
private def last : Fin small.leaves := ⟨2, by decide⟩

example : small.leafOutput last = 2 := rfl

-- The rectangle of the last leaf is `{true} × {true}`.
example : true ∈ small.leafAlice last ∧ true ∈ small.leafBob last :=
  Protocol.leaf_eq_iff.mp (rfl : small.leaf true true = last)

example : false ∉ small.leafBob last := fun h =>
  absurd (Protocol.leaf_eq_iff.mpr ⟨(Protocol.leaf_eq_iff.mp
    (rfl : small.leaf true true = last)).1, h⟩) (by decide)

-- The partition into at most `2 ^ 2` rectangles.
example : ∃ (n : ℕ) (A : Fin n → Set Bool) (B : Fin n → Set Bool) (z : Fin n → Fin 3),
    n ≤ 4 ∧ (∀ x y, ∃! i, x ∈ A i ∧ y ∈ B i) ∧ ∀ i, ∀ x ∈ A i, ∀ y ∈ B i, small.run x y = z i :=
  small.exists_rectangle_partition

/-! ### The trivial protocol and the boundary `n = 0` -/

-- Without any bits, equality is constant and needs no communication: `0 < n` is needed.
example : Protocol.ecomplexity (fun (x y : BitString 0) b => equality x y = b) Set.univ
    Set.univ = 0 := by
  refine le_antisymm ?_ bot_le
  have := Protocol.ecomplexity_le_depth (p := (.output true : Protocol (BitString 0) _ _))
    (R := fun (x y : BitString 0) b => equality x y = b) (A := Set.univ) (B := Set.univ)
    (fun x _ y _ => by simp [equality, Subsingleton.elim x y])
  simpa using this

example (f : BitString 3 → Bool → Bool) : Protocol.ecomplexityFun f ≤ 4 :=
  Protocol.ecomplexityFun_le_succ f

/-! ### Fooling sets -/

example : IsFoolingSet (equality : Fin 3 → Fin 3 → Bool) true
    (Finset.univ.image fun x => (x, x)) :=
  isFoolingSet_equality _

-- A pair off the diagonal cannot be added: `{(0, 0), (0, 1)}` is not a fooling set for equality.
example : ¬ IsFoolingSet (equality : Fin 2 → Fin 2 → Bool) true {(0, 0), (0, 1)} := by
  intro h
  have := h.1 (0, 1) (by simp)
  simp [equality] at this

example (n : ℕ) : IsFoolingSet disjointness true
    ((Finset.univ : Finset (BitString n)).image fun x => (x, fun i => !x i)) :=
  isFoolingSet_disjointness _

/-! ### The rank bound -/

-- The communication matrix of equality is the identity, so the rank bound gives `n` bits.
example (n : ℕ) : (n : ℕ∞) ≤
    Protocol.ecomplexity (fun (x y : BitString n) b => equality x y = b) Set.univ Set.univ := by
  have h := clog_rank_le_ecomplexity ℝ (equality : BitString n → BitString n → Bool)
  have hM : communicationMatrix ℝ (equality : BitString n → BitString n → Bool) = 1 := by
    ext x y
    simp [equality, Matrix.one_apply]
  rwa [hM, Matrix.rank_one, BitString.card, Nat.clog_pow _ _ one_lt_two] at h

example : Prop := LogRankConjecture

/-! ### Named functions -/

example : Protocol.ecomplexity (fun (x y : BitString 3) b => equality x y = b) Set.univ
    Set.univ = 4 :=
  ecomplexity_equality (by decide)

example : Protocol.ecomplexity (fun (x y : BitString 3) b =>
    greaterThan (BitString.equivFin 3 x) (BitString.equivFin 3 y) = b) Set.univ Set.univ = 4 :=
  ecomplexity_greaterThan (by decide)

example : Protocol.ecomplexity (fun (x y : BitString 3) b => x ⬝ᵥ y = b) Set.univ
    Set.univ = 4 :=
  ecomplexity_dotProduct (by decide)

example : Protocol.ecomplexity (fun (x y : BitString 3) b => disjointness x y = b) Set.univ
    Set.univ = 4 :=
  ecomplexity_disjointness (by decide)

-- Equality on a five-element set needs three bits.
example (p : Protocol (Fin 5) (Fin 5) Bool) (hp : p.run = equality) : 3 ≤ p.depth := by
  have h := card_lt_two_pow_of_run_eq_equality (by decide) hp
  rw [Fintype.card_fin] at h
  by_contra hd
  have : 2 ^ p.depth ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-! ### Axiom guards -/

/-- info: 'Cslib.Communication.Protocol.exists_rectangle_partition' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Protocol.exists_rectangle_partition

/-- info: 'Cslib.Communication.Protocol.card_filter_le_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Protocol.card_filter_le_mul

/-- info: 'Cslib.Communication.IsFoolingSet.card_lt_two_pow' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsFoolingSet.card_lt_two_pow

/-- info: 'Cslib.Communication.IsFoolingSet.succ_le_ecomplexity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsFoolingSet.succ_le_ecomplexity

/-- info: 'Cslib.Communication.Protocol.rank_communicationMatrix_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Protocol.rank_communicationMatrix_le

/-- info: 'Cslib.Communication.clog_rank_le_ecomplexity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clog_rank_le_ecomplexity

/-- info: 'Cslib.Communication.ecomplexity_equality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ecomplexity_equality

/-- info: 'Cslib.Communication.ecomplexity_greaterThan' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ecomplexity_greaterThan

/-- info: 'Cslib.Communication.ecomplexity_dotProduct' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ecomplexity_dotProduct

/-- info: 'Cslib.Communication.ecomplexity_disjointness' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ecomplexity_disjointness

end CommunicationComplexityTests
