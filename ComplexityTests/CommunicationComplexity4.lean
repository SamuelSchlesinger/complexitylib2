/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Communication.Equality
import Complexity.Computability.Communication.Inclusion
import Complexity.Computability.Communication.InnerProductRank

/-!
Regression clients for exchanging the players and relabelling outputs, the trivial upper bounds,
equality on finite sets, intersection and inclusion, the rank bounds for relabelled outputs and
sign matrices, and the rank of the inner-product matrix.
-/

open Cslib Cslib.Communication Finset

namespace CommunicationComplexity4Tests

/-! ### Exchanging the players and relabelling outputs -/

/-- Alice sends her bit; on `true`, Bob sends his. -/
private def small : Protocol Bool Bool (Fin 3) :=
  .alice id (.output 0) (.bob id (.output 1) (.output 2))

example : small.swapPlayers = .bob id (.output 0) (.alice id (.output 1) (.output 2)) := rfl
example : small.swapPlayers.run true false = small.run false true := rfl
example : (small.map Fin.val).run true true = 2 := rfl
example : (small.map Fin.val).leaves = 3 := rfl

/-! ### Trivial upper bounds -/

example (f : BitString 3 → BitString 5 → Bool) : Protocol.ecomplexityFun f ≤ 4 :=
  (Protocol.ecomplexityFun_le_min_succ f).trans_eq rfl

-- A function of an input from a five-element set: three bits suffice for the encoding.
example (f : Fin 5 → ℕ → Bool) : Protocol.ecomplexityFun f ≤ 4 := by
  have h := Protocol.ecomplexityFun_le_clog_card_succ f
  rw [Fintype.card_fin, show Nat.clog 2 5 = 3 by decide] at h
  exact_mod_cast h

/-! ### Equality on finite sets -/

-- Equality on a five-element set costs exactly four bits: the fooling-set bound only gives three.
example : Protocol.ecomplexityFun (equality : Fin 5 → Fin 5 → Bool) = 4 := by
  rw [ecomplexityFun_equality (by decide), Fintype.card_fin, show Nat.clog 2 5 = 3 by decide]
  rfl

-- On bit strings, `⌈log₂ 2 ^ n⌉ + 1 = n + 1` recovers the bound for `n`-bit strings.
example {n : ℕ} (hn : 0 < n) :
    Protocol.ecomplexityFun (fun x y : BitString n => !equality x y) = n + 1 := by
  rw [ecomplexityFun_not_equality (by rw [BitString.card]; exact Nat.one_lt_two_pow hn.ne'),
    BitString.card, Nat.clog_pow _ _ one_lt_two]

example (p : Protocol (Fin 3) (Fin 3) Bool) (hp : p.run = equality) : 5 ≤ p.leaves := by
  simpa using card_add_two_le_leaves_of_run_eq_equality (by decide) hp

/-! ### Intersection and inclusion -/

example : Protocol.ecomplexityFun (fun x y : BitString 4 => !disjointness x y) = 5 :=
  ecomplexityFun_not_disjointness (by decide)

example : Protocol.ecomplexityFun (fun x y : BitString 4 => decide (x ≤ y)) = 5 :=
  ecomplexityFun_decide_le (by decide)

/-! ### Rank bounds -/

example (A B : Matrix (Fin 2) (Fin 3) ℚ) : (A - B).rank ≤ A.rank + B.rank :=
  Matrix.rank_sub_le A B

example {X Y : Type} [Fintype Y] (p : Protocol X Y Bool) :
    (signMatrix ℝ p.run).rank ≤ 2 ^ p.depth :=
  Protocol.rank_signMatrix_le_two_pow rfl

-- The inner product of two bits: its `4 × 4` matrix has rank `3` over `ℚ`.
example : (communicationMatrix ℚ fun x y : Fin 2 → Bool => x ⬝ᵥ y).rank = 3 := by
  rw [rank_communicationMatrix_dotProduct, Fintype.card_fin]
  rfl

example : (signMatrix ℝ fun x y : Fin 2 → Bool => x ⬝ᵥ y).rank = 4 := by
  rw [rank_signMatrix_dotProduct, Fintype.card_fin]
  rfl

/-! ### Axiom guards -/

/-- info: 'Cslib.Communication.Protocol.ecomplexityFun_swap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Protocol.ecomplexityFun_swap

/-- info: 'Cslib.Communication.Protocol.ecomplexityFun_le_clog_card_succ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Protocol.ecomplexityFun_le_clog_card_succ

/-- info: 'Cslib.Communication.ecomplexityFun_equality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ecomplexityFun_equality

/-- info: 'Cslib.Communication.card_add_two_le_leaves_of_run_eq_equality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms card_add_two_le_leaves_of_run_eq_equality

/-- info: 'Cslib.Communication.ecomplexityFun_decide_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ecomplexityFun_decide_le

/-- info: 'Cslib.Communication.Protocol.Solves.rank_communicationMatrix_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Protocol.Solves.rank_communicationMatrix_le

/-- info: 'Cslib.Communication.rank_communicationMatrix_dotProduct' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rank_communicationMatrix_dotProduct

end CommunicationComplexity4Tests
