/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.Rectangle
public import Mathlib.Data.Nat.Log
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The rank bound and the log-rank conjecture

The *communication matrix* of a Boolean function `f : X → Y → Bool` over a ring `R` has rows
indexed by Alice's inputs, columns indexed by Bob's inputs, and entry `1` where `f` is true and `0`
elsewhere (`communicationMatrix`). A protocol computing `f` writes it as the sum, over the leaves
labelled `true`, of the indicator matrices of their rectangles, each of rank at most one. So over
any commutative ring with the strong rank condition, such as a field, the rank of the communication
matrix is at most the number of leaves labelled `true` (`Protocol.rank_communicationMatrix_le`), and
the ranks of the matrices of `f` and of its negation add up to at most the number of leaves
(`Protocol.rank_add_rank_not_le_leaves`). This is the *rank bound* `⌈log₂ rank M_f⌉ ≤ D(f)`
(`clog_rank_le_ecomplexity`) [Mehlhorn and Schmidt][MehlhornSchmidt1982],
[Kushilevitz and Nisan, Chapter 1][KushilevitzNisan1997].

The *log-rank conjecture* of Lovász and Saks asserts the converse up to a polynomial: the
communication complexity of every Boolean function is at most polynomial in the logarithm of the
rank of its communication matrix over the reals (`LogRankConjecture`) [LovaszSaks1988]. It is open.

## Main definitions

* `Cslib.Communication.communicationMatrix`: the communication matrix of a Boolean function.
* `Cslib.Communication.LogRankConjecture`: the log-rank conjecture, as a proposition.

## Main results

* `Cslib.Communication.Protocol.rank_communicationMatrix_le`: the rank of the communication matrix
  is at most the number of leaves labelled `true`.
* `Cslib.Communication.Protocol.rank_add_rank_not_le_leaves`: the ranks of the matrices of `f` and
  of `!f` add up to at most the number of leaves.
* `Cslib.Communication.clog_rank_le_ecomplexity`: the rank bound.

## References

* [K. Mehlhorn and E. M. Schmidt, *Las Vegas is better than determinism in VLSI and distributed
  computing*][MehlhornSchmidt1982]
* [L. Lovász and M. Saks, *Lattices, Möbius functions and communication
  complexity*][LovaszSaks1988]
* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Communication

open Finset

variable {X Y Z : Type*}

/-- The communication matrix of a Boolean function `f` over `R`: rows are indexed by Alice's
inputs, columns by Bob's inputs, and the entry at `x` and `y` is `1` if `f x y` and `0`
otherwise. -/
def communicationMatrix (R : Type*) [Zero R] [One R] (f : X → Y → Bool) : Matrix X Y R :=
  Matrix.of fun x y => if f x y then 1 else 0

@[simp] theorem communicationMatrix_apply (R : Type*) [Zero R] [One R] (f : X → Y → Bool) (x : X)
    (y : Y) : communicationMatrix R f x y = if f x y then 1 else 0 :=
  rfl

namespace Protocol

variable [Fintype Y] {R : Type*} [CommSemiring R] [StrongRankCondition R]

/-- If a protocol computes `f`, then for every set of outputs, given by its indicator `g`, the rank
of the communication matrix of `g ∘ f` is at most the number of leaves labelled in the set. -/
theorem rank_communicationMatrix_comp_le {p : Protocol X Y Z} {f : X → Y → Z} (hp : p.run = f)
    (g : Z → Bool) :
    (communicationMatrix R fun x y => g (f x y)).rank ≤ #{i | g (p.leafOutput i) = true} := by
  classical
  set T : Finset (Fin p.leaves) := {i | g (p.leafOutput i) = true}
  let U : Matrix X T R := Matrix.of fun x i => if x ∈ p.leafAlice i then 1 else 0
  let V : Matrix T Y R := Matrix.of fun i y => if y ∈ p.leafBob i then 1 else 0
  have hUV : communicationMatrix R (fun x y => g (f x y)) = U * V := by
    ext x y
    simp only [communicationMatrix_apply, Matrix.mul_apply, U, V, Matrix.of_apply, ite_mul,
      one_mul, zero_mul, ← ite_and]
    rw [sum_coe_sort T fun i => if x ∈ p.leafAlice i ∧ y ∈ p.leafBob i then (1 : R) else 0]
    simp only [← leaf_eq_iff, sum_ite_eq, T, mem_filter, mem_univ, true_and,
      ← run_eq_leafOutput_leaf, hp]
  rw [hUV]
  exact (Matrix.rank_mul_le_left U V).trans ((Matrix.rank_le_card_width U).trans_eq
    (Fintype.card_coe T))

variable {p : Protocol X Y Bool} {f : X → Y → Bool}

/-- **The rank bound.** The rank of the communication matrix of a function computed by a protocol
is at most the number of leaves labelled `true`. -/
theorem rank_communicationMatrix_le (hp : p.run = f) :
    (communicationMatrix R f).rank ≤ #{i | p.leafOutput i = true} :=
  rank_communicationMatrix_comp_le hp id

/-- The ranks of the communication matrices of `f` and of its negation add up to at most the
number of leaves of a protocol computing `f`. -/
theorem rank_add_rank_not_le_leaves (hp : p.run = f) :
    (communicationMatrix R f).rank + (communicationMatrix R fun x y => !f x y).rank ≤
      p.leaves := by
  refine (add_le_add (rank_communicationMatrix_le hp)
    (rank_communicationMatrix_comp_le hp not)).trans ?_
  rw [← card_union_of_disjoint (disjoint_filter.mpr fun i _ h => by simp [h])]
  exact (card_le_univ _).trans_eq (card_fin p.leaves)

/-- A protocol computing `f` sends at least `log₂` of the rank of its communication matrix bits. -/
theorem rank_communicationMatrix_le_two_pow (hp : p.run = f) :
    (communicationMatrix R f).rank ≤ 2 ^ p.depth :=
  (rank_communicationMatrix_le hp).trans ((card_le_univ _).trans
    ((card_fin p.leaves).trans_le p.leaves_le_two_pow_depth))

end Protocol

/-- **The rank bound** [Mehlhorn and Schmidt][MehlhornSchmidt1982]: the communication complexity
of a Boolean function is at least `⌈log₂ r⌉`, for `r` the rank of its communication matrix over any
commutative ring with the strong rank condition, such as `ℝ`. -/
theorem clog_rank_le_ecomplexity [Fintype Y] (R : Type*) [CommSemiring R]
    [StrongRankCondition R] (f : X → Y → Bool) :
    (Nat.clog 2 (communicationMatrix R f).rank : ℕ∞) ≤
      Protocol.ecomplexity (fun x y b => f x y = b) Set.univ Set.univ :=
  Protocol.le_ecomplexity_iff.mpr fun _ hp => by
    exact_mod_cast Nat.clog_le_of_le_pow
      (Protocol.rank_communicationMatrix_le_two_pow (Protocol.solves_univ_iff.mp hp))

/-- **The log-rank conjecture** [LovaszSaks1988]: for some constant `c`, every Boolean function
`f` on finite sets has communication complexity at most `c (⌊log₂ r⌋ + 1) ^ c`, where `r` is the
rank of its communication matrix over `ℝ`. The rank bound `clog_rank_le_ecomplexity` is the converse
inequality up to rounding; the conjecture is open. -/
def LogRankConjecture : Prop :=
  ∃ c : ℕ, ∀ (X Y : Type) [Fintype X] [Fintype Y] (f : X → Y → Bool),
    Protocol.ecomplexity (fun x y b => f x y = b) Set.univ Set.univ ≤
      ((c * (Nat.log 2 (communicationMatrix ℝ f).rank + 1) ^ c : ℕ) : ℕ∞)

end Cslib.Communication
