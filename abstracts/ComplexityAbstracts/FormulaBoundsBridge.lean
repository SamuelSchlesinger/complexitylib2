/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import Complexity.Computability.Circuit.Boolean.Spira
import Complexity.Computability.Circuit.Boolean.KhrapchenkoDepth
import Complexity.Computability.Circuit.Boolean.Yablonskii
import Complexity.Computability.Circuit.Boolean.Formula.Andreev

/-! # Bridges for formula balancing and lower bounds -/

namespace ComplexityTests.Abstracts.FormulaBoundsBridge

/-- A De Morgan expression is a tree of binary AND/OR, unary NOT, constants, and input leaves.
Only the elementary tree datatype/evaluator/costs in the explicitly allowed Formula module are
used; the lower-bound and balancing implementations are not allowed dependencies. -/
abbrev Expression (n : ℕ) := Cslib.Circuits.Formula Cslib.Circuits.Boolean.signature n

/-- The Boolean function computed by an expression under the standard interpretation. -/
def evaluate {n : ℕ} (F : Expression n) : (Fin n → Bool) → Bool :=
  F.eval Cslib.Circuits.Boolean.interpretation

/-- Input occurrences are counted with multiplicity. Constants contribute zero leaves. -/
def leaves {n : ℕ} (F : Expression n) : ℕ := F.leafSize

/-- Count AND/OR gates on the longest path; NOT and constant gates cost zero. -/
def andOrDepth {n : ℕ} (F : Expression n) : ℕ :=
  F.depthWith (fun op : Cslib.Circuits.Boolean.Op =>
    match op with | .and | .or => 1 | .const _ | .not => 0)

/-- The least number of input occurrences in an expression computing `f`. Every Boolean
function has such an expression; this minimum is a size measure, not a search algorithm. -/
noncomputable def minimumLeaves {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf {L | ∃ F : Expression n, (∀ x, evaluate F x = f x) ∧ leaves F = L}

/-- Parity is true exactly when an odd number of input bits are true. -/
def parity (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter fun i => x i = true).card % 2 = 1)

/-- The binary number represented by a word, with coordinate zero least significant. -/
def tableIndex (n : ℕ) : (Fin n → Bool) ≃ Fin (2 ^ n) :=
  (Equiv.arrowCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- Andreev's function: the first `2^b` bits are a truth table; the next `b*m` bits form `b`
blocks whose parities address that table. The table is part of the input, not a hardwired oracle. -/
def andreev (b m : ℕ) (x : Fin (2 ^ b + b * m) → Bool) : Bool :=
  x (Fin.castAdd (b * m) (tableIndex b fun j =>
    parity m fun t => x (Fin.natAdd (2 ^ b) (finProdFinEquiv (j, t)))))

/-- **Spira.** Balancing preserves the function and bounds AND/OR depth by four times the
ceiling logarithm of the original leaf count. For a constant expression the bound is zero. -/
theorem spira {n : ℕ} (F : Expression n) :
    ∃ G : Expression n, (∀ x, evaluate G x = evaluate F x) ∧
      andOrDepth G ≤ 4 * Nat.clog 2 (leaves F) :=
  Cslib.Circuits.Boolean.exists_formula_depthWith_le_four_mul_clog F

/-- **Khrapchenko.** If an expression is true on `A` and false on `B`, the square of the
number of Hamming-distance-one pairs between them is at most `leaves * |A| * |B|`. -/
theorem khrapchenko {n : ℕ} (F : Expression n)
    (A B : Finset (Fin n → Bool)) (hA : ∀ x ∈ A, evaluate F x = true)
    (hB : ∀ x ∈ B, evaluate F x = false) :
    ((A ×ˢ B).filter fun p => hammingDist p.1 p.2 = 1).card ^ 2 ≤
      leaves F * A.card * B.card :=
  Cslib.Circuits.Formula.sq_card_hammingEdges_le F hA hB

/-- Parity on `n` bits requires at least `n²` input leaves, including `n = 0`. -/
theorem parity_lower_bound {n : ℕ} (F : Expression n)
    (hF : ∀ x, evaluate F x = parity n x) : n ^ 2 ≤ leaves F :=
  Cslib.Circuits.Boolean.sq_le_leafSize_of_computes_parity hF

/-- The lower bound is attained at every power-of-two arity. -/
theorem parity_exact_at_powers_of_two (k : ℕ) :
    ∃ F : Expression (2 ^ k), (∀ x, evaluate F x = parity (2 ^ k) x) ∧
      leaves F = (2 ^ k) ^ 2 :=
  Cslib.Circuits.Boolean.exists_formula_parity_two_pow k

/-- **Yablonskii.** Every parity function has an expression within a factor `9/8` of `n²`.
This counts formula leaves, not gates in a circuit that shares intermediate values. -/
theorem yablonskii (n : ℕ) :
    ∃ F : Expression n, (∀ x, evaluate F x = parity n x) ∧ 8 * leaves F ≤ 9 * n ^ 2 :=
  Cslib.Circuits.Boolean.exists_formula_parity_eight_mul_leafSize_le n

/-- Free negations still leave a depth lower bound of `ceil(log₂(n²))` for parity. -/
theorem parity_depth_lower_bound {n : ℕ} (F : Expression n)
    (hF : ∀ x, evaluate F x = parity n x) : Nat.clog 2 (n ^ 2) ≤ andOrDepth F :=
  (Cslib.Circuits.Boolean.clog_sq_le_formulaDepth_parity n).trans
    (Cslib.Circuits.Boolean.formulaDepth_le hF)

/-- **Subbotovskaya.** Some restriction leaving exactly `k` coordinates free shrinks squared
formula size by at least `(k/n)³`. Fixed coordinates use `some bit`; `none` leaves a coordinate
free. Free coordinates remain in the original `n`-coordinate space and are counted explicitly. -/
theorem subbotovskaya {n : ℕ} (f : (Fin n → Bool) → Bool) {k : ℕ}
    (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ∃ ρ : Fin n → Option Bool,
      (Finset.univ.filter fun i => ρ i = none).card = k ∧
      minimumLeaves (fun x => f (fun i => (ρ i).getD (x i))) ^ 2 * n ^ 3 ≤
        minimumLeaves f ^ 2 * k ^ 3 :=
by
  obtain ⟨ρ, hρ, hbound⟩ :=
    Cslib.Circuits.Boolean.exists_withFree_formulaSize_sq_mul_pow_three_le f hk1 hkn
  exact ⟨ρ, Cslib.BitString.PartialAssignment.mem_withFree.mp hρ, hbound⟩

/-- **Andreev.** Beyond one fixed cutoff in `b`, every `m ≥ floor(log₂ b)+2` gives the
following quantitative formula-size bound. Taking `m = 2^b` yields the familiar
`n^(5/2-o(1))` bound, with `n = (b+1)2^b`. The theorem does not concern general circuits. -/
theorem andreev_lower_bound :
    ∃ B : ℕ, ∀ b ≥ B, ∀ m ≥ Nat.log 2 b + 2,
      2 ^ (2 * b) * m ^ 3 ≤
        144 * b ^ 2 * (Nat.log 2 b + 2) ^ 3 * minimumLeaves (andreev b m) ^ 2 :=
  Cslib.Circuits.Boolean.pow_two_mul_pow_three_le_formulaSize_andreev_sq

end ComplexityTests.Abstracts.FormulaBoundsBridge
