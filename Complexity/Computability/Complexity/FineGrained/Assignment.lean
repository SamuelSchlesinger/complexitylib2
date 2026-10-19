/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained
public import Complexity.Computability.Complexity.Problems.SubsetSum
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.Nat.Bitwise

/-!
# Numbered assignments

Exhaustive search over the assignments of the `n` distinct variables of a formula enumerates the
numbers `i < 2 ^ n`. `Cslib.Logic.PL.bitsAssignment vs i` gives the variable at position `j` of
the list `vs` the binary digit `j` of `i`. Every assignment of the variables of a duplicate-free
list `vs` is numbered by some `i < 2 ^ |vs|` (`Cslib.Logic.PL.exists_lt_two_pow_bitsAssignment_eq`),
so a formula whose variables are listed by `vs` is satisfiable exactly when one of the numbered
assignments satisfies it (`Cslib.Logic.PL.CNF.satisfiable_iff_exists_bitsAssignment`). The
distinct variables of a formula are listed by `Cslib.Complexity.ThreeSAT.distinctVars`, of length
`Cslib.Logic.PL.CNF.numVars` (`Cslib.Complexity.ThreeSAT.length_distinctVars`). Evaluating a
formula under a numbered assignment is polynomial-time
(`Cslib.Complexity.computableTidilyInPolyTime_eval_bitsAssignment`).

## Main definitions

* `Cslib.Logic.PL.bitsAssignment`: the assignment numbered by `i`.

## Main results

* `Cslib.Logic.PL.CNF.satisfiable_iff_exists_bitsAssignment`: satisfiability is a search over
  `2 ^ |vs|` numbered assignments.
* `Cslib.Complexity.ThreeSAT.length_distinctVars`: a formula has `numVars` distinct variables.
* `Cslib.Complexity.computableTidilyInPolyTime_eval_bitsAssignment`: evaluation under a numbered
  assignment is polynomial-time.
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {V : Type*} [DecidableEq V]

/-- The assignment numbered by `i` on the list of variables `vs`: the variable at position `j` of
`vs` takes the binary digit `j` of `i`. -/
def bitsAssignment (vs : List V) (i : ℕ) (v : V) : Bool := i.testBit (vs.idxOf v)

/-- **Every assignment is numbered.** The assignments of the variables of a duplicate-free list
`vs` are the numbered assignments `bitsAssignment vs i` for `i < 2 ^ |vs|`. -/
theorem exists_lt_two_pow_bitsAssignment_eq {vs : List V} (σ : V → Bool) :
    ∃ i < 2 ^ vs.length, ∀ v ∈ vs, bitsAssignment vs i v = σ v := by
  refine ⟨(BitVec.ofBoolListLE (vs.map σ)).toNat, (BitVec.isLt _).trans_eq (by simp),
    fun v hv => ?_⟩
  have hlt : vs.idxOf v < vs.length := List.idxOf_lt_length_iff.mpr hv
  rw [bitsAssignment, BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt,
    List.getElem_idxOf hlt]
  rfl

/-- **Satisfiability by exhaustive search.** A formula whose variables are all in the list `vs` is
satisfiable exactly when it is satisfied by an assignment numbered by some `i < 2 ^ |vs|`. -/
theorem CNF.satisfiable_iff_exists_bitsAssignment {φ : CNF V} {vs : List V}
    (hφ : ∀ v ∈ φ.vars, v ∈ vs) :
    φ.Satisfiable ↔ ∃ i < 2 ^ vs.length, φ.eval (bitsAssignment vs i) = true := by
  refine ⟨fun ⟨σ, hσ⟩ => ?_, fun ⟨i, _, hi⟩ => ⟨_, hi⟩⟩
  obtain ⟨i, hi, hiσ⟩ := exists_lt_two_pow_bitsAssignment_eq (vs := vs) σ
  exact ⟨i, hi, (CNF.eval_congr fun v hv => hiσ v (hφ v hv)).trans hσ⟩

theorem bitsAssignment_eq_getD (vs : List V) (i : ℕ) (v : V) :
    bitsAssignment vs i v = i.bits.getD (vs.idxOf v) false := by
  rw [bitsAssignment, Nat.testBit_eq_inth]
  rfl

end Cslib.Logic.PL

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### The distinct variables -/

namespace ThreeSAT

theorem mem_vars_of_mem_distinctVars {φ : CNF ℕ} {v : ℕ} (hv : v ∈ distinctVars φ) :
    v ∈ φ.vars := by
  simp only [distinctVars, List.mem_map, List.mem_filter, Prod.exists, exists_and_right,
    exists_eq_right] at hv
  obtain ⟨i, hi, -⟩ := hv
  exact List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hi)

theorem mem_distinctVars {φ : CNF ℕ} {v : ℕ} : v ∈ distinctVars φ ↔ v ∈ φ.vars :=
  ⟨mem_vars_of_mem_distinctVars, mem_distinctVars_of_mem_vars⟩

/-- A formula has `numVars` distinct variables. -/
theorem length_distinctVars (φ : CNF ℕ) : (distinctVars φ).length = φ.numVars := by
  rw [CNF.numVars, ← List.toFinset_card_of_nodup nodup_distinctVars]
  congr 1
  ext v
  simp [mem_distinctVars]

end ThreeSAT

/-! ### Polynomial time -/

open ComputableTidilyInPolyTime in
/-- Evaluating a formula under the assignment numbered by `i` on a list of variables is
polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_eval_bitsAssignment :
    ComputableTidilyInPolyTime (fun p : (CNF ℕ × List ℕ) × ℕ => p.1.1.eval (bitsAssignment p.1.2 p.2))
      (encPair (encPair encCNF (encList encNat)) encNat) encBool := by
  have e : (fun p : (CNF ℕ × List ℕ) × ℕ => p.1.1.eval (bitsAssignment p.1.2 p.2)) =
      fun p => p.1.1.eval fun v => p.2.bits.getD (p.1.2.idxOf v) false := by
    funext p
    congr 1
    funext v
    exact bitsAssignment_eq_getD ..
  rw [e]
  unfold encCNF
  fun_prop [CNF.eval, Clause.eval, Literal.eval]

end Cslib.Complexity
