/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.TupleInterpretation

/-! # Arbitrary-base tuple numbering, order formulas and interpreted constants -/

@[expose] public section

namespace Cslib.Tests.OrderedTuples

open FirstOrder Language Structure Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.Ordered

abbrev L : Language := Language.empty

instance {n : ℕ} : L.Structure (Fin n) := Language.emptyStructure
instance : Fact (2 ≤ 3) := ⟨by decide⟩
instance : Fact (2 ≤ 5) := ⟨by decide⟩

/-- These tuples reverse their relative order under the old colexicographic numbering. -/
def x : Fin 2 → Fin 3 := ![0, 2]
def y : Fin 2 → Fin 3 := ![1, 0]

example : lexRank x = 2 := by decide
example : lexRank y = 3 := by decide
example : tupleIndex x = 6 := by decide
example : tupleIndex y = 1 := by decide
example : lexRank x < lexRank y ∧ tupleIndex y < tupleIndex x := by decide

example : Pi.Lex (· < ·) (· < ·) x y :=
  (lexRank_lt_iff_lex x y).mp (by decide)

/-- Base five also uses arithmetic digits, not concatenated binary coordinates. -/
example : lexRank (![3, 2] : Fin 2 → Fin 5) = 17 := by decide
example : ((lexEquiv.symm (17 : Fin (5 ^ 2))) 0).val = 3 := by
  rw [lexEquiv_symm_apply_val]
  decide
example : ((lexEquiv.symm (17 : Fin (5 ^ 2))) 1).val = 2 := by
  rw [lexEquiv_symm_apply_val]
  decide

/-- The zero-dimensional universe has one tuple, even at base zero. -/
example (z : Fin 0 → Fin 0) : lexRank z = 0 := by
  rw [lexRank_apply]
  simp

example : lexRank (tupleZero (n := 3) (k := 2)) = 0 := lexRank_tupleZero
example : lexRank (tupleOne (n := 3) (k := 1)) = 1 := lexRank_tupleOne
example : lexRank (tupleMax (n := 3) (k := 2)) = 8 := lexRank_tupleMax
example : lexRank (tupleMax (n := 5) (k := 3)) = 124 := lexRank_tupleMax

example : (tupleLt L 2).IsQF := isQF_tupleLt L 2
example : (tupleLe L 2).IsQF := isQF_tupleLe L 2

example : (tupleLt L 2).Realize (fun p => if p.1 = 0 then x p.2 else y p.2) := by
  rw [realize_tupleLt]
  decide

example : ¬ (tupleLe L 2).Realize (fun p => if p.1 = 0 then y p.2 else x p.2) := by
  rw [realize_tupleLe]
  decide

example : (tupleLe L 0).Realize (fun p => p.2.elim0 : Fin 2 × Fin 0 → Fin 3) := by
  rw [realize_tupleLe]

/-- A genuine validity witness for target constants on the full two-dimensional domain. -/
example : (tupleConstants L 1).Valid (Fin 3) := tupleConstants_valid
example : ((tupleConstants L 1).constant .one).IsQF := isQF_tupleConstants L 1 .one
example : ((tupleConstants L 1).constant .one).Realize (![0, 1] : Fin 2 → Fin 3) := by
  rw [realize_tupleConstants]
  decide
example : lexRank ((tupleConstants L 1).value (tupleConstants_valid (n := 3)) .max).val = 8 :=
  lexRank_tupleConstants_value .max
example : lexRank ((tupleConstants L 2).value (tupleConstants_valid (n := 5)) .one).val = 1 :=
  lexRank_tupleConstants_value .one

/-- A sentence with target constants pulls back through the full tuple interpretation. -/
def separated : Language.empty[[NumericFunction 0]].Sentence :=
  ((Language.empty.con .zero).term.equal (Language.empty.con .one).term).not

example : Fin 3 ⊨ (tupleConstants L 1).onSentence separated := by
  rw [(tupleConstants L 1).realize_onSentence tupleConstants_valid]
  simp only [separated, Sentence.Realize, Formula.realize_not, Formula.realize_equal,
    Term.realize_constants]
  intro h
  have hr := congrArg (fun z : (fullTuple L 2).Model (Fin 3) => lexRank z.val) h
  change lexRank ((tupleConstants L 1).value tupleConstants_valid .zero).val =
    lexRank ((tupleConstants L 1).value tupleConstants_valid .one).val at hr
  simp only [lexRank_tupleConstants_value] at hr
  contradiction

/-- info: 'Cslib.Logic.FO.Ordered.lexRank_lt_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Logic.FO.Ordered.lexRank_lt_iff

/-- info: 'Cslib.Logic.FO.Ordered.realize_tupleLe' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Logic.FO.Ordered.realize_tupleLe

/-- info: 'Cslib.Logic.FO.Ordered.lexRank_tupleConstants_value' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Logic.FO.Ordered.lexRank_tupleConstants_value

end Cslib.Tests.OrderedTuples
