/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Oracle.BakerGillSolovay

/-! Requests of adaptive word-query programs under language oracles, locality, membership in the
oracle classes, the unary language, candidate deciders and the Baker–Gill–Solovay lower bound. -/

namespace ComplexityTests.Relativization

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-! ### Adaptive requests -/

/-- Ask `[true]`; on a positive answer, also ask `[false]`. -/
def adaptive : WordQueryComp Unit Bool := do
  let reply ← OracleComp.query ((), [true])
  if reply = [true] then
    let second ← OracleComp.query ((), [false])
    return second = [true]
  else
    return false

/-- An oracle containing `[true]` receives the second request. -/
example : OracleComp.queriesWith (languageOracle {[true]}) adaptive =
    [((), [true]), ((), [false])] := by
  simp [adaptive, languageOracle_apply]

/-- The empty oracle does not. -/
example : OracleComp.queriesWith (languageOracle ∅) adaptive = [((), [true])] := by
  simp [adaptive, languageOracle_apply]

/-- The answer is whether both words are in the oracle. -/
example : OracleComp.interpret (m := Id) (languageOracle {[true], [false]}) adaptive = true := by
  simp only [adaptive, OracleComp.interpret_id_query_bind, languageOracle_apply]
  simp [languageOracle_apply]
  rfl

example : OracleComp.interpret (m := Id) (languageOracle {[true]}) adaptive = false := by
  simp only [adaptive, OracleComp.interpret_id_query_bind, languageOracle_apply]
  simp [languageOracle_apply]
  rfl

/-- Locality: words that are never requested do not matter. -/
example (A : Set (List Bool)) (hA : [true] ∉ A) :
    OracleComp.interpret (m := Id) (languageOracle A) adaptive =
      OracleComp.interpret (m := Id) (languageOracle ∅) adaptive :=
  (interpret_languageOracle_congr adaptive fun q hq => by
    simp only [adaptive, OracleComp.queriesWith_query_bind, languageOracle_apply,
      Set.mem_empty_iff_false, decide_false] at hq
    simp only [List.cons.injEq, Bool.false_eq_true, and_true, ite_false,
      OracleComp.queriesWith_pure, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    simpa using hA).1

/-! ### The oracle classes -/

/-- A problem in `P`, here every word, is in `P` relative to every oracle. -/
example (A : Set (List Bool)) : (Set.univ : Set (List Bool)) ∈ PWithOracle A encBits :=
  P_subset_PWithOracle A encBits ⟨fun _ => true, ComputableTidilyInPolyTime.const true,
    fun _ => by simp⟩

/-- A deterministic computation is polynomial time relative to an oracle, with a certificate. -/
example (A : Set (List Bool)) :
    ComputableInPolyTimeWithOracle A (fun _ : List Bool => false) encBits encBool :=
  (ComputableTidilyInPolyTime.const false).computableInPolyTimeWithOracle A

/-- `P` relative to `A` contains `A`, and lies inside `NP` relative to `A`. -/
example (A : Set (List Bool)) : A ∈ NPWithOracle A encBits :=
  PWithOracle_subset_NPWithOracle A encBits (mem_PWithOracle_self A)

/-- A reduction to the oracle language: words whose reversal is in `A`. -/
example (A : Set (List Bool)) : {w : List Bool | w.reverse ∈ A} ∈ PWithOracle A encBits :=
  PolyTimeReducible.mem_PWithOracle ⟨List.reverse, by fun_prop, fun _ => Iff.rfl⟩
    (mem_PWithOracle_self A)

/-! ### The unary language -/

example : [true, true] ∈ unaryLanguage {[false, true]} :=
  replicate_mem_unaryLanguage.mpr ⟨[false, true], rfl, rfl⟩

/-- The empty word asks for a word of length zero. -/
example : [] ∈ unaryLanguage {[]} := replicate_mem_unaryLanguage (n := 0).mpr ⟨[], rfl, rfl⟩

example : [] ∉ unaryLanguage ∅ := fun h => by simpa using h.2

/-- Words containing `false` are never in the unary language. -/
example (B : Set (List Bool)) : [true, false] ∉ unaryLanguage B := fun h => by
  simpa using h.1

example : [true] ∉ unaryLanguage {[], [true, true]} := fun h => by
  obtain ⟨-, w, hw, hlen⟩ := h
  rcases hw with rfl | rfl <;> simp at hlen

/-! ### Candidate deciders -/

/-- The candidates are countably many. -/
example : Countable BakerGillSolovay.Candidate := inferInstance

open BakerGillSolovay in
/-- A candidate with a machine that halts at once and a zero clock: its verdict makes no request
and rejects, against every oracle. -/
example (A : Set (List Bool)) (n : ℕ) :
    OracleComp.queriesWith (languageOracle A)
      (Candidate.verdict ⟨0, 1, ⟨0, fun _ _ _ _ _ => .step ⟨0, fun i => i.elim0, none, none⟩
        (fun _ => none) (fun _ => 0)⟩, 0, 0⟩ n) = [] ∧
    OracleComp.interpret (m := Id) (languageOracle A)
      (Candidate.verdict ⟨0, 1, ⟨0, fun _ _ _ _ _ => .step ⟨0, fun i => i.elim0, none, none⟩
        (fun _ => none) (fun _ => 0)⟩, 0, 0⟩ n) = false := by
  constructor <;> rfl

/-- The unary language of every oracle is in `NP` relative to it. -/
example : unaryLanguage {[true, false]} ∈ NPWithOracle {[true, false]} encBits :=
  unaryLanguage_mem_NPWithOracle _

/-! ### Axioms -/

/--
info: 'Cslib.Complexity.exists_PWithOracle_ssubset_NPWithOracle' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.exists_PWithOracle_ssubset_NPWithOracle

/--
info: 'Cslib.Complexity.unaryLanguage_mem_NPWithOracle' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.unaryLanguage_mem_NPWithOracle

/--
info: 'Cslib.Complexity.PolyTimeReducible.mem_NPWithOracle' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PolyTimeReducible.mem_NPWithOracle

/--
info: 'Cslib.Complexity.exists_unaryLanguage_not_mem_PWithOracle' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.exists_unaryLanguage_not_mem_PWithOracle

/--
info: 'Cslib.Complexity.exists_oracle_diagonal' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.exists_oracle_diagonal

/--
info: 'Cslib.Probability.IsOraclePPTOn.exists_fin_run_pure_false' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.IsOraclePPTOn.exists_fin_run_pure_false

end ComplexityTests.Relativization
