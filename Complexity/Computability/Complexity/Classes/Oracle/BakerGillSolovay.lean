/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle.Diagonal
public import Complexity.Computability.Complexity.Classes.Oracle.Deterministic
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# An oracle relative to which `P` and `NP` differ

For an oracle language `B`, the unary language `Cslib.Complexity.unaryLanguage B` consists of the
words `1ⁿ` such that `B` has a word of length `n`. Baker, Gill and Solovay construct an oracle `B`
for which this language is not in `P` relative to `B`, while it is in `NP` relative to every
oracle (a certificate is a word of length `n` in `B`) [Arora and Barak, Theorem 3.7][AroraBarak09].

The oracle diagonalizes against all candidate deciders at once
(`Cslib.Complexity.exists_oracle_diagonal`). The candidates are the fair-coin tables with one
oracle channel and control states `Fin m`, under the clocks `c * (n + 1) ^ d`, run on `1ⁿ` with
every coin fixed to `false`. They are countably many, and each makes at most one request per
instruction, hence fewer than `2 ^ n` requests for all large `n`. Every decider in `P` relative to
`B` is one of them on the instances `1ⁿ`
(`Cslib.Probability.IsOraclePPTOn.exists_fin_run_pure_false`), so none decides the unary language
(`Cslib.Complexity.exists_unaryLanguage_not_mem_PWithOracle`).

## Main definitions

* `Cslib.Complexity.unaryLanguage`: the words `1ⁿ` such that the oracle has a word of length `n`.

## Main results

* `Cslib.Complexity.exists_unaryLanguage_not_mem_PWithOracle`: for some oracle `B`, the unary
  language of `B` is not in `P` relative to `B`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Probability

/-- The words `1ⁿ` such that `B` has a word of length `n`. -/
def unaryLanguage (B : Set (List Bool)) : Set (List Bool) :=
  {x | (∀ b ∈ x, b = true) ∧ ∃ w ∈ B, w.length = x.length}

theorem replicate_mem_unaryLanguage {B : Set (List Bool)} {n : ℕ} :
    List.replicate n true ∈ unaryLanguage B ↔ ∃ w ∈ B, w.length = n := by
  simp only [unaryLanguage, Set.mem_ofPred_eq, List.length_replicate]
  exact and_iff_right fun b hb => (List.eq_of_mem_replicate hb)

namespace BakerGillSolovay

/-- A candidate decider: a fair-coin table with `k` work tapes, control `Fin m` and one oracle
channel, together with the constants `c` and `d` of its clock `c * (n + 1) ^ d`. -/
abbrev Candidate : Type := Σ k m : ℕ, MultiTapePTM k Bool (Fin m) Unit × ℕ × ℕ

instance : Countable Candidate := by
  have (k m : ℕ) : Countable (MultiTapePTM k Bool (Fin m) Unit) :=
    have := MultiTapePTM.finite (k := k) (Symbol := Bool) (State := Fin m) (Oracle := Unit)
    inferInstance
  infer_instance

/-- The clock `c * (n + 1) ^ d` of a candidate on inputs of length `n`. -/
def Candidate.clock (candidate : Candidate) (n : ℕ) : ℕ :=
  candidate.2.2.2.1 * (n + 1) ^ candidate.2.2.2.2

/-- The verdict of a candidate on `1ⁿ`: its clocked run with every coin fixed to `false`, accepting
exactly with output `[true]`. -/
def Candidate.verdict (candidate : Candidate) (n : ℕ) : WordQueryComp Unit Bool :=
  (fun output => decide (output = [true])) <$> candidate.2.2.1.run (pure false)
    (fun op word => OracleComp.query (op, word)) (candidate.clock n) (List.replicate n true)

/-- A candidate makes at most one request per instruction. -/
theorem Candidate.length_queriesWith_verdict_le (candidate : Candidate) (n : ℕ)
    (A : Set (List Bool)) :
    (OracleComp.queriesWith (languageOracle A) (candidate.verdict n)).length ≤
      candidate.clock n := by
  simp only [verdict, MultiTapePTM.run, MultiTapePTM.runFrom, OracleComp.queriesWith_map]
  exact MultiTapeMachine.length_queriesWith_runConfigFrom_le candidate.2.2.1
    (fun choices => choices false) _ _ _

/-- Every clock is eventually below `2 ^ n`. -/
theorem Candidate.eventually_clock_lt (candidate : Candidate) :
    ∀ᶠ n in Filter.atTop, candidate.clock n < 2 ^ n :=
  PolynomiallyBounded.eventually_lt_two_pow (f := candidate.clock)
    (by unfold Candidate.clock; fun_prop)

end BakerGillSolovay

open BakerGillSolovay in
/-- **Baker–Gill–Solovay, the lower bound** [Arora and Barak, Theorem 3.7][AroraBarak09]: for some
oracle language `B`, the unary language of `B` is not decidable in polynomial time relative to
`B`. -/
theorem exists_unaryLanguage_not_mem_PWithOracle :
    ∃ B : Set (List Bool), unaryLanguage B ∉ PWithOracle B encBits := by
  obtain ⟨B, hB⟩ := exists_oracle_diagonal Candidate.verdict Candidate.clock
    Candidate.eventually_clock_lt Candidate.length_queriesWith_verdict_le
  refine ⟨B, fun ⟨f, ⟨program, hcertificate, hprogram⟩, hf⟩ => ?_⟩
  obtain ⟨k, m, machine, c, d, hrun⟩ := hcertificate.exists_fin_run_pure_false
  obtain ⟨n, hn⟩ := hB ⟨k, m, machine, c, d⟩
  apply hn
  have hlength : (encBits (List.replicate n true)).length = n := by
    simp [encBits]
  have hverdict := hrun (List.replicate n true) (languageOracle B)
  rw [hprogram, encBool_apply, hlength] at hverdict
  simp only [encBits, Function.Embedding.refl_apply] at hverdict
  have heq : OracleComp.interpret (m := Id) (languageOracle B)
      (Candidate.verdict ⟨k, m, machine, c, d⟩ n) = f (List.replicate n true) := by
    simp only [Candidate.verdict, Candidate.clock, OracleComp.interpret_map]
    rw [hverdict]
    cases f (List.replicate n true) <;> rfl
  rw [heq, ← hf, replicate_mem_unaryLanguage]

end Cslib.Complexity
