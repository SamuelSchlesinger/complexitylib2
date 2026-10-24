/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Oracle.Transcript
public import Complexity.Probability.Forking
import Complexity.Languages.Probabilistic.Presample
import Complexity.Languages.Probabilistic.Repeat
import Complexity.Probability.PMF
import Complexity.Probability.Product

/-!
# Forking oracle programs

An oracle program `P s : OracleComp (fun _ : Query => H) (Option ℕ × β)`, with explicit coins
`s`, asks queries whose answers lie in a finite set `H` and finally names one of its queries by
its position, or none. Forking runs it with uniform answers and, if it names the query at
position `j`, runs it again on the same coins with the same answers before `j` and fresh answers
from `j` on. Both runs ask the same first `j + 1` queries (`mem_support_fork`), so the named
query is the same, while its two answers differ.

`runWithAnswers` runs a program on a list of answers, deterministically, recording its queries.
Answering queries from `q` presampled uniform answers has the law of answering them uniformly as
they come, when the program asks at most `q` queries: this is the presampling theorem
`ProbOracleComp.HasQueryBounds.eval_presample` (`interpret_uniform_eq`). Hence the general forking
lemma (`Probability.Forking.le_add_sqrt_fork`) bounds the acceptance probability of the program
with uniform answers by `q / |H| + √(q · frk)` (`le_add_sqrt_fork`).

The coins are explicit: the second run replays them. A program with private randomness is put in
this form by drawing its coins in advance. The statements are exact; no efficiency is involved.

## Main definitions

* `Cslib.OracleComp.runWithAnswers`: run on a list of answers, recording the queries.
* `Cslib.OracleComp.indexBelow`: the named position, if it is below `q`.
* `Cslib.OracleComp.forkingAlgorithm`: a program on coins and an answer vector, for forking.

## Main results

* `Cslib.OracleComp.interpret_uniform_eq`: uniform answers as they come, or presampled.
* `Cslib.OracleComp.le_add_sqrt_fork`: the forking lemma for oracle programs.
* `Cslib.OracleComp.mem_support_fork`: both runs of a successful fork ask the same queries up to
  the named one, and answer it differently.
* `Cslib.OracleComp.take_runWithAnswers`: a program's first `n + 1` queries depend only on its
  first `n` answers.

## References

* [M. Bellare, G. Neven, *Multi-Signatures in the Plain Public-Key Model and a General Forking
  Lemma*][BellareNeven2006], Lemma 1.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Lemma 19.8.
-/

@[expose] public section

namespace Cslib.OracleComp

open Probability

variable {Query H α : Type}

/-- Run a program on a list of answers, in order, answering `default` once the list is exhausted;
return its result and its queries, in order. -/
def runWithAnswers (default : H) : OracleComp (fun _ : Query => H) α → List H → α × List Query
  | .pure a, _ => (a, [])
  | .liftBind q cont, answers =>
    ((runWithAnswers default (cont (answers.headD default)) answers.tail).1,
      q :: (runWithAnswers default (cont (answers.headD default)) answers.tail).2)

/-- A program's first `n + 1` queries depend only on the first `n` answers. -/
theorem take_runWithAnswers (default : H) (program : OracleComp (fun _ : Query => H) α) :
    ∀ {answers answers' : List H} {n : ℕ}, answers.take n = answers'.take n →
      (runWithAnswers default program answers).2.take (n + 1) =
        (runWithAnswers default program answers').2.take (n + 1) := by
  induction program with
  | pure a => intros; rfl
  | liftBind q cont ih =>
    intro answers answers' n h
    cases n with
    | zero => rfl
    | succ n =>
      have hsplit : answers.headD default = answers'.headD default ∧
          answers.tail.take n = answers'.tail.take n := by
        cases answers <;> cases answers' <;> simp_all
      simp only [runWithAnswers, List.take_succ_cons, hsplit.1, ih _ hsplit.2]

/-! ### Presampled answers -/

/-- Answering the lifted program from a saved list is running it on that list. -/
private theorem eval_run_withSampleList (default : H)
    (program : OracleComp (fun _ : Query => H) α) (answers : List H) :
    ProbComp.eval ((fun (result, next, _) => (result, next)) <$>
      (interpret (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n))
        (withSampleList default fun v _ s => (pure (v, s) : ProbComp (H × Unit))))
          (interpret (fun q => ProbOracleComp.query (spec := fun _ : Query => H) q)
            program)).run ((), answers)) =
      PMF.pure ((runWithAnswers default program answers).1, ()) := by
  induction program generalizing answers with
  | pure a => rfl
  | liftBind q cont ih =>
    change _ = PMF.pure ((runWithAnswers default (cont (answers.headD default)) answers.tail).1, ())
    rw [← ih (answers.headD default) answers.tail]
    rfl

/-- Answering lifted queries uniformly as they come is answering them uniformly. -/
private theorem eval_run_uniform [Fintype H] [Nonempty H]
    (program : OracleComp (fun _ : Query => H) α) :
    ProbComp.eval ((interpret (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n))
        (fun _ s => do
          let value ← ProbComp.uniform H
          (pure (value, s) : ProbComp (H × Unit))))
          (interpret (fun q => ProbOracleComp.query (spec := fun _ : Query => H) q)
            program)).run ()) =
      (interpret (fun _ => PMF.uniformOfFintype H) program).map (·, ()) := by
  have hstate : (fun (_ : Query) (s : Unit) => do
      let value ← ProbComp.uniform H
      (pure (value, s) : ProbComp (H × Unit))) =
      fun _ s => (fun a => (a, s)) <$> ProbComp.uniform H := by
    funext _ s
    rw [map_eq_bind_pure_comp]
    rfl
  have heval : ProbComp.eval (interpret (fun _ => ProbComp.uniform H) program) =
      interpret (fun _ => PMF.uniformOfFintype H) program := by
    change interpret ProbComp.unifOracle (interpret _ program) = _
    rw [interpret_interpret]
    congr 1
    funext q
    exact ProbComp.eval_uniform H
  rw [interpret_interpret]
  simp only [ProbOracleComp.interpret_query]
  rw [hstate, run_interpret_stateless, ProbComp.eval_map, heval]

/-- `q` uniform samples, collected in a list, are the entries of a uniform vector. -/
private theorem eval_replicate_uniform [Fintype H] [Nonempty H] (q : ℕ) :
    ProbComp.eval (replicate q (ProbComp.uniform H)) =
      (PMF.uniformOfFintype (Fin q → H)).map List.ofFn := by
  induction q with
  | zero =>
    have hconst : (List.ofFn : (Fin 0 → H) → List H) = Function.const _ [] :=
      funext fun _ => List.ofFn_zero
    rw [replicate_zero, ProbComp.eval_pure, hconst, PMF.map_const]
  | succ q ih =>
    rw [replicate_succ, ← Probability.PMF.pi_uniformOfFintype, Probability.PMF.pi_fin_succ,
      Probability.PMF.pi_uniformOfFintype]
    simp only [ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_uniform, ih, PMF.map_bind,
      PMF.map_comp, Function.comp_def, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]

/-- The lazy law of uniform answers is the law of `q` presampled uniform answers, for a program
asking at most `q` queries: an instance of the presampling theorem
`ProbOracleComp.HasQueryBounds.eval_presample`. -/
theorem interpret_uniform_eq [Fintype H] [Nonempty H] (default : H)
    (program : OracleComp (fun _ : Query => H) α) {size : Query → ℕ} {q maxSize : ℕ}
    (hq : (interpret (fun q => ProbOracleComp.query (spec := fun _ : Query => H) q)
      program).HasQueryBounds size q maxSize) :
    interpret (fun _ => PMF.uniformOfFintype H) program =
      (PMF.uniformOfFintype (Fin q → H)).map fun h =>
        (runWithAnswers default program (List.ofFn h)).1 := by
  have hp := hq.eval_presample (ProbComp.uniform H) default
    (fun v _ s => (pure (v, s) : ProbComp (H × Unit))) ()
  rw [eval_run_uniform, ProbComp.eval_bind, eval_replicate_uniform] at hp
  simp only [eval_run_withSampleList, PMF.bind_map, Function.comp_def] at hp
  have hfst := congrArg (PMF.map Prod.fst) hp
  simp only [PMF.map_comp, Function.comp_def] at hfst
  rw [show PMF.map (fun x => x) (interpret (fun _ => PMF.uniformOfFintype H) program) =
    interpret (fun _ => PMF.uniformOfFintype H) program from PMF.map_id _] at hfst
  rw [← hfst, PMF.map_bind]
  simp only [PMF.pure_map]
  rfl

/-! ### Forking -/

/-- The named position, if it is below `q`. -/
def indexBelow (q : ℕ) (position : Option ℕ) : Option (Fin q) :=
  position.bind fun j => if h : j < q then some ⟨j, h⟩ else none

/-- A program with explicit coins as an algorithm on coins and `q` answers, for the general
forking lemma: the named position below `q`, and the result with the queries. -/
def forkingAlgorithm {S β : Type} (default : H) (q : ℕ)
    (program : S → OracleComp (fun _ : Query => H) (Option ℕ × β)) (s : S) (h : Fin q → H) :
    Option (Fin q) × ((Option ℕ × β) × List Query) :=
  (indexBelow q (runWithAnswers default (program s) (List.ofFn h)).1.1,
    runWithAnswers default (program s) (List.ofFn h))

variable {S β : Type} [Fintype H] [Nonempty H] [DecidableEq H]

/-- **The forking lemma for oracle programs** ([BellareNeven2006], Lemma 1): if a program with
explicit coins asks at most `q` queries, and names a position below `q` with probability `acc`
when its queries are answered uniformly as they come, then forking it succeeds with probability
`frk` such that `acc ≤ q / |H| + √(q · frk)`. -/
theorem le_add_sqrt_fork (first : PMF S)
    (program : S → OracleComp (fun _ : Query => H) (Option ℕ × β)) (default : H)
    {size : Query → ℕ} {q maxSize : ℕ}
    (hq : ∀ s, (interpret (fun q => ProbOracleComp.query (spec := fun _ : Query => H) q)
      (program s)).HasQueryBounds size q maxSize) :
    ((do
      let s ← first
      let result ← interpret (fun _ => PMF.uniformOfFintype H) (program s)
      return (indexBelow q result.1).isSome : PMF Bool) true).toReal ≤
      q / Fintype.card H + √(q * ((Forking.fork first (forkingAlgorithm default q program)).map
        Option.isSome true).toReal) := by
  have hacc : (do
      let s ← first
      let result ← interpret (fun _ => PMF.uniformOfFintype H) (program s)
      return (indexBelow q result.1).isSome : PMF Bool) =
      Forking.accept first (forkingAlgorithm default q program) := by
    simp only [Forking.accept, forkingAlgorithm, Probability.PMF.monad_bind_eq_bind,
      Probability.PMF.monad_pure_eq_pure]
    refine congrArg _ (funext fun s => ?_)
    rw [interpret_uniform_eq default (program s) (hq s), PMF.bind_map]
    rfl
  rw [hacc]
  exact Forking.le_add_sqrt_fork first _

/-- A successful fork of a program reruns it on the same coins with answers that agree before the
named position `j` and differ at it; both runs name `j` and ask the same first `j + 1`
queries. -/
theorem mem_support_fork {first : PMF S}
    {program : S → OracleComp (fun _ : Query => H) (Option ℕ × β)} {default : H} {q : ℕ}
    {j : Fin q} {out out' : (Option ℕ × β) × List Query}
    (hfork : some (j, out, out') ∈
      (Forking.fork first (forkingAlgorithm default q program)).support) :
    ∃ s ∈ first.support, ∃ h h' : Fin q → H, (∀ i < j, h i = h' i) ∧ h j ≠ h' j ∧
      out = runWithAnswers default (program s) (List.ofFn h) ∧
      out' = runWithAnswers default (program s) (List.ofFn h') ∧
      out.1.1 = some j.val ∧ out'.1.1 = some j.val ∧ out.2.take (j + 1) = out'.2.take (j + 1) := by
  obtain ⟨s, hs, h, h', hagree, hne, hrun, hrun'⟩ := Forking.mem_support_fork hfork
  simp only [forkingAlgorithm, Prod.mk.injEq] at hrun hrun'
  obtain ⟨hidx, rfl⟩ := hrun
  obtain ⟨hidx', rfl⟩ := hrun'
  have hpos {r : Option ℕ} (hr : indexBelow q r = some j) : r = some j.val := by
    cases r with
    | none => simp [indexBelow] at hr
    | some r =>
      simp only [indexBelow, Option.bind_some] at hr
      split_ifs at hr with hlt
      · simp only [Option.some.injEq, Fin.ext_iff] at hr
        rw [hr]
  refine ⟨s, hs, h, h', hagree, hne, rfl, rfl, hpos hidx, hpos hidx',
    take_runWithAnswers default (program s) ?_⟩
  refine List.ext_getElem (by simp) fun i hi _ => ?_
  simp only [List.length_take, List.length_ofFn] at hi
  simp only [List.getElem_take, List.getElem_ofFn]
  exact hagree ⟨i, by omega⟩ (Fin.mk_lt_of_lt_val (by omega))

end Cslib.OracleComp
