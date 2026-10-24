/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Oracle.Transcript
public import Complexity.Languages.Probabilistic.Presample
public import Complexity.Probability.IID
import Complexity.Probability.PMF

/-!
# Counting oracle calls structurally

`OracleComp.IsQueryBounded program n` says that `program` makes at most `n` oracle calls on every
path through its tree of calls, whatever the answers. This is the structural form of a call
budget: it is preserved by sequencing (`IsQueryBounded.bind`) and proved by induction on the
program, and it gives the semantic, handler-quantified bound
`ProbOracleComp.HasQueryBounds` for the program's external calls
(`IsQueryBounded.hasQueryBounds`). Running a program through a handler multiplies budgets
(`IsQueryBounded.run_interpret`).

A budget also justifies presampling: a handler that draws one sample per call can read its
samples from a list of independent draws made in advance, with the same law of the result and the
final state (`IsQueryBounded.run_interpret_withSampleList`).

## Main definitions

* `Cslib.OracleComp.IsQueryBounded`: at most `n` calls on every path.

## Main results

* `Cslib.OracleComp.IsQueryBounded.bind`: budgets add under sequencing.
* `Cslib.OracleComp.IsQueryBounded.hasQueryBounds`: the semantic external call bound.
* `Cslib.OracleComp.IsQueryBounded.run_interpret`: the budget of a program run through a handler.
* `Cslib.OracleComp.IsQueryBounded.run_interpret_withSampleList`: presampling a handler's draws.
-/

@[expose] public section

namespace Cslib.OracleComp

universe u v

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {α β : Type v}

/-- The program makes at most `n` oracle calls on every path, whatever the answers. -/
inductive IsQueryBounded : OracleComp spec α → ℕ → Prop
  /-- Returning a value makes no call. -/
  | pure (a : α) (n : ℕ) : IsQueryBounded (PFunctor.FreeM.pure a) n
  /-- A call followed by continuations that each make at most `n` calls. -/
  | liftBind (q : ι) (cont : spec q → OracleComp spec α) (n : ℕ)
      (hcont : ∀ a, IsQueryBounded (cont a) n) :
      IsQueryBounded (PFunctor.FreeM.liftBind q cont) (n + 1)

namespace IsQueryBounded

/-- A larger budget is still a budget. -/
theorem mono {program : OracleComp spec α} {n m : ℕ} (h : IsQueryBounded program n)
    (hnm : n ≤ m) : IsQueryBounded program m := by
  induction h generalizing m with
  | pure a n => exact .pure a m
  | liftBind q cont n _ ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact .liftBind q cont m fun a => ih a (by omega)

/-- One call. -/
theorem query (q : ι) : IsQueryBounded (OracleComp.query (spec := spec) q) 1 :=
  .liftBind q _ 0 fun a => .pure a 0

/-- Budgets add under sequencing. -/
theorem bind {program : OracleComp spec α} {next : α → OracleComp spec β} {n m : ℕ}
    (h : IsQueryBounded program n) (hnext : ∀ a, IsQueryBounded (next a) m) :
    IsQueryBounded (program >>= next) (n + m) := by
  induction h with
  | pure a n => exact (hnext a).mono (by omega)
  | liftBind q cont n _ ih =>
    rw [show n + 1 + m = n + m + 1 by omega]
    exact .liftBind q _ (n + m) ih

end IsQueryBounded

/-- A structural budget bounds the external calls of the program run with private
randomness, for every size bound on its queries. -/
theorem IsQueryBounded.hasQueryBounds {Query : Type} {Response : Query → Type} {γ : Type}
    {program : OracleComp Response γ} {n : ℕ} (h : IsQueryBounded program n)
    {size : Query → ℕ} {maxSize : ℕ} (hsize : ∀ q, size q ≤ maxSize) :
    (interpret (fun q => ProbOracleComp.query (spec := Response) q)
      program).HasQueryBounds size n maxSize := by
  induction h with
  | pure a n => exact (ProbOracleComp.HasQueryBounds.pure a size maxSize).mono (by omega) le_rfl
  | liftBind q cont n _ ih =>
    have hbind := (ProbOracleComp.HasQueryBounds.query (Response := Response) q size
      (hsize q)).bind ih
    rw [show 1 + n = n + 1 by omega] at hbind
    exact hbind

/-- A program run through a stateful handler, each of whose calls makes at most `k` calls to the
target oracle, makes at most `n * k` target calls when the program makes at most `n` calls. -/
theorem IsQueryBounded.run_interpret {κ : Type u} {target : OracleSpec.{u, v} κ} {σ : Type v}
    {handler : (q : ι) → StateT σ (OracleComp target) (spec q)} {k : ℕ}
    (hhandler : ∀ q s, IsQueryBounded ((handler q).run s) k) {program : OracleComp spec α}
    {n : ℕ} (h : IsQueryBounded program n) (s : σ) :
    IsQueryBounded ((interpret handler program).run s) (n * k) := by
  induction h generalizing s with
  | pure a n => exact .pure (a, s) _
  | liftBind q cont n _ ih =>
    change IsQueryBounded ((interpret handler (OracleComp.query q >>= cont)).run s) _
    simp only [interpret_bind, interpret_query, StateT.run_bind]
    rw [show (n + 1) * k = k + n * k by ring]
    exact (hhandler q s).bind fun result => ih result.1 result.2

/-- **Presampling a handler's randomness.** A handler that draws one sample per call from
`source` can instead read the samples from a list of independent draws, made in advance: for a
program making at most `n` calls, `n` presampled draws give the same law of the result and the
final state. -/
theorem IsQueryBounded.run_interpret_withSampleList {ι' σ γ V : Type} {spec' : ι' → Type}
    {program : OracleComp spec' γ} {n : ℕ} (h : IsQueryBounded program n) (source : PMF V)
    (fallback : V) (oracle : V → (q : ι') → StateT σ PMF (spec' q)) (s : σ) :
    ((Probability.PMF.iid source n).map List.ofFn).bind (fun values =>
      ((interpret (withSampleList fallback oracle) program).run (s, values)).map
        fun result => (result.1, result.2.1)) =
      (interpret (m := StateT σ PMF) (fun q state => source.bind fun value => oracle value q state)
        program).run s := by
  induction h generalizing s with
  | pure a n =>
    change ((Probability.PMF.iid source n).map List.ofFn).bind (fun values =>
      (PMF.pure (a, s, values)).map fun result => (result.1, result.2.1)) = PMF.pure (a, s)
    simp only [PMF.pure_map, PMF.bind_const]
  | liftBind q cont n _ ih =>
    change ((Probability.PMF.iid source (n + 1)).map List.ofFn).bind (fun values =>
      (((withSampleList fallback oracle q) (s, values)).bind fun result =>
        (interpret (withSampleList fallback oracle) (cont result.1)).run result.2).map
          fun result => (result.1, result.2.1)) =
      (source.bind fun value => oracle value q s).bind fun result =>
        (interpret (m := StateT σ PMF)
          (fun q state => source.bind fun value => oracle value q state) (cont result.1)).run
          result.2
    simp only [Probability.PMF.iid, withSampleList, Probability.PMF.monad_bind_eq_bind,
      PMF.monad_map_eq_map, PMF.map_bind, PMF.bind_bind, PMF.bind_map, PMF.map_comp,
      Function.comp_def, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.headD_cons,
      List.tail_cons]
    refine congrArg (source.bind ·) (funext fun value => ?_)
    rw [PMF.bind_comm]
    refine congrArg ((oracle value q s).bind ·) (funext fun result => ?_)
    rw [← ih result.1 result.2, PMF.bind_map]
    rfl

end Cslib.OracleComp
