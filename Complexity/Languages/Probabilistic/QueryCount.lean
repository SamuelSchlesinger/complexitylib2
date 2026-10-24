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

`OracleComp.IsCostBounded cost program n` says that the calls of `program` cost at most `n` in
total on every path through its tree of calls, whatever the answers, where a call `q` costs
`cost q`. With unit costs this is `OracleComp.IsQueryBounded program n`: at most `n` calls on every
path. Other costs count calls of one kind only, such as the signing calls of a forger. Budgets are
preserved by sequencing (`IsCostBounded.bind`), add over costs (`IsCostBounded.add`) and are proved
by induction on the program. A call budget gives the semantic, handler-quantified bound
`ProbOracleComp.HasQueryBounds` for the program's external calls
(`IsQueryBounded.hasQueryBounds`), and running a program through a handler whose calls make at
most `cost q` calls gives a call budget (`IsCostBounded.run_interpret`).

A budget also justifies presampling: a handler that draws one sample per call can read its
samples from a list of independent draws made in advance, with the same law of the result and the
final state (`IsQueryBounded.run_interpret_withSampleList`).

## Main definitions

* `Cslib.OracleComp.IsCostBounded`: calls costing at most `n` on every path.
* `Cslib.OracleComp.IsQueryBounded`: at most `n` calls on every path.

## Main results

* `Cslib.OracleComp.IsCostBounded.bind`: budgets add under sequencing.
* `Cslib.OracleComp.IsCostBounded.add`: budgets for two costs give a budget for their sum.
* `Cslib.OracleComp.IsCostBounded.run_interpret`: the call budget of a program run through a
  handler.
* `Cslib.OracleComp.IsQueryBounded.hasQueryBounds`: the semantic external call bound.
* `Cslib.OracleComp.IsQueryBounded.run_interpret_withSampleList`: presampling a handler's draws.
-/

@[expose] public section

namespace Cslib.OracleComp

universe u v

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {α β : Type v}

/-- The calls of the program cost at most `n` in total on every path, whatever the answers, where
a call `q` costs `cost q`. -/
inductive IsCostBounded (cost : ι → ℕ) : OracleComp spec α → ℕ → Prop
  /-- Returning a value makes no call. -/
  | pure (a : α) (n : ℕ) : IsCostBounded cost (PFunctor.FreeM.pure a) n
  /-- A call followed by continuations whose calls each cost at most `n`. -/
  | liftBind (q : ι) (cont : spec q → OracleComp spec α) (n : ℕ)
      (hcont : ∀ a, IsCostBounded cost (cont a) n) :
      IsCostBounded cost (PFunctor.FreeM.liftBind q cont) (n + cost q)

/-- The program makes at most `n` oracle calls on every path, whatever the answers. -/
abbrev IsQueryBounded (program : OracleComp spec α) (n : ℕ) : Prop :=
  IsCostBounded (fun _ => 1) program n

namespace IsCostBounded

variable {cost : ι → ℕ}

/-- A larger budget is still a budget. -/
theorem mono {program : OracleComp spec α} {n m : ℕ} (h : IsCostBounded cost program n)
    (hnm : n ≤ m) : IsCostBounded cost program m := by
  induction h generalizing m with
  | pure a n => exact .pure a m
  | liftBind q cont n _ ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + cost q := ⟨m - cost q, by omega⟩
    exact .liftBind q cont m fun a => ih a (by omega)

/-- A budget for a call's continuations, from a budget for the call. -/
theorem liftBind_iff {q : ι} {cont : spec q → OracleComp spec α} {n : ℕ} :
    IsCostBounded cost (PFunctor.FreeM.liftBind q cont) n ↔
      cost q ≤ n ∧ ∀ a, IsCostBounded cost (cont a) (n - cost q) := by
  constructor
  · rintro (_ | ⟨_, _, n, hcont⟩)
    exact ⟨by omega, fun a => by rw [Nat.add_sub_cancel]; exact hcont a⟩
  · rintro ⟨hle, hcont⟩
    rw [show n = n - cost q + cost q by omega]
    exact .liftBind q cont _ hcont

/-- One call costs its cost. -/
theorem query (q : ι) : IsCostBounded cost (OracleComp.query (spec := spec) q) (cost q) := by
  have h := IsCostBounded.liftBind (spec := spec) (cost := cost) q
    (fun a : spec q => PFunctor.FreeM.pure a) 0 fun a => .pure a 0
  rw [Nat.zero_add] at h
  exact h

/-- Budgets add under sequencing. -/
theorem bind {program : OracleComp spec α} {next : α → OracleComp spec β} {n m : ℕ}
    (h : IsCostBounded cost program n) (hnext : ∀ a, IsCostBounded cost (next a) m) :
    IsCostBounded cost (program >>= next) (n + m) := by
  induction h with
  | pure a n => exact (hnext a).mono (by omega)
  | liftBind q cont n _ ih =>
    rw [show n + cost q + m = n + m + cost q by omega]
    exact .liftBind q _ (n + m) ih

/-- A budget for a cost is one for every smaller cost. -/
theorem of_le {cost' : ι → ℕ} {program : OracleComp spec α} {n : ℕ}
    (h : IsCostBounded cost program n) (hcost : ∀ q, cost' q ≤ cost q) :
    IsCostBounded cost' program n := by
  induction h with
  | pure a n => exact .pure a n
  | liftBind q cont n _ ih => exact (IsCostBounded.liftBind q cont n ih).mono (by simp [hcost q])

/-- Budgets for two costs give a budget for their sum. -/
theorem add {cost' : ι → ℕ} {program : OracleComp spec α} {n n' : ℕ}
    (h : IsCostBounded cost program n) (h' : IsCostBounded cost' program n') :
    IsCostBounded (fun q => cost q + cost' q) program (n + n') := by
  induction h generalizing n' with
  | pure a n => exact .pure a _
  | liftBind q cont n _ ih =>
    obtain ⟨hle, hcont⟩ := liftBind_iff.mp h'
    rw [show n + cost q + n' = n + (n' - cost' q) + (cost q + cost' q) by omega]
    exact .liftBind q cont _ fun a => ih a (hcont a)

/-- A program run through a stateful handler, each of whose calls `q` makes at most `cost q`
calls to the target oracle, makes at most `n` target calls when its own calls cost at most
`n`. -/
theorem run_interpret {κ : Type u} {target : OracleSpec.{u, v} κ} {σ : Type v}
    {handler : (q : ι) → StateT σ (OracleComp target) (spec q)}
    (hhandler : ∀ q s, IsQueryBounded ((handler q).run s) (cost q)) {program : OracleComp spec α}
    {n : ℕ} (h : IsCostBounded cost program n) (s : σ) :
    IsQueryBounded ((interpret handler program).run s) n := by
  induction h generalizing s with
  | pure a n => exact .pure (a, s) _
  | liftBind q cont n _ ih =>
    change IsQueryBounded ((interpret handler (OracleComp.query q >>= cont)).run s) _
    simp only [interpret_bind, interpret_query, StateT.run_bind]
    rw [Nat.add_comm]
    exact (hhandler q s).bind fun result => ih result.1 result.2

end IsCostBounded

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
