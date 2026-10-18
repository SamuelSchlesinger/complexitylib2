/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Nondeterministic

/-!
# Deciding problems with nondeterministic machines

A nondeterministic machine accepts an input when some computation path ends halted with output
`[true]`, the encoding `Turing.MultiTapeTM.encBool true` used by verifiers and deterministic
deciders. Paths that halt with another output, and paths ending in a stuck configuration, do not
accept. A machine decides `A` in time `t` [Arora and Barak, Definition 2.5][AroraBarak09] when
on every encoded instance `enc a`, every computation path of at least `t a` steps ends halted, and
`a ∈ A` exactly when some computation path on `enc a` accepts. The time bound applies to every
branch, including rejecting ones.

A transition relation may be empty at a running configuration. Upstream's
`Turing.MultiTapeNTM.RunsInTime` therefore permits a computation path that ends stuck before the
time bound; such a path neither halts nor accepts. When no configuration is stuck, every
computation path within the bound extends to a halted one of exactly the bound
(`Turing.MultiTapeNTM.ComputationPath.exists_halted_extension`).

`Turing.MultiTapeNTM.DecidableInPolyTime` asks for one machine with a binary alphabet and finitely
many states, and one polynomially bounded time bound, for all instances. Problems in the
verifier class `Cslib.Complexity.NP` have such machines
(`Cslib.Complexity.decidableInPolyTime_of_mem_NP`); the converse is not proved here.

## Main definitions

* `Turing.MultiTapeNTM.Accepts`: some computation path halts with output `[true]`.
* `Turing.MultiTapeNTM.DecidesInTime`: a machine decides a problem within a time bound.
* `Turing.MultiTapeNTM.DecidableInTime`, `Turing.MultiTapeNTM.DecidableInPolyTime`: some finite
  binary machine decides a problem within a time bound, or within a polynomial time bound.

## Main results

* `Turing.MultiTapeNTM.RunPath.exists_extend_of_halted`: a halted path extends to any length.
* `Turing.MultiTapeNTM.accepts_iff_exists_time_eq`: under a time bound `t`, acceptance is
  witnessed by a computation path of exactly `t` steps.
* `Turing.MultiTapeNTM.ComputationPath.exists_halted_extension`: without stuck configurations,
  every computation path within a time bound is a prefix of a halted one.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeNTM

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol} {ntm : MultiTapeNTM k Symbol State}

/-- A run path that ends halted extends to any longer length, by steps of its halted last
configuration to itself. -/
theorem RunPath.exists_extend_of_halted (p : ntm.RunPath input) (h : p.last.Halted) {n : ℕ}
    (hn : p.length ≤ n) :
    ∃ q : ntm.RunPath input, q.head = p.head ∧ q.length = n ∧ q.last = p.last := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction m with
  | zero => exact ⟨p, rfl, rfl, rfl⟩
  | succ m ih =>
    obtain ⟨q, hhead, hlen, hlast⟩ := ih (Nat.le_add_right _ _)
    have hstep : ntm.Step q.last q.last := (step_of_halt (hlast ▸ h)).mpr rfl
    exact ⟨q.snoc q.last hstep, by simpa using hhead, by simp [hlen]; rfl, by simpa using hlast⟩

/-- Under a time bound `t`, every computation path that ends halted has the same last
configuration as a computation path of exactly `t` steps. -/
theorem exists_time_eq_of_runsInTime {t : ℕ} (ht : ntm.RunsInTime input t)
    (p : ntm.ComputationPath input) (hp : p.last.Halted) :
    ∃ q : ntm.ComputationPath input, q.time = t ∧ q.last = p.last := by
  rcases le_or_gt t p.time with hle | hlt
  · -- cut the path after `t` steps; it has halted there
    have hlt : t < p.length + 1 := Nat.lt_succ_of_le hle
    let q : ntm.ComputationPath input :=
      ⟨p.toRunPath.take ⟨t, hlt⟩, by rw [RelSeries.head_take]; exact p.head_eq⟩
    have hq : q.last.Halted := ht q (by simp [q, ComputationPath.time, RunPath.time])
    refine ⟨q, by simp [q, ComputationPath.time, RunPath.time], ?_⟩
    have hlast : q.last = p.toRunPath ⟨t, hlt⟩ := RelSeries.last_take _ _
    exact hlast.trans (RunPath.last_eq_of_halted p.toRunPath _ (hlast ▸ hq)).symm
  · obtain ⟨q, hhead, hlen, hlast⟩ := RunPath.exists_extend_of_halted p.toRunPath hp hlt.le
    exact ⟨⟨q, hhead.trans p.head_eq⟩, hlen, hlast⟩

/-- Without stuck configurations, every run path extends to any longer length, as a prefix. -/
theorem RunPath.exists_extend (htotal : ∀ c : Cfg k Symbol State input, ∃ c', ntm.Step c c')
    (p : ntm.RunPath input) {n : ℕ} (hn : p.length ≤ n) :
    ∃ (q : ntm.RunPath input) (hq : q.length = n),
      ∀ i (hi : i < p.length + 1), q ⟨i, by omega⟩ = p ⟨i, hi⟩ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction m with
  | zero => exact ⟨p, rfl, fun _ _ => rfl⟩
  | succ m ih =>
    obtain ⟨q, hlen, hprefix⟩ := ih (Nat.le_add_right _ _)
    obtain ⟨c, hc⟩ := htotal q.last
    refine ⟨q.snoc c hc, by simp [hlen]; rfl, fun i hi => ?_⟩
    rw [← hprefix i hi]
    have hi' : i < q.length + 1 := by omega
    exact (congrArg (q.snoc c hc) (Fin.ext rfl)).trans (RelSeries.snoc_castSucc q c hc ⟨i, hi'⟩)

/-- **Actual halting.** Without stuck configurations, every computation path within a time bound
`t` is a prefix of a computation path of exactly `t` steps, which has halted. -/
theorem ComputationPath.exists_halted_extension
    (htotal : ∀ c : Cfg k Symbol State input, ∃ c', ntm.Step c c') {t : ℕ}
    (ht : ntm.RunsInTime input t) (p : ntm.ComputationPath input) (hp : p.time ≤ t) :
    ∃ (q : ntm.ComputationPath input) (hq : q.time = t), q.last.Halted ∧
      ∀ i (hi : i < p.length + 1),
        q.toRunPath ⟨i, by unfold time RunPath.time at hp hq; omega⟩ = p.toRunPath ⟨i, hi⟩ := by
  obtain ⟨q, hlen, hprefix⟩ := RunPath.exists_extend htotal p.toRunPath hp
  have hhead : q.head = ntm.initCfg input := by
    rw [← p.head_eq]
    exact hprefix 0 (Nat.succ_pos _)
  let q' : ntm.ComputationPath input := ⟨q, hhead⟩
  exact ⟨q', hlen, ht q' hlen.ge, hprefix⟩

/-- The machine accepts `input` when some computation path ends halted with output `[true]`. -/
def Accepts (ntm : MultiTapeNTM k Bool State) (input : List Bool) : Prop :=
  ∃ p : ntm.ComputationPath input, p.last.Halted ∧ p.last.output = [true]

/-- Under a time bound `t`, a machine accepts exactly when some computation path of exactly `t`
steps ends with output `[true]`; such a path has halted. -/
theorem accepts_iff_exists_time_eq {ntm : MultiTapeNTM k Bool State} {input : List Bool} {t : ℕ}
    (ht : ntm.RunsInTime input t) :
    ntm.Accepts input ↔ ∃ p : ntm.ComputationPath input, p.time = t ∧ p.last.output = [true] := by
  constructor
  · rintro ⟨p, hhalt, hout⟩
    obtain ⟨q, hq, hlast⟩ := exists_time_eq_of_runsInTime ht p hhalt
    exact ⟨q, hq, hlast ▸ hout⟩
  · rintro ⟨p, hp, hout⟩
    exact ⟨p, ht p hp.ge, hout⟩

variable {α : Type*}

/-- `ntm` decides `A` within `t` relative to the encoding `enc`: on every encoded instance `enc a`,
every computation path of at least `t a` steps ends halted, and `a ∈ A` exactly when some
computation path accepts. A computation path may also end stuck before `t a` steps; it does not
accept. -/
def DecidesInTime (ntm : MultiTapeNTM k Bool State) (enc : α ↪ List Bool) (A : Set α)
    (t : α → ℕ) : Prop :=
  ∀ a, ntm.RunsInTime (enc a) (t a) ∧ (a ∈ A ↔ ntm.Accepts (enc a))

/-- Some nondeterministic machine with a binary alphabet and finitely many states decides `A`
within `t`. -/
def DecidableInTime (A : Set α) (enc : α ↪ List Bool) (t : α → ℕ) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State),
    ntm.DecidesInTime enc A t

/-- Some nondeterministic machine with a binary alphabet and finitely many states decides `A`
within a time bound polynomial in the length of the encoded instance. -/
def DecidableInPolyTime (A : Set α) (enc : α ↪ List Bool) : Prop :=
  ∃ t, MultiTapeTM.PolyBounded (fun a => (enc a).length) t ∧ DecidableInTime A enc t

/-- Time bounds can be increased. -/
theorem DecidesInTime.mono {ntm : MultiTapeNTM k Bool State} {enc : α ↪ List Bool} {A : Set α}
    {t t' : α → ℕ} (h : ntm.DecidesInTime enc A t) (ht : ∀ a, t a ≤ t' a) :
    ntm.DecidesInTime enc A t' :=
  fun a => ⟨(h a).1.mono (ht a), (h a).2⟩

end Turing.MultiTapeNTM
