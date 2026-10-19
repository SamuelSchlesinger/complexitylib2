/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Nondeterministic

/-!
# Polynomial space

`Cslib.Complexity.PSPACE enc` consists of the problems decided by one deterministic machine with a
binary alphabet and finitely many states that halts on every encoded instance `enc a` with output
`[true]` or `[false]`, visiting at most `s a` work-tape cells for an `s` polynomially bounded in
the length of `enc a` (upstream `Turing.MultiTapeTM.ComputableInTimeAndSpace`, with no tidiness
requirement). No bound on the time is imposed beyond halting. Equivalently
(`Cslib.Complexity.mem_PSPACE_iff`), the problem is decidable within some time bound and such a
space bound in the sense of upstream `Turing.MultiTapeTM.DecidableInTimeAndSpace`. The proposed
upstream complexity classes (cslib pull request #767, open) build `DSPACE` on the same notion of
decidability and define `PSPACE` as the union of the classes of space `O(n ^ k)`; their bounds
are functions of the input length, and that comparison is not formalized here.

`Cslib.Complexity.NPSPACE enc` consists of the problems decided by one nondeterministic machine
with a binary alphabet and finitely many states, every computation path of which on `enc a` visits
at most `s a` work-tape cells, for an `s` polynomially bounded in the length of `enc a` (upstream
`Turing.MultiTapeNTM.RunsInSpace`, over every prefix of every path), with `a ∈ A` exactly when
some computation path halts with output exactly `[true]` (`Turing.MultiTapeNTM.Accepts`). No
time bound is imposed: branches may run forever or end stuck, and neither accepts.

Space counts visited work-tape cells, as upstream does: the input tape is read-only and the output
tape write-only [Sipser, Section 8.0][Sipser2013].

## Main definitions

* `Cslib.Complexity.PSPACE`: deterministic polynomial space.
* `Cslib.Complexity.NPSPACE`: nondeterministic polynomial space.

## Main results

* `Cslib.Complexity.mem_PSPACE_iff`: `PSPACE` in terms of upstream `DecidableInTimeAndSpace`.
* `Cslib.Complexity.P_subset_PSPACE`: polynomial time is within polynomial space.
* `Cslib.Complexity.PSPACE_subset_NPSPACE`: a deterministic machine is a nondeterministic machine
  with one computation path.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- The problems decided by one deterministic machine within polynomial space, with respect to
the encoding `enc`: a Boolean function deciding membership is computable (upstream
`Turing.MultiTapeTM.ComputableInTimeAndSpace`) within some time and within space polynomially
bounded in the length of the encoded instance. -/
def PSPACE (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f : α → Bool, (∃ t s, PolyBounded (fun a => (enc a).length) s ∧
    ComputableInTimeAndSpace f enc encBool t s) ∧ ∀ a, a ∈ A ↔ f a = true}

/-- Membership in `PSPACE` is upstream decidability within some time and polynomial space. -/
theorem mem_PSPACE_iff : A ∈ PSPACE enc ↔
    ∃ t s, PolyBounded (fun a => (enc a).length) s ∧ DecidableInTimeAndSpace A enc t s := by
  have hind : ∀ f : α → Bool, (∀ a, a ∈ A ↔ f a = true) → f = indicator A := fun f hf => by
    funext a
    rcases h : f a <;> simp [indicator, hf a, h]
  constructor
  · rintro ⟨f, ⟨t, s, hs, hf⟩, hA⟩
    obtain rfl := hind f hA
    exact ⟨t, s, hs, hf⟩
  · rintro ⟨t, s, hs, hA⟩
    exact ⟨indicator A, ⟨t, s, hs, hA⟩, fun a => by by_cases ha : a ∈ A <;> simp [indicator, ha]⟩

/-- The problems decided by one nondeterministic machine within polynomial space, with respect to
the encoding `enc`: every computation path on `enc a` visits at most `s a` work-tape cells, for a
polynomially bounded `s`, and `a ∈ A` exactly when some computation path halts with output
`[true]`. -/
def NPSPACE (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State)
    (s : α → ℕ), PolyBounded (fun a => (enc a).length) s ∧
      ∀ a, ntm.RunsInSpace (enc a) (s a) ∧ (a ∈ A ↔ ntm.Accepts (enc a))}

/-- **Polynomial time is within polynomial space.** -/
theorem P_subset_PSPACE : P enc ⊆ PSPACE enc := by
  rintro A ⟨f, ⟨t, s, -, hs, hf⟩, hA⟩
  exact ⟨f, ⟨t, s, hs, hf.computableInTimeAndSpace⟩, hA⟩

/-- **A deterministic polynomial-space machine is a nondeterministic one**, with one computation
path: its prefixes and its halted extensions visit no more cells than the run, and it accepts
exactly when it halts with output `[true]`. -/
theorem PSPACE_subset_NPSPACE : PSPACE enc ⊆ NPSPACE enc := by
  rintro A ⟨f, ⟨t, s, hs, k, State, hfinite, tm, htm⟩, hA⟩
  refine ⟨k, State, hfinite, tm.toMultiTapeNTM, s, hs, fun a => ?_⟩
  obtain ⟨⟨u, hhalt, hout⟩, -, hspace⟩ := htm a
  refine ⟨hspace, ?_⟩
  rw [hA a, MultiTapeNTM.accepts_iff_exists_time_eq (runsInTime_of_halted hhalt)]
  constructor
  · intro hf
    refine ⟨MultiTapeNTM.ComputationPath.ofDeterministic tm (enc a) u, rfl, ?_⟩
    rw [MultiTapeTM.computationPath_last_eq_runFrom]
    change (tm.runFrom _ u).output = _
    rw [hout, hf]
    rfl
  · rintro ⟨q, hq, hout'⟩
    rw [MultiTapeTM.computationPath_last_eq_runFrom, hq, hout] at hout'
    exact List.head_eq_of_cons_eq hout'

end Cslib.Complexity
