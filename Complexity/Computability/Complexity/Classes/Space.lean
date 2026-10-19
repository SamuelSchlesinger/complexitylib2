/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Complexity.Reduction
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
with a binary alphabet and finitely many states within space `s`
(`Turing.MultiTapeNTM.DecidesInSpace`), for an `s` polynomially bounded in the length of `enc a`:
every computation path on `enc a` visits at most `s a` work-tape cells (upstream
`Turing.MultiTapeNTM.RunsInSpace`, over every prefix of every path), and `a ∈ A` exactly when
some computation path halts with output exactly `[true]` (`Turing.MultiTapeNTM.Accepts`). No
time bound is imposed: branches may run forever or end stuck, and neither accepts.

A problem is `PSPACE`-hard when every problem in `PSPACE`, with any encoding of its instances,
reduces to it in polynomial time (`Cslib.Complexity.PolyTimeReducible`), and `PSPACE`-complete
when it is moreover in `PSPACE` [Arora and Barak, Section 4.2][AroraBarak09]
[Sipser, Section 8.3][Sipser2013]. The true quantified Boolean formulas are `PSPACE`-complete;
see `Complexity.Computability.Complexity.Classes.Space.TQBF`.

Space counts visited work-tape cells, as upstream does: the input tape is read-only and the output
tape write-only [Sipser, Section 8.0][Sipser2013].

## Main definitions

* `Cslib.Complexity.PSPACE`: deterministic polynomial space.
* `Cslib.Complexity.NPSPACE`: nondeterministic polynomial space.
* `Cslib.Complexity.PSPACEHard`, `Cslib.Complexity.PSPACEComplete`: hardness and completeness
  under polynomial-time reductions.

## Main results

* `Cslib.Complexity.mem_PSPACE_iff`: `PSPACE` in terms of upstream `DecidableInTimeAndSpace`.
* `Cslib.Complexity.P_subset_PSPACE`: polynomial time is within polynomial space.
* `Cslib.Complexity.PSPACE_subset_NPSPACE`: a deterministic machine is a nondeterministic machine
  with one computation path.
* `Cslib.Complexity.PSPACEHard.trans`: hardness transfers along polynomial-time reductions.

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
the encoding `enc` (`Turing.MultiTapeNTM.DecidesInSpace`): every computation path on `enc a`
visits at most `s a` work-tape cells, for a polynomially bounded `s`, and `a ∈ A` exactly when
some computation path halts with output `[true]`. -/
def NPSPACE (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State)
    (s : α → ℕ), PolyBounded (fun a => (enc a).length) s ∧ ntm.DecidesInSpace enc A s}

/-- **Polynomial time is within polynomial space.** -/
theorem P_subset_PSPACE : P enc ⊆ PSPACE enc := by
  rintro A ⟨f, ⟨t, s, -, hs, hf⟩, hA⟩
  exact ⟨f, ⟨t, s, hs, hf.computableInTimeAndSpace⟩, hA⟩

/-- **A deterministic polynomial-space machine is a nondeterministic one**, with one computation
path (`Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_decidesInSpace`). -/
theorem PSPACE_subset_NPSPACE : PSPACE enc ⊆ NPSPACE enc := by
  rintro A ⟨f, ⟨t, s, hs, hf⟩, hA⟩
  obtain ⟨k, State, hfinite, ntm, h⟩ := hf.exists_decidesInSpace hA
  exact ⟨k, State, hfinite, ntm, s, hs, h⟩

/-! ### Hardness and completeness -/

/-- Every problem in `PSPACE`, with any encoding of its instances, reduces to `B` in polynomial
time. -/
def PSPACEHard {β : Type*} (encB : β ↪ List Bool) (B : Set β) : Prop :=
  ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α), A ∈ PSPACE enc → PolyTimeReducible enc encB A B

/-- `B` is in `PSPACE` and every problem in `PSPACE` reduces to it. -/
def PSPACEComplete {β : Type} (encB : β ↪ List Bool) (B : Set β) : Prop :=
  B ∈ PSPACE encB ∧ PSPACEHard encB B

/-- `PSPACE`-hardness transfers along a polynomial-time reduction. -/
theorem PSPACEHard.trans {β γ : Type*} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {B : Set β} {C : Set γ} (hB : PSPACEHard encB B) (hBC : PolyTimeReducible encB encC B C) :
    PSPACEHard encC C :=
  fun enc A hA => (hB enc A hA).trans hBC

end Cslib.Complexity
