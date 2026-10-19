/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Space
public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Logarithmic space

Space is upstream's measure: the number of distinct work-tape cells visited by the heads, summed
over the work tapes. The input is on a read-only tape and is not charged; nor is the write-only,
append-only output. A space bound applies to every computation prefix
(`Turing.MultiTapeNTM.RunsInSpace`). The logarithmic bounds are `c * (Nat.log2 n + 1)` on encoded
instances of length `n`, for a constant `c` [Sipser, Section 8.4][Sipser2013].

`Cslib.Complexity.L enc` consists of the problems decided by a Boolean function computable in
logarithmic space (`Turing.MultiTapeTM.ComputableInLogSpace`): one deterministic machine with a
binary alphabet and finitely many states halts on every encoded instance with output `[true]` or
`[false]` within logarithmic space. Any number of work tapes is allowed; definitions with one
work tape give the same class, since work tapes can be interleaved on one at a constant factor in
space (not formalized here). No time bound is imposed beyond halting; a polynomial one follows
(`Cslib.Complexity.L_subset_P`). Equivalently (`Cslib.Complexity.mem_L_iff`), the problem is
decidable within some time and space `c₁ * Nat.log2 n + c₂` in the sense of upstream
`Turing.MultiTapeTM.DecidableInTimeAndSpace`, the shape of the class `L = DSPACE(log₂)` of cslib
pull request #767 (open), whose classes are indexed by languages rather than encoded instances.

`Cslib.Complexity.NL enc` consists of the problems decided by one nondeterministic machine with a
binary alphabet and finitely many states within logarithmic space
(`Turing.MultiTapeNTM.DecidesInSpace`): every computation prefix on `enc a` stays within the bound,
and `a ∈ A` exactly when some computation path halts with output `[true]`. No time bound is
imposed, and branches need not halt.

`Cslib.Complexity.LogSpaceReducible encA encB A B` asks for a logspace function mapping instances
of `A` to instances of `B`, preserving membership [Sipser, Section 8.5][Sipser2013]. Logspace
reductions compose, and `L` is closed under them, because logspace functions compose without
storing intermediate values (`Turing.MultiTapeTM.ComputableInLogSpace.comp`).

## Main definitions

* `Cslib.Complexity.L`: deterministic logarithmic space.
* `Cslib.Complexity.NL`: nondeterministic logarithmic space.
* `Cslib.Complexity.LogSpaceReducible`: logspace many-one reductions.

## Main results

* `Cslib.Complexity.mem_L_iff`: `L` in terms of upstream `DecidableInTimeAndSpace`.
* `Cslib.Complexity.L_subset_NL`: a deterministic machine is a nondeterministic machine.
* `Cslib.Complexity.compl_mem_L`: `L` is closed under complement.
* `Cslib.Complexity.L_subset_P`: logarithmic space is within polynomial time.
* `Cslib.Complexity.L_subset_PSPACE`, `Cslib.Complexity.NL_subset_NPSPACE`: logarithmic space is
  within polynomial space.
* `Cslib.Complexity.LogSpaceReducible.refl`, `Cslib.Complexity.LogSpaceReducible.trans`:
  logspace reducibility is a preorder.
* `Cslib.Complexity.LogSpaceReducible.mem_L`: `L` is closed under logspace reductions.
* `Cslib.Complexity.LogSpaceReducible.compl`: reductions between complements.
* `Cslib.Complexity.LogSpaceReducible.polyTimeReducible`: logspace reductions are polynomial-time
  reductions.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Sections 8.4 and 8.5][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 4.3][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α β γ : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {A : Set α} {B : Set β} {C : Set γ}

/-- The problems decided in logarithmic space with respect to the encoding `enc`: a Boolean
function deciding membership is computable in logarithmic space. -/
def L (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f : α → Bool, ComputableInLogSpace f enc encBool ∧ ∀ a, a ∈ A ↔ f a = true}

/-- The problems decided by one nondeterministic machine within logarithmic space with respect to
the encoding `enc`: every computation prefix on `enc a` visits at most `c * (Nat.log2 n + 1)`
work-tape cells, where `n` is the length of `enc a`, and `a ∈ A` exactly when some computation path
halts with output `[true]`. -/
def NL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
    ntm.DecidesInSpace enc A fun a => c * (Nat.log2 (enc a).length + 1)}

/-- **Membership in `L`** is upstream decidability within some time and space
`c₁ * Nat.log2 n + c₂`, the shape of `DSPACE(log₂)` in cslib pull request #767. -/
theorem mem_L_iff : A ∈ L enc ↔ ∃ c₁ c₂ t,
    DecidableInTimeAndSpace A enc t fun a => c₁ * Nat.log2 (enc a).length + c₂ := by
  constructor
  · rintro ⟨f, ⟨t, c, hf⟩, hA⟩
    exact ⟨c, c, t, decidableInTimeAndSpace_iff.mpr
      ⟨f, hf.mono (fun _ => le_rfl) fun _ => by rw [Nat.mul_add, Nat.mul_one], hA⟩⟩
  · rintro ⟨c₁, c₂, t, h⟩
    obtain ⟨f, hf, hA⟩ := decidableInTimeAndSpace_iff.mp h
    refine ⟨f, ⟨t, c₁ + c₂, hf.mono (fun _ => le_rfl) fun a => ?_⟩, hA⟩
    nlinarith [Nat.zero_le (Nat.log2 (enc a).length)]

/-- **Deterministic logarithmic space is within nondeterministic logarithmic space**: a
deterministic machine is a nondeterministic one with one computation path. -/
theorem L_subset_NL : L enc ⊆ NL enc := by
  rintro A ⟨f, ⟨t, c, k, State, hfinite, tm, htm⟩, hA⟩
  refine ⟨k, State, hfinite, tm.toMultiTapeNTM, c, fun a => ?_⟩
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

/-- **`L` is closed under complement**: negate the decider, a composition of logspace
functions. -/
theorem compl_mem_L (h : A ∈ L enc) : Aᶜ ∈ L enc :=
  let ⟨f, hf, hA⟩ := h
  ⟨fun a => !f a, (ComputableInLogSpace.of_finite (encIn := encBool) not).comp hf,
    fun a => by simp [hA a]⟩

/-- **Logarithmic space is within polynomial time**: a deterministic machine that halts within
logarithmic space repeats no configuration it can read, of which there are polynomially many. -/
theorem L_subset_P : L enc ⊆ P enc := by
  rintro A ⟨f, hf, hA⟩
  exact ⟨f, hf.computableTidilyInPolyTime, hA⟩

/-- The logarithmic bounds are polynomially bounded. -/
private theorem polyBounded_log (c : ℕ) :
    PolyBounded (fun a => (enc a).length) fun a => c * (Nat.log2 (enc a).length + 1) :=
  .of_forall_le c 1 fun a => Nat.mul_le_mul_left c (by
    simpa using Nat.log2_le_self (enc a).length)

/-- **Deterministic logarithmic space is within polynomial space.** -/
theorem L_subset_PSPACE : L enc ⊆ PSPACE enc := by
  rintro A ⟨f, ⟨t, c, hf⟩, hA⟩
  exact ⟨f, ⟨t, _, polyBounded_log c, hf⟩, hA⟩

/-- **Nondeterministic logarithmic space is within nondeterministic polynomial space.** -/
theorem NL_subset_NPSPACE : NL enc ⊆ NPSPACE enc := by
  rintro A ⟨k, State, hfinite, ntm, c, h⟩
  exact ⟨k, State, hfinite, ntm, _, polyBounded_log c, h⟩

/-! ### Logspace reductions -/

/-- `A` reduces to `B` in logarithmic space: some `f`, computable in logarithmic space with
respect to `enc` and `encB`, satisfies `a ∈ A ↔ f a ∈ B`. -/
def LogSpaceReducible (enc : α ↪ List Bool) (encB : β ↪ List Bool) (A : Set α) (B : Set β) :
    Prop :=
  ∃ f : α → β, ComputableInLogSpace f enc encB ∧ ∀ a, a ∈ A ↔ f a ∈ B

/-- Every problem reduces to itself in logarithmic space. -/
theorem LogSpaceReducible.refl (enc : α ↪ List Bool) (A : Set α) : LogSpaceReducible enc enc A A :=
  ⟨fun a => a, .id, fun _ => Iff.rfl⟩

/-- **Logspace reductions compose.** -/
theorem LogSpaceReducible.trans (hAB : LogSpaceReducible enc encB A B)
    (hBC : LogSpaceReducible encB encC B C) : LogSpaceReducible enc encC A C :=
  let ⟨f, hf, hfAB⟩ := hAB
  let ⟨g, hg, hgBC⟩ := hBC
  ⟨g ∘ f, hg.comp hf, fun a => (hfAB a).trans (hgBC (f a))⟩

/-- **`L` is closed under logspace reductions.** -/
theorem LogSpaceReducible.mem_L (hAB : LogSpaceReducible enc encB A B) (hB : B ∈ L encB) :
    A ∈ L enc :=
  let ⟨f, hf, hfAB⟩ := hAB
  let ⟨g, hg, hgB⟩ := hB
  ⟨g ∘ f, hg.comp hf, fun a => (hfAB a).trans (hgB (f a))⟩

/-- A logspace reduction between problems is one between their complements. -/
theorem LogSpaceReducible.compl (h : LogSpaceReducible enc encB A B) :
    LogSpaceReducible enc encB Aᶜ Bᶜ :=
  let ⟨f, hf, hfAB⟩ := h
  ⟨f, hf, fun a => not_congr (hfAB a)⟩

/-- **Logspace reductions are polynomial-time reductions.** -/
theorem LogSpaceReducible.polyTimeReducible (h : LogSpaceReducible enc encB A B) :
    PolyTimeReducible enc encB A B :=
  let ⟨f, hf, hfAB⟩ := h
  ⟨f, hf.computableTidilyInPolyTime, hfAB⟩

end Cslib.Complexity
