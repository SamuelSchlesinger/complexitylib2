/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (after crei/tidy-universal lands)

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# Polynomial time on plain machines

`Turing.MultiTapeTM.ComputableTidilyInPolyTime` asks for a *tidy* machine, which clears its work
tapes and rewinds its heads before halting, within polynomially bounded time and space. Neither
requirement changes the class. A machine that halts within `t` steps visits at most `k t + k`
work-tape cells, where `k` is its number of work tapes
(`Turing.MultiTapeTM.ComputesInTimeAndSpace.space_linear`), and the tidy normal form makes any
machine tidy at a linear cost in time and space
(`Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace`). So a function
is tidily computable in polynomial time exactly when some machine computes it in the sense of
upstream `Turing.MultiTapeTM.ComputableInTimeAndSpace`, within polynomially bounded time and space
(`Turing.MultiTapeTM.computableTidilyInPolyTime_iff_exists_computableInTimeAndSpaceOfLength`), and
a polynomial time bound alone already suffices
(`Turing.MultiTapeTM.ComputableInTimeAndSpace.computableTidilyInPolyTime`)
[Arora and Barak, Chapter 1][AroraBarak09].

Passing from tidy to plain computations is lossless: a tidy machine is a machine, with the same
bounds. Passing from plain to tidy computations changes the bounds by linear functions whose
coefficients depend on the machine.

The plain notion, `Turing.MultiTapeTM.ComputableInPolyTime`, is the one for definitions and public
statements; the tidy notion is a proof device. Proofs switch between them with
`Turing.MultiTapeTM.ComputableInPolyTime.tidy` and
`Turing.MultiTapeTM.ComputableInPolyTime.of_tidy`.
The closure rules of the plain notion are proved through the tidy calculus and registered with
`fun_prop`, together with the transition from tidy to plain computability, so `fun_prop` proves a
plain goal from plain hypotheses and from any tidy certificate.

Upstream `Turing.MultiTapeTM.DecidableInTimeAndSpace` decides a problem through its Boolean
indicator. `Turing.MultiTapeTM.decidableInTimeAndSpace_iff` restates it for any Boolean function
deciding membership, the form used by the classes in `Cslib.Complexity`.

## Main results

* `Turing.MultiTapeTM.ComputesInTimeAndSpace.space_linear`,
  `Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_space_linear`: time bounds space.
* `Turing.MultiTapeTM.decidableInTimeAndSpace_iff`: decidability through any Boolean decider.
* `Turing.MultiTapeTM.ComputableInTimeAndSpace.computableTidilyInPolyTime`: a polynomial time
  bound for any machine, with any space bound, gives tidy polynomial time.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.exists_computableInTimeAndSpaceOfLength`: tidy
  polynomial time gives a machine within polynomially bounded time and space.
* `Turing.MultiTapeTM.computableTidilyInPolyTime_iff_exists_computableInTimeAndSpaceOfLength`: the
  two notions agree.
* `Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime`: the same statement for
  `Turing.MultiTapeTM.ComputableInPolyTime`, with the shortcuts
  `Turing.MultiTapeTM.ComputableInPolyTime.tidy`, `Turing.MultiTapeTM.ComputableInPolyTime.of_tidy`
  and `Turing.MultiTapeTM.ComputableTidilyInPolyTime.computableInPolyTime`.
* `Turing.MultiTapeTM.ComputableInTimeAndSpace.computableInPolyTime`: a polynomial time bound for
  any machine, with any space bound, gives polynomial time.
* `Turing.MultiTapeTM.ComputableInPolyTime.comp`, `.pair`, `.ite'`, `.fst`, `.snd`: closure rules.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Cslib

-- upstream: candidate (addition to `Machines/Turing/MultiTape/Deterministic.lean`)

/-! ### Time bounds space -/

section Machine

variable {k : ℕ} {Symbol State : Type*} {tm : MultiTapeTM k Symbol State}

/-- A computation within `t` steps needs no separate space bound: it visits at most `k t + k`
work-tape cells. -/
theorem ComputesInTimeAndSpace.space_linear {input output : List Symbol} {t s : ℕ}
    (h : tm.ComputesInTimeAndSpace input output t s) :
    tm.ComputesInTimeAndSpace input output t (k * t + k) :=
  ⟨h.1, h.2.1, runsInSpace_of_halted (runsInTime_iff_halted.mp h.2.1) (tm.space_linear _ t)⟩

end Machine

variable {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

/-- A function computable within time `t` is computable within time `t` and space `c t + c`, for
a constant `c`: the number of work tapes of the machine. -/
theorem ComputableInTimeAndSpace.exists_space_linear {t s : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s) :
    ∃ c, ComputableInTimeAndSpace f encIn encOut t fun a => c * t a + c :=
  let ⟨k, State, hfinite, tm, htm⟩ := h
  ⟨k, k, State, hfinite, tm, fun a => (htm a).space_linear⟩

/-- The indicator of `A` is the Boolean function that is `true` exactly on `A`. -/
theorem indicator_eq_iff {A : Set α} {g : α → Bool} :
    indicator A = g ↔ ∀ a, a ∈ A ↔ g a = true := by
  refine ⟨fun h a => ?_, fun h => funext fun a => ?_⟩
  · subst h
    by_cases ha : a ∈ A <;> simp [indicator, ha]
  · rcases hg : g a <;> simp [indicator, h a, hg]

-- upstream: candidate (after crei/tidy-universal lands)

/-! ### Decidability through a Boolean decider -/

/-- A problem is decidable within given bounds exactly when some Boolean function deciding
membership is computable within them, with answers encoded by `encBool`. -/
theorem decidableInTimeAndSpace_iff {A : Set α} {enc : α ↪ List Bool} {t s : α → ℕ} :
    DecidableInTimeAndSpace A enc t s ↔
      ∃ g : α → Bool, ComputableInTimeAndSpace g enc encBool t s ∧ ∀ a, a ∈ A ↔ g a = true := by
  refine ⟨fun h => ⟨indicator A, h, indicator_eq_iff.mp rfl⟩, fun ⟨g, hg, hA⟩ => ?_⟩
  rw [DecidableInTimeAndSpace, indicator_eq_iff.mpr hA]
  exact hg

/-! ### Tidy and plain polynomial time -/

/-- **Plain polynomial time is tidy polynomial time.** A function computable by some machine
within a time bound polynomial in the length of the encoded input, with any space bound, is
tidily computable in polynomial time. -/
theorem ComputableInTimeAndSpace.computableTidilyInPolyTime {t : ℕ → ℕ} {s : α → ℕ}
    (ht : PolynomiallyBounded t)
    (h : ComputableInTimeAndSpace f encIn encOut (fun a => t (encIn a).length) s) :
    ComputableTidilyInPolyTime f encIn encOut := by
  obtain ⟨c, h⟩ := h.exists_space_linear
  obtain ⟨d, h⟩ := h.exists_computableTidilyInTimeAndSpace
  exact ⟨_, _,
    PolyBounded.of_polynomiallyBounded (fun a => (encIn a).length)
      (bound := fun n => 2 * t n + 3 * (c * t n + c) + d) (by fun_prop),
    PolyBounded.of_polynomiallyBounded (fun a => (encIn a).length)
      (bound := fun n => d * (c * t n + c + 1)) (by fun_prop), h⟩

/-- Tidy polynomial time gives a machine computing the function within polynomially bounded time
and space. The machine and its bounds are those of the tidy computation. -/
theorem ComputableTidilyInPolyTime.exists_computableInTimeAndSpaceOfLength
    (h : ComputableTidilyInPolyTime f encIn encOut) :
    ∃ t s : ℕ → ℕ, PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
      ComputableInTimeAndSpaceOfLength f encIn encOut t s :=
  let ⟨_, _, ⟨t, ht, htb⟩, ⟨s, hs, hsb⟩, h⟩ := h
  ⟨t, s, ht, hs, (h.mono htb hsb).computableInTimeAndSpace⟩

/-- **Tidy polynomial time is plain polynomial time:** `f` is tidily computable in polynomial time
exactly when some machine with a binary alphabet and finitely many states computes it within time
and space bounded by polynomially bounded functions of the length of the encoded input. -/
theorem computableTidilyInPolyTime_iff_exists_computableInTimeAndSpaceOfLength :
    ComputableTidilyInPolyTime f encIn encOut ↔ ∃ t s : ℕ → ℕ, PolynomiallyBounded t ∧
      PolynomiallyBounded s ∧ ComputableInTimeAndSpaceOfLength f encIn encOut t s :=
  ⟨ComputableTidilyInPolyTime.exists_computableInTimeAndSpaceOfLength,
    fun ⟨_, _, ht, _, h⟩ => h.computableTidilyInPolyTime ht⟩

/-! ### Bridges to `ComputableInPolyTime` -/

/-- **Plain and tidy polynomial time agree.** `Turing.MultiTapeTM.ComputableInPolyTime` unfolds to
the right-hand side of
`Turing.MultiTapeTM.computableTidilyInPolyTime_iff_exists_computableInTimeAndSpaceOfLength`. -/
theorem computableInPolyTime_iff_computableTidilyInPolyTime :
    ComputableInPolyTime f encIn encOut ↔ ComputableTidilyInPolyTime f encIn encOut :=
  computableTidilyInPolyTime_iff_exists_computableInTimeAndSpaceOfLength.symm

/-- A function computable in polynomial time is tidily computable in polynomial time. The tidy
machine adds linear overhead to both bounds. -/
theorem ComputableInPolyTime.tidy (h : ComputableInPolyTime f encIn encOut) :
    ComputableTidilyInPolyTime f encIn encOut :=
  computableInPolyTime_iff_computableTidilyInPolyTime.mp h

/-- A function tidily computable in polynomial time is computable in polynomial time, by the same
machine within the same bounds. -/
theorem ComputableInPolyTime.of_tidy (h : ComputableTidilyInPolyTime f encIn encOut) :
    ComputableInPolyTime f encIn encOut :=
  h.exists_computableInTimeAndSpaceOfLength

/-- `Turing.MultiTapeTM.ComputableInPolyTime.of_tidy` for dot notation on a tidy hypothesis. It is
a `fun_prop` transition rule, so every tidy certificate also proves plain goals. -/
@[fun_prop]
theorem ComputableTidilyInPolyTime.computableInPolyTime
    (h : ComputableTidilyInPolyTime f encIn encOut) : ComputableInPolyTime f encIn encOut :=
  .of_tidy h

/-- **A polynomial time bound alone suffices.** A function computable by some machine within a time
bound polynomial in the length of the encoded input, with any space bound, is computable in
polynomial time: within `t` steps the machine visits at most `c t + c` work-tape cells. -/
theorem ComputableInTimeAndSpace.computableInPolyTime {t : ℕ → ℕ} {s : α → ℕ}
    (ht : PolynomiallyBounded t)
    (h : ComputableInTimeAndSpace f encIn encOut (fun a => t (encIn a).length) s) :
    ComputableInPolyTime f encIn encOut :=
  let ⟨c, h⟩ := h.exists_space_linear
  ⟨t, fun n => c * t n + c, ht, by fun_prop, h⟩

end Turing.MultiTapeTM

/-! ### Closure of `ComputableInPolyTime`

The rules that need a machine construction, proved through the tidy calculus. Together with
`Turing.MultiTapeTM.ComputableTidilyInPolyTime.computableInPolyTime` they make `fun_prop` prove
plain goals from plain hypotheses and tidy certificates. -/

namespace Turing.MultiTapeTM.ComputableInPolyTime

universe u

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- The encoded value of a function computable in polynomial time has polynomial length. -/
theorem polyBounded_length {f : α → β} (h : ComputableInPolyTime f encIn encMid) :
    PolyBounded (fun a => (encIn a).length) fun a => (encMid (f a)).length :=
  h.tidy.polyBounded_length

theorem comp {f : β → γ} {g : α → β} (hf : ComputableInPolyTime f encMid encOut)
    (hg : ComputableInPolyTime g encIn encMid) : ComputableInPolyTime (f ∘ g) encIn encOut :=
  .of_tidy (hf.tidy.comp hg.tidy)

theorem pair {α β₁ β₂ : Type u} {encIn : α ↪ List Bool} {enc₁ : β₁ ↪ List Bool}
    {enc₂ : β₂ ↪ List Bool} {enc : β₁ × β₂ ↪ List Bool} [PairEncoding enc₁ enc₂ enc]
    {f : α → β₁} {g : α → β₂} (hf : ComputableInPolyTime f encIn enc₁)
    (hg : ComputableInPolyTime g encIn enc₂) :
    ComputableInPolyTime (fun x => (f x, g x)) encIn enc :=
  .of_tidy (hf.tidy.pair hg.tidy)

@[fun_prop]
theorem comp' {f : β → γ} {g : α → β} (hf : ComputableInPolyTime f encMid encOut)
    (hg : ComputableInPolyTime g encIn encMid) :
    ComputableInPolyTime (fun a => f (g a)) encIn encOut :=
  hf.comp hg

@[fun_prop]
theorem prod {α β₁ β₂ : Type u} {encIn : α ↪ List Bool} {enc₁ : β₁ ↪ List Bool}
    {enc₂ : β₂ ↪ List Bool} {f : α → β₁} {g : α → β₂} (hf : ComputableInPolyTime f encIn enc₁)
    (hg : ComputableInPolyTime g encIn enc₂) :
    ComputableInPolyTime (fun x => (f x, g x)) encIn (encPair enc₁ enc₂) :=
  hf.pair hg

@[fun_prop]
theorem fst {β₁ β₂ : Type u} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableInPolyTime (fun p : β₁ × β₂ => p.1) (encPair enc₁ enc₂) enc₁ :=
  .of_tidy (ComputableTidilyInPolyTime.fst enc₁ enc₂)

@[fun_prop]
theorem snd {β₁ β₂ : Type u} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableInPolyTime (fun p : β₁ × β₂ => p.2) (encPair enc₁ enc₂) enc₂ :=
  .of_tidy (ComputableTidilyInPolyTime.snd enc₁ enc₂)

/-- A case distinction between functions computable in polynomial time on all inputs. -/
@[fun_prop]
theorem ite' {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    (hc : ComputableInPolyTime c encIn encC) (hf : ComputableInPolyTime f encIn encMid)
    (hg : ComputableInPolyTime g encIn encMid) :
    ComputableInPolyTime (fun x => if c x then f x else g x) encIn encMid :=
  .of_tidy (hc.tidy.ite' hf.tidy hg.tidy)

end Turing.MultiTapeTM.ComputableInPolyTime
