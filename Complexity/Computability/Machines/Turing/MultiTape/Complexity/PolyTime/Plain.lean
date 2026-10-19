/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (after crei/tidy-universal lands)

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
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

end Turing.MultiTapeTM
