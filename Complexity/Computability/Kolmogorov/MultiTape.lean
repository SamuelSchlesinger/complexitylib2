/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Kolmogorov.Invariance
public import Complexity.Computability.Machines.Turing.MultiTape.Run
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id

/-!
# Description methods of multi-tape Turing machines

A deterministic multi-tape Turing machine over the binary alphabet is a description method: a
program is an input of the machine, the clock counts steps, and the output of a program is the
contents of the output tape once the machine has halted. Its complexity `C_tm(x)` is the length of
a shortest input on which `tm` computes `x`, and `C_tm^t(x)` that of a shortest input on which `tm`
computes `x` within `t` steps.

## Main definitions

* `Cslib.Kolmogorov.DescriptionMethod.ofMultiTapeTM`: the description method of a machine.
* `Cslib.Kolmogorov.DescriptionMethod.literalSimulation`: a machine computing the identity
  simulates the literal description method.

## Main results

* `Cslib.Kolmogorov.DescriptionMethod.ofMultiTapeTM_produces_iff`: a program describes `x`
  exactly when the machine computes `x` from it.
* `Cslib.Kolmogorov.DescriptionMethod.mem_ofMultiTapeTM_run_iff`: a program describes `x` within
  `t` steps exactly when the machine computes `x` from it and halts within `t` steps.
* `Cslib.Kolmogorov.DescriptionMethod.timeBoundedComplexity_ofMultiTapeTM_le`: an input from which
  the machine computes `x` within `t` steps bounds `C_tm^t(x)`.
* `Cslib.Kolmogorov.DescriptionMethod.exists_simulation_literal`: some machine simulates the
  literal description method.
-/

@[expose] public section

namespace Cslib.Kolmogorov.DescriptionMethod

open Turing

variable {k : ℕ} {State : Type*} (tm : MultiTapeTM k Bool State)

/-- The description method of a deterministic multi-tape Turing machine over the binary alphabet:
the program `p` is the input, and after `t` steps its output is the contents of the output tape if
the machine has halted. -/
noncomputable def ofMultiTapeTM : DescriptionMethod (List Bool) where
  run p t :=
    if (tm.runFrom (tm.initCfg p) t).Halted then some (tm.runFrom (tm.initCfg p) t).output
    else none
  run_mono {p t₁ t₂ x} h hx := by
    simp only [Option.mem_def, Option.ite_none_right_eq_some, Option.some.injEq] at hx ⊢
    rwa [tm.runFrom_eq_of_halt _ h hx.1]

variable {tm} {p x : List Bool} {t : ℕ}

theorem mem_ofMultiTapeTM_run_iff_halted :
    x ∈ (ofMultiTapeTM tm).run p t ↔
      (tm.runFrom (tm.initCfg p) t).Halted ∧ (tm.runFrom (tm.initCfg p) t).output = x := by
  simp only [ofMultiTapeTM, Option.mem_def, Option.ite_none_right_eq_some, Option.some.injEq]

/-- A program describes `x` exactly when the machine computes `x` from it. -/
@[simp]
theorem ofMultiTapeTM_produces_iff : (ofMultiTapeTM tm).Produces p x ↔ tm.Computes p x :=
  exists_congr fun _ => mem_ofMultiTapeTM_run_iff_halted

/-- A program describes `x` within `t` steps exactly when the machine computes `x` from it and
halts within `t` steps. -/
theorem mem_ofMultiTapeTM_run_iff :
    x ∈ (ofMultiTapeTM tm).run p t ↔ tm.RunsInTime p t ∧ tm.Computes p x := by
  constructor
  · intro h
    exact ⟨MultiTapeTM.runsInTime_iff_halted.mpr (mem_ofMultiTapeTM_run_iff_halted.mp h).1,
      ofMultiTapeTM_produces_iff.mp (.of_mem_run h)⟩
  · rintro ⟨ht, hx⟩
    have hmem : (tm.runFrom (tm.initCfg p) t).output ∈ (ofMultiTapeTM tm).run p t :=
      mem_ofMultiTapeTM_run_iff_halted.mpr ⟨MultiTapeTM.runsInTime_iff_halted.mp ht, rfl⟩
    rwa [(Produces.of_mem_run hmem).unique (ofMultiTapeTM_produces_iff.mpr hx)] at hmem

theorem complexity_ofMultiTapeTM_le (h : tm.Computes p x) :
    (ofMultiTapeTM tm).complexity x ≤ p.length :=
  complexity_le_length (ofMultiTapeTM_produces_iff.mpr h)

/-- An input from which the machine computes `x` within `t` steps bounds the time-bounded
complexity `C_tm^t(x)`. -/
theorem timeBoundedComplexity_ofMultiTapeTM_le (ht : tm.RunsInTime p t) (h : tm.Computes p x) :
    (ofMultiTapeTM tm).timeBoundedComplexity t x ≤ p.length :=
  timeBoundedComplexity_le_length (mem_ofMultiTapeTM_run_iff.mpr ⟨ht, h⟩)

/-! ### A machine simulating the literal method -/

/-- From a computation of the identity, a simulation of the literal description method with one
extra step. -/
noncomputable def literalSimulation
    (h : tm.ComputesFunInTimeAndSpace (Function.Embedding.refl _) (Function.Embedding.refl _) id
      (fun p => p.length + 1) (fun _ => 0)) :
    Simulation literal (ofMultiTapeTM tm) 0 fun _ t => t + 1 where
  compile := id
  length_compile_le _ := le_rfl
  mem_run_compile {p t x} hpx := by
    obtain ⟨hp, rfl⟩ := mem_literal_run.mp hpx
    exact mem_ofMultiTapeTM_run_iff.mpr ⟨(h p).2.1.mono (Nat.succ_le_succ hp), (h p).1⟩

/-- Some machine with finitely many states simulates the literal description method with one extra
step, so under it every string `x` has complexity at most `|x|` within `|x| + 1` steps. -/
theorem exists_simulation_literal :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
      Nonempty (Simulation literal (ofMultiTapeTM tm) 0 fun _ t => t + 1) :=
  let ⟨k, State, hfin, tm, h⟩ := MultiTapeTM.computableInTimeAndSpace_id
    (enc := Function.Embedding.refl (List Bool))
  ⟨k, State, hfin, tm, ⟨literalSimulation h⟩⟩

end Cslib.Kolmogorov.DescriptionMethod
