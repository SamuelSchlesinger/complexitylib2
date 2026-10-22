/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Generic
public import Complexity.Computability.GenericRAM.Simulation.Run
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Tactic.PolyTime.Init

/-!
# Native primitive certificates and whole-run transport for WordRAM

The width is a runtime input encoded in unary; operand values are encoded in binary. A single
native machine handles every width and both operands, returning `none` precisely when the sum
does not fit. Its polynomial bound is in the complete encoded input length, including the unary
width, not the bit length of a binary-encoded width. No claim about the other standard-basis
operations, memory access or whole-program simulation follows from this primitive certificate.
Computable width selection with charged costs and input fit remain separate obligations.

Via `WordRAM.Program.toGeneric`, halting `WordRAM.Executes` runs correspond to halting
`GenericRAM.FiniteState.run` executions and inherit whole-run native transport
(`WordRAM.transportCertificate`, `WordRAM.transport_inO`, `WordRAM.transport_polyTime`, and
`WordRAM.transport_polyTime_of_le_const`) whenever a `NativePrimitives` bundle is supplied for
`B.genericModel`.

## Main results

* `checkedAdd_polyTime`: native polynomial time for checked standard-basis addition.
* `checkedAddCertificate`: arbitrary-bound interface obtained from that implementation.
* `executes_iff_exists_finiteRun`, `transportCertificate`, `transport_inO`,
  `transport_polyTime`, `transport_polyTime_of_le_const`: whole-run native transport for `WordRAM`
  programs via `GenericRAM.FiniteState`.

## References

* [MIT–ULB CompGeom Group, *Undecidability of tiling with a tromino*][Tromino2025]

Uses Christian Reitwiessner's binary natural encodings and native machine arithmetic through the
library's polynomial-time calculus.
-/

@[expose] public section

namespace Cslib.WordRAM

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Checked addition is polynomial in the full encoding: unary width and binary operands. -/
@[program_certificate]
theorem checkedAdd_polyTime :
    ComputableTidilyInPolyTime (Basis.standard.genericModel.checkedOp (.bin .add))
      (encPair encUnary (encPi encNat)) (encOption encNat) := by
  have hx := (pi_apply encNat (0 : Fin 2)).comp (snd encUnary (encPi encNat))
  have hy := (pi_apply encNat (1 : Fin 2)).comp (snd encUnary (encPi encNat))
  have hadd := binary_add.comp (hx.prod hy)
  have hpow := binary_two_pow.comp (fst encUnary (encPi encNat (Index := Fin 2)))
  change ComputableTidilyInPolyTime
    (fun p : ℕ × (Fin 2 → ℕ) => if decide (p.2 0 + p.2 1 < 2 ^ p.1)
      then some (p.2 0 + p.2 1) else none)
    (encPair encUnary (encPi encNat (Index := Fin 2))) (encOption encNat)
  simp only [decide_eq_true_eq]
  exact (binary_lt.comp (hadd.prod hpow)).ite_decide
    ((optionSome encNat).comp hadd) (const none)

/-- One native checked-add implementation works at every encoded width. -/
noncomputable def checkedAddCertificate :
    GenericRAM.NativeCertificate (Basis.standard.genericModel.checkedOp (.bin .add))
      (encPair encUnary (encPi encNat)) (encOption encNat) :=
  .ofPolyTime checkedAdd_polyTime

/-! ## Whole-run transport adapter -/

noncomputable section

open Cslib.GenericRAM

variable {B : Basis} {r : ℕ} {α : Type} {ei : α ↪ List Bool}

/-- Halting `WordRAM.Executes` runs correspond to halting `FiniteState.run` executions of
`p.toGeneric`. -/
theorem executes_iff_exists_finiteRun (w : ℕ) (p : Program B r)
    (s : FiniteState B.genericModel r) (u : State r) (hden : s.denote = u.toGeneric B)
    (v : ℕ) :
    (∃ m, Executes w p u v m) ↔ ∃ n, FiniteState.run w p.toGeneric n s = some (.inr v) := by
  rw [← FiniteState.executes_iff_exists_run, hden]
  exact ⟨fun ⟨m, h⟩ => ⟨m, executes_toGeneric_iff.mpr h⟩,
    fun ⟨m, h⟩ => ⟨m, executes_toGeneric_iff.mp h⟩⟩

/-- Transport a halting `WordRAM.Executes` certificate within `steps a` instructions to a native
multitape Turing-machine certificate for `f : α → ℕ`. -/
def transportCertificate (enc : B.genericModel.Encoding) (N : B.genericModel.NativePrimitives enc)
    (p : Program B r) {f : α → ℕ} {cfg : α → ℕ}
    {initState : α → FiniteState B.genericModel r} {u : α → State r} {steps : α → ℕ}
    (cSteps : NativeCertificate steps ei encNat)
    (cCfg : NativeCertificate cfg ei enc.config)
    (cInit : NativeCertificate initState ei (FiniteState.encoding enc))
    (hden : ∀ a, (initState a).denote = (u a).toGeneric B)
    (hExec : ∀ a, ∃ m ≤ steps a, Executes (cfg a) p (u a) (f a) m) :
    NativeCertificate f ei enc.value :=
  FiniteState.transportCertificate enc N p.toGeneric cSteps cCfg cInit fun a => by
    obtain ⟨m, hm, hex⟩ := hExec a
    rw [hden a]
    exact ⟨m, hm, executes_toGeneric_iff.mpr hex⟩

/-- Parameterized `ComputableTidilyInO` transport theorem from `WordRAM.Executes`. -/
theorem transport_inO (enc : B.genericModel.Encoding) (N : B.genericModel.NativePrimitives enc)
    (p : Program B r) {f : α → ℕ} {cfg : α → ℕ}
    {initState : α → FiniteState B.genericModel r} {u : α → State r} {steps : α → ℕ}
    (cSteps : NativeCertificate steps ei encNat)
    (cCfg : NativeCertificate cfg ei enc.config)
    (cInit : NativeCertificate initState ei (FiniteState.encoding enc))
    (hden : ∀ a, (initState a).denote = (u a).toGeneric B)
    (hExec : ∀ a, ∃ m ≤ steps a, Executes (cfg a) p (u a) (f a) m) :
    ComputableTidilyInO f ei enc.value
      (fun a => cSteps.time a + (cCfg.time a + cInit.time a) +
        FiniteState.runTime enc N p.toGeneric (steps a, (cfg a, initState a)))
      (fun a => cSteps.space a + (cCfg.space a + cInit.space a) +
        FiniteState.runSpace enc N p.toGeneric (steps a, (cfg a, initState a))) :=
  (transportCertificate enc N p cSteps cCfg cInit hden hExec).computes

/-- Automatic `ComputableTidilyInPolyTime` transport corollary from `WordRAM.Executes`. -/
theorem transport_polyTime (enc : B.genericModel.Encoding)
    (N : B.genericModel.NativePrimitives enc)
    (p : Program B r) {f : α → ℕ} {cfg : α → ℕ}
    {initState : α → FiniteState B.genericModel r} {u : α → State r} {steps : α → ℕ}
    (cSteps : NativeCertificate steps ei encNat)
    (cCfg : NativeCertificate cfg ei enc.config)
    (cInit : NativeCertificate initState ei (FiniteState.encoding enc))
    (hden : ∀ a, (initState a).denote = (u a).toGeneric B)
    (hExec : ∀ a, ∃ m ≤ steps a, Executes (cfg a) p (u a) (f a) m)
    (hN : N.IsPolynomial)
    (hSteps : cSteps.IsPolynomial) (hCfg : cCfg.IsPolynomial) (hInit : cInit.IsPolynomial)
    (hStepsBound : PolyBounded (fun a => (ei a).length) steps)
    {bound : α → ℕ} (hB : PolyBounded (fun a => (ei a).length) bound)
    (hOutLen : ∀ a, ∀ j ≤ steps a,
      (FiniteState.resultEncoding enc
        (FiniteState.run (cfg a) p.toGeneric j (initState a))).length ≤ bound a) :
    ComputableTidilyInPolyTime f ei enc.value :=
  FiniteState.transport_polyTime enc N p.toGeneric cSteps cCfg cInit
    (fun a => by
      obtain ⟨m, hm, hex⟩ := hExec a
      rw [hden a]
      exact ⟨m, hm, executes_toGeneric_iff.mpr hex⟩)
    hN hSteps hCfg hInit hStepsBound hB hOutLen

/-- Automatic `ComputableTidilyInPolyTime` transport corollary from `WordRAM.Executes` under a
constant step-budget bound `∀ a, steps a ≤ K`. -/
theorem transport_polyTime_of_le_const (enc : B.genericModel.Encoding)
    (N : B.genericModel.NativePrimitives enc)
    (p : Program B r) {f : α → ℕ} {cfg : α → ℕ}
    {initState : α → FiniteState B.genericModel r} {u : α → State r} {steps : α → ℕ}
    (cSteps : NativeCertificate steps ei encNat)
    (cCfg : NativeCertificate cfg ei enc.config)
    (cInit : NativeCertificate initState ei (FiniteState.encoding enc))
    (hden : ∀ a, (initState a).denote = (u a).toGeneric B)
    (hExec : ∀ a, ∃ m ≤ steps a, Executes (cfg a) p (u a) (f a) m)
    (hN : N.IsPolynomial)
    (hSteps : cSteps.IsPolynomial) (hCfg : cCfg.IsPolynomial) (hInit : cInit.IsPolynomial)
    (K : ℕ) (hStepsLe : ∀ a, steps a ≤ K) :
    ComputableTidilyInPolyTime f ei enc.value :=
  FiniteState.transport_polyTime_of_le_const enc N p.toGeneric cSteps cCfg cInit
    (fun a => by
      obtain ⟨m, hm, hex⟩ := hExec a
      rw [hden a]
      exact ⟨m, hm, executes_toGeneric_iff.mpr hex⟩)
    hN hSteps hCfg hInit K hStepsLe

end

end Cslib.WordRAM
