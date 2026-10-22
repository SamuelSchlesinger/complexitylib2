/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.ACC0.Basic
public import Complexity.Computability.Circuit.Boolean.ACC0.Simulation
public import Complexity.Computability.Circuit.Boolean.ACC0.SymPlus
public import Complexity.Computability.Circuit.Boolean.ACC0.Williams

/-!
# ACC⁰, fast `Sym⁺` evaluation, and modular circuit lower bounds

This module re-exports the `ACC⁰` development split across four submodules:

* `Complexity.Computability.Circuit.Boolean.ACC0.Basic`: definition of `ACC0 = ⋃ q ≥ 2, AC0Mod q`,
  degenerate moduli `AC0Mod 0 = AC0Mod 1 = AC0`, divisibility monotonicity
  `AC0Mod_subset_AC0Mod_of_dvd`, Boolean closure (`ACC0.compl`, `ACC0.inf`, `ACC0.sup`),
  `ACC0_subset_TC0`, and strict separations `AC0 ⊂ ACC0` and `AC0Mod p ⊂ ACC0` for odd prime `p`.
* `Complexity.Computability.Circuit.Boolean.ACC0.Simulation`: logarithmic-depth unbounded-fan-in
  and polynomial-size De Morgan simulations of `MOD_q` circuits, `ACMod_subset_AC_succ`,
  `ACC0 ⊆ AC 1 ⊆ NC 2 ⊆ PPoly`, and `SIZEMod_subset_SIZE`.
* `Complexity.Computability.Circuit.Boolean.ACC0.SymPlus`: depth-two `Sym⁺` (`Sym ∘ AND`) circuits
  (`SymPlusCircuit`) and split-variable Fast Zeta multipoint evaluation
  (`SymPlusCircuit.fastSymPlusEval`), building on `Complexity.Foundations.Data.BitString.Zeta`.
* `Complexity.Computability.Circuit.Boolean.ACC0.Williams`: unconditional separations against `AC0`,
  `AC0Mod p`, and `SIZEMod q` in `P`, `Σ₂`, and `NEXP`, and the Karp–Lipton collapse
  `PH_eq_SigmaP_two_of_NEXP_subset_ACC0`. Williams's full `NEXP ⊄ ACC⁰` separation is not proved
  here.

## Main definitions

* `Cslib.Circuits.Boolean.ACC0`: the class ACC⁰ = `⋃ q ≥ 2, AC0Mod q`.
* `Cslib.Circuits.Boolean.SIZEMod`: languages decided by `MOD_q` circuits of size at most `s n`.
* `Cslib.Circuits.Boolean.SymPlusCircuit`: depth-two `Sym ∘ AND` circuits.

## Main results

* `Cslib.Circuits.Boolean.ACC0_eq_iUnion_AC0Mod`: `ACC⁰ = ⋃ q, AC⁰[q]`.
* `Cslib.Circuits.Boolean.ACC0.compl`, `Cslib.Circuits.Boolean.ACC0.inf`,
  `Cslib.Circuits.Boolean.ACC0.sup`: Boolean closure of `ACC⁰`.
* `Cslib.Circuits.Boolean.ACC0_subset_TC0`, `Cslib.Circuits.Boolean.ACC0_subset_AC_one`,
  `Cslib.Circuits.Boolean.ACC0_subset_NC_two`, `Cslib.Circuits.Boolean.ACC0_subset_PPoly`.
* `Cslib.Circuits.Boolean.SymPlusCircuit.fastSymPlusEval_eq_eval`: correctness of Williams's fast
  `Sym⁺` evaluation.
* `Cslib.Circuits.Boolean.exists_mem_SigmaP_two_notMem_SIZEMod`,
  `Cslib.Circuits.Boolean.exists_mem_NEXP_notMem_SIZEMod`: unconditional fixed-degree `MOD_q`
  circuit lower bounds in `Σ₂` and `NEXP` for every modulus `q`.
* `Cslib.Circuits.Boolean.PH_eq_SigmaP_two_of_NEXP_subset_ACC0`: `NEXP ⊆ ACC⁰` collapses `PH` to
  `Σ₂`.

## References

* [R. Williams, *Nonuniform ACC Circuit Lower Bounds*][Williams2014]
* [A. C.-C. Yao, *On ACC and threshold circuits*][Yao1990]
* [R. Beigel, J. Tarui, *On ACC*][BeigelTarui1994]
* [D. A. M. Barrington, *Bounded-width polynomial-size branching programs recognize exactly those
  languages in NC¹*][Barrington1989]
* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section
