/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Program

/-!
# Fair-coin multi-tape machines

`MultiTapePTM` specializes the common table to one action per Boolean coin value. Its run is
the common interpreter with a handler that samples a bit and selects the corresponding action.
Even equal branches consume a bit; halted configurations consume no more bits.

The open run accepts a typed program supplying coins and a program answering each named oracle
call. This separates the syntax from the interpretation: fair-coin semantics requires interpreting
the coin program as an independent uniform bit. `runClosed` fixes this interpretation through
`ProbComp.uniform Bool` for machines without oracle channels. No efficiency assertion about an
arbitrary coin program or oracle handler is made here.

Adapted from the cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.

## Main definitions

* `Turing.MultiTapePTM`: the Boolean-indexed specialization of the common machine.
* `Turing.MultiTapePTM.runConfigFrom`: the run program with explicit coin and query programs.
* `Turing.MultiTapePTM.runClosed`: a closed fair-coin run using the finite-uniform interface.
-/

@[expose] public section

namespace Turing

open Cslib

/-- A machine with one transition per Boolean coin; by default it has no oracle channels. -/
abbrev MultiTapePTM (k : ℕ) (Symbol State : Type) (Oracle : Type := Empty) :=
  MultiTapeMachine k Symbol State Oracle (fun α => Bool → α)

namespace MultiTapePTM

open MultiTapeMachine

variable {k : ℕ} {Symbol State Oracle Query : Type} {spec : OracleSpec.{0, 0} Query}
  {input : List Symbol} [DecidableEq Oracle]

/-- Run with the supplied coin program, retaining the whole configuration at clock exhaustion. -/
def runConfigFrom (machine : MultiTapePTM k Symbol State Oracle) (coin : OracleComp spec Bool)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol)) (fuel : ℕ)
    (cfg : Config k Symbol State Oracle input) :
    OracleComp spec (Config k Symbol State Oracle input) :=
  MultiTapeMachine.runConfigFrom machine (fun choices => choices <$> coin) query fuel cfg

/-- Observe the output word of an open run. -/
def runFrom (machine : MultiTapePTM k Symbol State Oracle) (coin : OracleComp spec Bool)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol)) (fuel : ℕ)
    (cfg : Config k Symbol State Oracle input) : OracleComp spec (List Symbol) :=
  (fun final => final.tapes.output) <$> machine.runConfigFrom coin query fuel cfg

/-- Run from the initial configuration with explicit coin and oracle programs. -/
def run (machine : MultiTapePTM k Symbol State Oracle) (coin : OracleComp spec Bool)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol)) (fuel : ℕ)
    (input : List Symbol) : OracleComp spec (List Symbol) :=
  machine.runFrom coin query fuel (machine.initialConfig input)

/-- The closed fair-coin run, with fresh uniform Boolean choices at each live transition. -/
noncomputable def runClosed (machine : MultiTapePTM k Symbol State) (fuel : ℕ)
    (input : List Symbol) : ProbComp (List Symbol) :=
  machine.run (ProbComp.uniform Bool) (fun oracle => oracle.elim) fuel input

/-- Forget probabilities, retaining exactly the actions selected by some coin value. -/
def toNondeterministic (machine : MultiTapePTM k Symbol State Oracle) :
    MultiTapeMachine k Symbol State Oracle Set where
  initial := machine.initial
  tr state symbol work answer := Set.range (machine.tr state symbol work answer)

end MultiTapePTM

end Turing
