/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract tests)

import ComplexityTests.Abstracts.Check
import ComplexityTests.Abstracts.ShamirBridge

/-! # Shamir's theorem: IP equals PSPACE

Interaction lets a verifier challenge a prover about a computation far larger than the verifier
could inspect directly. Shamir turns quantified Boolean formulas into arithmetic expressions:
the prover supplies polynomial claims, and the verifier checks their consistency at random field
points. These local checks suffice to verify every problem decidable in polynomial space, using
only polynomial time on the verifier's side. Conversely, the best success probability of such an
interaction can be analyzed in polynomial space, giving equality of the two classes.

The verifier is one finite fair-coin oracle machine with a polynomial clock uniform over all
stateful randomized provers. Completeness is at least two thirds and soundness at most one third;
bounds and correctness apply to encoded instances. The explicit foundational model below
distinguishes finite-uniform requests in program syntax from their efficient fair-coin realization.

Lean checks the bridge, and the audit permits only the seven listed foundational program and
machine modules, with no complexity-class or headline-result allowance.

## References

* [A. Shamir, *IP = PSPACE*][Shamir1992]
* [A. Shen, *IP = SPACE: simplified proof*][Shen1992]
* [S. Goldwasser, S. Micali, C. Rackoff, *The knowledge complexity of interactive proof systems*]
  [GoldwasserMicaliRackoff1989]
-/

namespace ComplexityTests.Abstracts.ShamirAbstract

/-- A Boolean is encoded by a single bit. -/
def encBool : Bool ↪ List Bool := ⟨fun b => [b], by intro a b h; injection h⟩

/-- A terminating return/request tree. A private request indexed by `n` draws a fresh uniform
`Fin (n+1)`; an external request sends `((), word)` and receives a word. Private draws do not
change the oracle's state. Bare syntax imposes no efficiency or fair-coin implementability:
those are required separately by `StrictOraclePPT`. -/
abbrev InteractiveProgram (β : Type) :=
  Cslib.ProbOracleComp (fun _ : Unit × List Bool => List Bool) β

/-- One fixed finite fair-coin machine and one polynomial clock realize the entire joint law
of the program's encoded result and the oracle's final state, against every stateful oracle.
Each live instruction consumes one fresh fair bit to select between two transitions. Ordinary
steps perform an upstream tape action, append at most one bit to a query buffer and move a
read-only reply head by at most one cell. A query step submits the buffer, installs the reply,
resets the reply head and clears the buffer. Each instruction costs one unit; the oracle's
computation is external. The bounded run observes its written output on halting or clock
exhaustion, so the definition does not pretend the unclocked machine has already halted. -/
def StrictOraclePPT {α β : Type} (enc : α ↪ List Bool) (out : β ↪ List Bool)
    (program : α → InteractiveProgram β) : Prop :=
  ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (machine : Turing.MultiTapePTM k Bool Control Unit) (c d : ℕ),
    ∀ a (State : Type)
      (oracle : Unit × List Bool → StateT State PMF (List Bool)) s,
      Cslib.ProbOracleComp.runWith oracle (out <$> program a) s =
        Cslib.ProbOracleComp.runWith oracle
          (machine.runOracle (c * ((enc a).length + 1) ^ d) (enc a)) s

/-- Acceptance probability against a prover with arbitrary private state and probabilistic
responses. The response function sees the message and its own state, not the verifier's coins. -/
noncomputable def acceptProbability (program : InteractiveProgram Bool)
    (State : Type)
    (respond : Unit × List Bool → StateT State PMF (List Bool)) (initial : State) : ENNReal :=
  (Cslib.ProbOracleComp.runWith respond program initial).map Prod.fst true

/-- Private-coin interactive proofs: strict polynomial verifier, completeness at least 2/3
for some unbounded prover on each member, soundness at most 1/3 against every unbounded stateful
randomized prover on every nonmember. The efficiency clock is uniform over all those provers. -/
def IP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ verifier : α → InteractiveProgram Bool, StrictOraclePPT enc encBool verifier ∧
    (∀ a ∈ A, ∃ (State : Type) (initial : State)
      (respond : Unit × List Bool → StateT State PMF (List Bool)),
      (2 / 3 : ENNReal) ≤ acceptProbability (verifier a) State respond initial) ∧
    ∀ a ∉ A, ∀ (State : Type) (initial : State)
      (respond : Unit × List Bool → StateT State PMF (List Bool)),
      acceptProbability (verifier a) State respond initial ≤ (1 / 3 : ENNReal)}

/-- Total deterministic polynomial-space decision, using plain upstream Turing machines.
The input is read-only, output write-only and the time bound is unrestricted. -/
def PSPACE {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (f : α → Bool) (t : α → ℕ) (s : ℕ → ℕ), Cslib.PolynomiallyBounded s ∧
    Turing.MultiTapeTM.ComputableInTimeAndSpace f enc encBool t (fun a => s (enc a).length) ∧
    ∀ a, a ∈ A ↔ f a = true}

/-- Private-coin interactive proofs with strict polynomial-time verifiers capture
deterministic polynomial space. Provers may be stateful, randomized and unbounded. -/
theorem ip_eq_pspace {α : Type} (enc : α ↪ List Bool) : IP enc = PSPACE enc :=
  ShamirBridge.ip_eq_pspace enc

/--
info: abstract audit passed for `ComplexityTests.Abstracts.ShamirAbstract`:
10 root declarations, 213 dependencies checked
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.ShamirAbstract allowing [
  Complexity.Computability.Machines.Turing.MultiTape.Machine,
  Complexity.Computability.Machines.Turing.MultiTape.Machine.Program,
  Complexity.Computability.Machines.Turing.MultiTape.Probabilistic,
  Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Oracle,
  Complexity.Languages.Probabilistic.Basic,
  Complexity.Languages.Probabilistic.Oracle,
  Complexity.Languages.Probabilistic.Oracle.Interaction
]

end ComplexityTests.Abstracts.ShamirAbstract
