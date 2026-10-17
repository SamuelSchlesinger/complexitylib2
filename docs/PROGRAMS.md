# Programs and efficiency proofs

Write the function first, choose its encodings, then prove its resource bound. The shared
calculus composes certificates for primitive operations and routines. Examples below are
exercised in [PolyTimeTactic](../ComplexityTests/PolyTimeTactic.lean) and
[PPTTactic](../ComplexityTests/PPTTactic.lean).

## Deterministic programs

```lean
import Complexity.Tactic.PolyTime

open Turing.MultiTapeTM

example : ComputableTidilyInPolyTime
    (fun p : ℕ × List ℕ => (List.range p.1).flatMap fun i => p.2.map fun j => i + j)
    (encPair encUnary (encList encUnary)) (encList encUnary) := by
  polytime
```

`ComputableTidilyInPolyTime f input output` asserts that one machine tidily computes `f`, with
time and space polynomial in the length of the encoded input. Tidy execution supplies the
machine interface needed for composition. The certificate concerns the formal machine model;
it is not a benchmark of Lean's evaluator.

The deterministic backend builds on Christian Reitwiessner's tidy machine calculus. Its
[encoding interfaces](../Complexity/Computability/Machines/Turing/MultiTape/Combinators/Encoding.lean)
explain the shared representation contracts; the tactic modules credit their source implementations.

The encoding is part of the claim. `encBits` encodes a bit list directly, `encBool` encodes one
bit, `encUnary` encodes a natural number in unary, and `encNat` uses binary. `encPair` and
`encList` build structured encodings. The example uses unary naturals, so a loop of length
`p.1` is bounded by the input length. A unary bound cannot simply be reused for binary input.
Changing an arbitrary encoding requires a certified conversion.

Use `fun_prop` for compositional properties, including polynomial bounds and supported
computation certificates. `polytime` combines these rules with routine certificates and bounded
loop rules through Aesop. Neither tactic supplies an implementation for an unknown algorithm.

## Reusing certified routines

Local certificates compose through ordinary argument preparation:

```lean
import Complexity.Tactic.PolyTime

open Turing.MultiTapeTM

example (f g : List Bool → List Bool)
    (hf : ComputableTidilyInPolyTime f encBits encBits)
    (hg : ComputableTidilyInPolyTime g encBits encBits) :
    ComputableTidilyInPolyTime (fun word => g (f word) ++ word) encBits encBits := by
  polytime
```

For named routines, attach `@[program_certificate]` to the efficiency theorem. The attribute
indexes the theorem for `polytime` and `ppt` and also registers it with `fun_prop`. Clients can
then use the routine without unfolding its implementation. It registers an existing proof;
it does not generate the routine's certificate. The supported theorem forms and optional
hypothesis ordering are documented in
[PolyTime.Init](../Complexity/Tactic/PolyTime/Init.lean).

## Loops and correctness invariants

A polynomial-time step can grow its state too quickly for a polynomial-time loop. The loop
contract therefore includes a bound on the encoded intermediate state. Simple fixed additive
growth is handled automatically. For other loops, supply a value-level invariant and size bound.

This fold contract proves both efficiency and the intended result:

```lean
import Complexity.Tactic.PolyTime

open Turing.MultiTapeTM

example : ComputableTidilyInPolyTime
      (fun word : List Bool => word.foldl (fun reversed bit => bit :: reversed) [])
      encBits encBits ∧
    ∀ word : List Bool, word.foldl (fun reversed bit => bit :: reversed) [] = word.reverse := by
  apply ComputableTidilyInPolyTime.foldl_spec (encA := encBool) (encL := encBits)
    (invariant := fun _ consumed state => state = consumed.reverse) (size := id)
  · polytime
  · polytime
  · polytime
  · simp
  · intro word consumed state bit _ hstate
    simp [hstate]
  · fun_prop
  · intro word consumed state hprefix hstate
    simpa [hstate] using hprefix.length_le
```

The invariant describes the reversed prefix. Its preservation proof is the algorithm-specific
argument; the step and input certificates are routine. `iterate_spec` and `iterateWith_spec`
provide the corresponding rules for iteration, including a captured input. See the
[tactic tests](../ComplexityTests/PolyTimeTactic.lean) for nested loops, lookup, alternative
encodings, and failure checks for exponential growth.

## Probabilistic programs

```lean
import Complexity.Tactic.PPT

open Cslib Cslib.Probability Turing.MultiTapeTM

example : IsPPTOn encBits encBits (fun word => do
    let bit ← ProbComp.uniform Bool
    pure (if bit then word.reverse else word)) := by
  ppt
```

`ProbComp` uses typed programs and finite sampling operations. `IsPPTOn input output program`
gives one finite fair-coin machine with a polynomial clock whose encoded output distribution
equals the program's distribution. The clock is strict on every execution and charges writing
the output. [Clock compilation](../Complexity/Computability/Probabilistic/PPT/Clock.lean) also
gives an intrinsically halting machine, charging preparation and consumption of the budget.
`IsPPT` specializes the encoded contract to a unary security parameter and an auxiliary bit
string. Deterministic callbacks reuse `polytime` certificates.

Supported sampling rules include fair bits and uniformly random bit strings of efficiently
computed lengths. Other sampling operations need their own machine certificates.

General probabilistic loops use `IsPPTOn.iterate_spec` with an invariant on supported states.
For efficient closed oracle substitution, supply a certified handler and a supported-state
invariant bounding replies and storage growth; the oracle-PPT certificate provides the query
bounds. The substitution rules preserve the joint result and final state, charging their encoded
storage. These contracts require explicit simulation arguments; `ppt` does not automatically
certify arbitrary open-oracle composition. Start with
[OracleSimulation](../Complexity/Computability/Probabilistic/OracleSimulation.lean) and its
[clients](../ComplexityTests/OraclePPT.lean).

An efficiency certificate supports a security proof; security is a separate theorem about
experiments and adversaries. For a substantial example, follow
[GGM evaluation](../Complexity/Crypto/Computational/GGM/Evaluation.lean) through
[adaptive security](../Complexity/Crypto/Computational/GGM/Security.lean), with executable and
certified clients in [GGM tests](../ComplexityTests/GGM.lean).

Return to the [library guide](LIBRARY.md) or [mission and design](DESIGN.md).
