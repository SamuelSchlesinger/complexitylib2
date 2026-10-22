/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract tests)

import ComplexityTests.Abstracts.Check
import ComplexityTests.Abstracts.CryptographyBridge

/-! # One-way functions, generators and adaptive pseudorandom functions

A one-way function is easy to compute, but finding any preimage of its output on a random input
is hard for every efficient randomized algorithm. Assuming such a function, the
Håstad–Impagliazzo–Levin–Luby construction produces a generator whose output is one bit longer
than its seed and computationally indistinguishable from uniform bits. The
Goldreich–Goldwasser–Micali construction then produces a keyed function that looks like one
consistently chosen random function even when each query depends on earlier answers.
Existence of a one-way function remains a hypothesis; efficiency and security use uniform
finite-control machines with strict polynomial bounds and independent fair coins.
Lean checks the explicit experiments below through `CryptographyBridge`, and `#check_abstract`
allows only the six foundational oracle-syntax and machine modules described in the adaptive
section across the implementation boundary.

## References

* [J. Håstad, R. Impagliazzo, L. Levin, M. Luby,
  *A Pseudorandom Generator from Any One-Way Function*][HILL1999]
* [T. Holenstein, *Pseudorandom Generators from One-Way Functions*][Holenstein2006], Sections 4–5.
* [S. Arora, B. Barak, *Computational Complexity*][AroraBarak09], Chapter 9.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Chapter 3.
* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986]

The typed oracle-program syntax follows VCVio, by Devon Tuma, Quang Dao and collaborators,
as credited in `Complexity.Languages.Probabilistic.Basic`.
-/

namespace ComplexityTests.Abstracts.CryptographyAbstract

/-- Self-delimiting framing: double each bit `b` to `[true,b]` and terminate with `[false]`. -/
def frame (w : List Bool) : List Bool := w.flatMap (fun b => [true, b]) ++ [false]

/-- Encode a pair by framing its first component and appending its second. -/
def encodePair {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) (p : α × β) :
    List Bool := frame (a p.1) ++ b p.2

theorem encodePair_injective {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) :
    Function.Injective (encodePair a b) := CryptographyBridge.encodePair_injective a b

/-- The injective pair encoding. The arrow `↪` means an injective function. -/
def pairEncoding {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) : α × β ↪ List Bool :=
  ⟨encodePair a b, encodePair_injective a b⟩

/-- Bitstrings encode as themselves. -/
def bitsEncoding : List Bool ↪ List Bool := Function.Embedding.refl _

/-- The security parameter is supplied in unary: `n` consecutive true bits. -/
def unaryEncoding : ℕ ↪ List Bool := ⟨fun n => List.replicate n true,
  fun _ _ h => by simpa only [List.length_replicate] using congrArg List.length h⟩

/-- A Boolean output encodes as one bit. -/
def boolEncoding : Bool ↪ List Bool := ⟨fun b => [b], fun _ _ h => by injection h⟩

/-- One deterministic finite-state binary multitape Turing machine halts with the encoded
answer on every encoded input, within polynomially bounded time and space in its bit length.
`ComputableInTimeAndSpaceOfLength` is the upstream machine contract; both bounds are uniform. -/
def PolyTime {α β : Type} (f : α → β) (a : α ↪ List Bool) (b : β ↪ List Bool) : Prop :=
  ∃ t s : ℕ → ℕ, Cslib.PolynomiallyBounded t ∧ Cslib.PolynomiallyBounded s ∧
    Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength f a b t s

/-- Exactly `n` independent fair bits, as a word of length `n`. -/
noncomputable def uniformBits (n : ℕ) : PMF (List Bool) :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin n → Bool)).map List.ofFn

/-- A uniformly strict polynomial-time probability law: one deterministic evaluator, supplied
with polynomially many independent fair bits, realizes every input's law exactly. Its time
includes reading the coin tape and writing the encoded output. Both evaluator and polynomial
are fixed before the input. This also bounds every execution, rather than its expectation. -/
def StrictPPT {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool)
    (law : α → PMF β) : Prop :=
  ∃ (c d : ℕ) (evaluate : α → List Bool → β),
    PolyTime (fun p : α × List Bool => evaluate p.1 p.2) (pairEncoding a bitsEncoding) b ∧
    ∀ x, law x = (uniformBits (c * ((a x).length + 1) ^ d)).map (evaluate x)

/-- A nonnegative error is negligible if multiplication by every fixed power of the security
parameter still tends to zero. The threshold and decay bound may depend on the whole adversary. -/
def Negligible (ε : ℕ → NNReal) : Prop :=
  ∀ k : ℕ, Filter.Tendsto (fun n : ℕ => (n : NNReal) ^ k * ε n)
    Filter.atTop (nhds 0)

/-- Probability that a Boolean experiment returns true. -/
noncomputable def probability (p : PMF Bool) : NNReal := (p true).toNNReal

/-- Every one uniform strict PPT test has negligible distinguishing advantage.
The test receives the unary seed length and a sample. `bind` samples the word and then runs
the test with independent coins; `nndist` is the absolute difference of success probabilities. -/
def Indistinguishable (X Y : ℕ → PMF (List Bool)) : Prop :=
  ∀ test : ℕ → List Bool → PMF Bool,
    StrictPPT (pairEncoding unaryEncoding bitsEncoding) boolEncoding
      (fun p => test p.1 p.2) →
    Negligible (fun n => nndist (probability ((X n).bind (test n)))
      (probability ((Y n).bind (test n))))

/-- A polynomial-time function is one-way if every strict PPT inverter, given unary `n` and
`f(x)` for a uniform `n`-bit `x`, finds any preimage only with negligible probability.
The candidate's length is unrestricted, and recovering the sampled `x` is unnecessary. -/
def OneWay (f : List Bool → List Bool) : Prop :=
  PolyTime f bitsEncoding bitsEncoding ∧
    ∀ inverter : ℕ → List Bool → PMF (List Bool),
      StrictPPT (pairEncoding unaryEncoding bitsEncoding) bitsEncoding
        (fun p => inverter p.1 p.2) →
      Negligible (fun n => probability ((uniformBits n).bind fun x =>
        (inverter n (f x)).map fun candidate => f candidate == f x))

/-- A deterministic polynomial-time generator has exact seed-dependent output length,
strictly expands every length, and its uniform-seed outputs are indistinguishable from the
uniform distribution at that output length. The security parameter in both games is the
seed length. The function need not be injective. -/
def PseudorandomGenerator (g : List Bool → List Bool) (length : ℕ → ℕ) : Prop :=
  PolyTime g bitsEncoding bitsEncoding ∧
    (∀ seed, (g seed).length = length seed.length) ∧ (∀ n, n < length n) ∧
    Indistinguishable (fun n => (uniformBits n).map g) (fun n => uniformBits (length n))

/-- **Håstad–Impagliazzo–Levin–Luby:** any uniform one-way function yields a deterministic
uniform polynomial-time generator stretching every `n`-bit seed to `n+1` bits. The proof follows
Holenstein's pseudoentropy route. No entropy estimate or nonuniform advice is an extra hypothesis;
the theorem does not assert optimized seed-length exponents or practical efficiency. -/
theorem hill {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ g : List Bool → List Bool, PseudorandomGenerator g (fun n => n + 1) :=
  CryptographyBridge.hill hf

/-- **Existence equivalence:** uniform one-way functions exist exactly when uniform
pseudorandom generators exist. This is a conditional equivalence, not an existence assertion. -/
theorem existence_equivalence :
    (∃ f : List Bool → List Bool, OneWay f) ↔
      ∃ (g : List Bool → List Bool) (length : ℕ → ℕ), PseudorandomGenerator g length :=
  CryptographyBridge.existence_equivalence

/-- **Polynomial stretch:** a one-bit generator yields any strictly larger output length
computable in polynomial time with unary input and output. The resulting algorithm remains
deterministic polynomial time and secure against the same uniform strict PPT tests. -/
theorem stretch {g : List Bool → List Bool}
    (hg : PseudorandomGenerator g (fun n => n + 1)) (target : ℕ → ℕ)
    (htarget : PolyTime target unaryEncoding unaryEncoding) (hgreater : ∀ n, n < target n) :
    ∃ g' : List Bool → List Bool, PseudorandomGenerator g' target :=
  CryptographyBridge.stretch hg target htarget hgreater

/-! ## Adaptive oracle tests and pseudorandom functions

A program is a terminating interaction tree. It can return a result, request an independent
uniform sample, or submit a word and branch on the oracle's reply. Its next requests may depend
on earlier replies. Termination alone gives no efficiency: the separate machine certificate
below charges ordinary computation, query writing, reply access and output writing.

The allowed machine is a binary multitape Turing machine with finite control and one named
oracle channel. Each channel has a write-only query buffer and a read-only reply tape with a
head. An ordinary transition reads input/work/reply cells, performs an upstream tape action,
appends at most one bit to the query buffer and moves the reply head by at most one cell.
A query instruction submits that buffer, installs the oracle's reply, resets the reply head
and clears the buffer. Each live instruction uses one independent fair bit to select between
two transitions. Each ordinary or query instruction costs one unit; the handler's computation
is external. The bounded interpreter starts with blank work and communication tapes and
returns the written output on halting or clock exhaustion. A later normalization theorem in
the implementation supplies an intrinsically halting realization with polynomial overhead.
-/

/-- Two disjoint effects: `.inl n` requests a fresh uniform `Fin (n+1)`; `.inr ((),word)`
submits a word to the single external channel and receives a word. This foundational response
family is reused exactly so the machine interpreter has the same typed interface. -/
abbrev OracleResponse : Sum ℕ (Unit × List Bool) → Type :=
  Cslib.probOracleSpec (fun _ : Unit × List Bool => List Bool)

/-- The free interaction tree for these effects. Upstream `PFunctor.FreeM` has two constructors:
`pure value` returns, and `liftBind request continuation` branches on the response. -/
abbrev OracleProgram (β : Type) :=
  (PFunctor.mk (Sum ℕ (Unit × List Bool)) OracleResponse).FreeM β

/-- Interpret a program against any shared stateful probabilistic handler. Fresh random draws
are independent of that handler and leave its private state unchanged; external requests can
update it. The result retains both the program's output and the final handler state. -/
noncomputable def execute {State β : Type} (program : OracleProgram β)
    (oracle : Unit × List Bool → StateT State PMF (List Bool)) (s : State) : PMF (β × State) :=
  (PFunctor.FreeM.liftM (P := ⟨Sum ℕ (Unit × List Bool), OracleResponse⟩)
    (fun q => match q with
    | .inl n => StateT.lift (Cslib.Probability.PMF.uniformOfFintype (Fin (n + 1)))
    | .inr request => oracle request) program).run s

/-- One uniform finite-control oracle machine realizes the entire interaction, at a strict
polynomial clock in the encoded unary parameter and auxiliary input. Equality is required for
every handler and starting state, preserving the final state as well as the output. The
machine cannot return an arbitrarily long reply for free: access and output writing are charged.
This is not a mere bound on the number of oracle queries. -/
def OraclePPT (program : ℕ → List Bool → OracleProgram Bool) : Prop :=
  ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (machine : Turing.MultiTapePTM k Bool Control Unit) (c d : ℕ),
    ∀ n aux (State : Type) (oracle : Unit × List Bool → StateT State PMF (List Bool)) s,
      execute (boolEncoding <$> program n aux) oracle s =
        execute (machine.runOracle (c * ((encodePair unaryEncoding bitsEncoding (n, aux)).length
          + 1) ^ d) (encodePair unaryEncoding bitsEncoding (n, aux))) oracle s

/-- Run a program against a fixed deterministic word oracle, with independent private samples. -/
noncomputable def evaluateOracle {β : Type} (program : OracleProgram β)
    (oracle : List Bool → List Bool) : PMF β :=
  PFunctor.FreeM.liftM (P := ⟨Sum ℕ (Unit × List Bool), OracleResponse⟩)
    (fun q => match q with
    | .inl n => Cslib.Probability.PMF.uniformOfFintype (Fin (n + 1))
    | .inr request => PMF.pure (oracle request.2)) program

/-- The real experiment samples one uniform key and consistently answers every valid query
with that key's function. Wrong-length queries return the empty word. The adversary receives
unary `n` and an empty auxiliary input. -/
noncomputable def realPRF (family : List Bool → List Bool → List Bool)
    (adversary : ℕ → List Bool → OracleProgram Bool) (n : ℕ) : PMF Bool :=
  (uniformBits n).bind fun key => evaluateOracle (adversary n [])
    (fun query => if query.length = n then family key query else [])

/-- The ideal experiment samples one entire uniform function from `n` bits to `n` bits and
reuses it across all adaptive calls. This is a probability specification; a lazy cache in the
implementation realizes the same law without constructing its exponential truth table.
Malformed queries are rejected in exactly the same way as in the real experiment. -/
noncomputable def idealPRF (adversary : ℕ → List Bool → OracleProgram Bool) (n : ℕ) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype ((Fin n → Bool) → Fin n → Bool)).bind
    fun table => evaluateOracle (adversary n []) (fun query =>
      if query.length = n then List.ofFn (table fun i => query.getD i.val false) else [])

/-- A uniform adaptive pseudorandom function family has a deterministic polynomial-time keyed
evaluator, `n`-bit answers to valid `n`-bit queries under `n`-bit keys, and negligible advantage
between the preceding games for every one strict uniform adaptive oracle-PPT adversary. -/
def PseudorandomFunction (family : List Bool → List Bool → List Bool) : Prop :=
  PolyTime (fun p : List Bool × List Bool => family p.1 p.2)
    (pairEncoding bitsEncoding bitsEncoding) bitsEncoding ∧
  (∀ key query, query.length = key.length → (family key query).length = key.length) ∧
  ∀ adversary : ℕ → List Bool → OracleProgram Bool, OraclePPT adversary →
    Negligible (fun n => nndist (probability (realPRF family adversary n))
      (probability (idealPRF adversary n)))

/-- **One-way functions imply adaptive pseudorandom functions:** HILL, polynomial stretching
and the Goldreich–Goldwasser–Micali tree construction give an efficient family satisfying the
full adaptive contract above. No fixed query-list restriction or nonuniform advice is assumed. -/
theorem adaptive_functions {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ family : List Bool → List Bool → List Bool, PseudorandomFunction family :=
  CryptographyBridge.adaptive_functions hf

/--
info: abstract audit passed for `ComplexityTests.Abstracts.CryptographyAbstract`: 33 root
declarations, 254 dependencies checked
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.CryptographyAbstract allowing [
  Complexity.Languages.Probabilistic.Basic,
  Complexity.Languages.Probabilistic.Oracle,
  Complexity.Computability.Machines.Turing.MultiTape.Machine,
  Complexity.Computability.Machines.Turing.MultiTape.Machine.Program,
  Complexity.Computability.Machines.Turing.MultiTape.Probabilistic,
  Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Oracle
]

/--
info: 'ComplexityTests.Abstracts.CryptographyAbstract.hill' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexityTests.Abstracts.CryptographyAbstract.hill

/--
info: 'ComplexityTests.Abstracts.CryptographyAbstract.adaptive_functions' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexityTests.Abstracts.CryptographyAbstract.adaptive_functions

end ComplexityTests.Abstracts.CryptographyAbstract
