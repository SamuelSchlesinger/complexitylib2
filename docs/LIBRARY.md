# Library guide

Use this guide to find a computational model, a reusable argument, or a theorem to build on.
Imports use `Complexity.`; declaration namespaces generally use `Cslib`, with `Turing` for the
machine calculus. The linked module docstrings give precise definitions and source references.

## Find an entry point

| Task | Entry points |
| --- | --- |
| Certify functional programs | [Program guide](PROGRAMS.md), [deterministic certificates](../Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime.lean), [PPT](../Complexity/Computability/Probabilistic/PPT.lean) |
| Work with complexity classes and reductions | [P](../Complexity/Computability/Complexity/Classes/P.lean), [NP](../Complexity/Computability/Complexity/Classes/NP.lean), [polynomial hierarchy](../Complexity/Computability/Complexity/Classes/PH.lean), [many-one reductions](../Complexity/Computability/Complexity/Reduction.lean) |
| Prove circuit upper or lower bounds | [Supplied-source complexity](../Complexity/Computability/Circuit/SourceComplexity.lean), [simulation](../Complexity/Computability/Circuit/Simulation.lean), [Fusion covers](../Complexity/Computability/Circuit/Fusion/Basic.lean), [arithmetic circuits](../Complexity/Computability/Circuit/Arithmetic.lean) |
| Relate computation to communication and queries | [Communication protocols](../Complexity/Computability/Communication/Protocol.lean), [Karchmer–Wigderson](../Complexity/Computability/Communication/KarchmerWigderson.lean), [decision trees](../Complexity/Computability/DecisionTree/Basic.lean) |
| Formalize cryptographic reductions | [Computational indistinguishability](../Complexity/Crypto/Computational/Basic.lean), [one-way functions](../Complexity/Crypto/Computational/OneWay.lean), [PRGs](../Complexity/Crypto/Computational/PseudorandomGenerator.lean), [PRFs](../Complexity/Crypto/Computational/PseudorandomFunction.lean) |
| Reason about sampling and stateful experiments | [Probabilistic programs](../Complexity/Languages/Probabilistic/Basic.lean), [random oracles](../Complexity/Languages/Probabilistic/RandomOracle.lean), [efficient substitution](../Complexity/Computability/Probabilistic/OracleSimulation.lean) |
| Use probability and information theory | [Statistical distance](../Complexity/Probability/StatisticalDistance.lean), [concentration](../Complexity/Probability/Concentration.lean), [entropy](../Complexity/Probability/Entropy.lean), [universal hashing](../Complexity/Probability/UniversalHash.lean) |
| Use Boolean and algebraic tools | [Fourier analysis](../Complexity/Foundations/BooleanAnalysis/Fourier.lean), [influence](../Complexity/Foundations/BooleanAnalysis/Influence.lean), [quadratic forms](../Complexity/Foundations/Data/BitString/QuadraticForm.lean), [Hessians](../Complexity/Foundations/Data/MvPolynomial/Hessian.lean) |
| Work with graph expansion and PCP | [Rotation maps](../Complexity/Foundations/Combinatorics/Expander/Basic.lean), [arithmetic expanders](../Complexity/Foundations/Combinatorics/Expander/AffineFamily.lean), [constraint graphs](../Complexity/Computability/PCP/ConstraintGraph.lean), [gap amplification](../Complexity/Computability/PCP/Amplification.lean) |
| Study descriptions, truth tables, or logical reductions | [Kolmogorov complexity](../Complexity/Computability/Kolmogorov/Basic.lean), [MCSP](../Complexity/Computability/MCSP/Basic.lean), [first-order reductions](../Complexity/Logics/FirstOrder/Reduction.lean) |

This is a selection of entry points. [Complexity.lean](../Complexity.lean) is the complete import
index. The presence of a definition does not establish every standard characterization: for
example, the MCSP entry defines the semantic problem without claiming a complexity class for an
encoded instance language, and the BPP definition uses deterministic random-string verifiers.

## Cook–Levin: a complete efficient reduction

[CookLevin.Completeness](../Complexity/Computability/Complexity/CookLevin/Completeness.lean)
proves `Cslib.Complexity.CookLevin.SAT_npComplete` and
`Cslib.Complexity.CookLevin.UNSAT_coNPComplete`. The reduction is correct and has a polynomial-time
machine certificate under the library's tidy polynomial-time many-one reductions. No additional
reduction-efficiency hypothesis remains.

Follow [Reduction](../Complexity/Computability/Complexity/CookLevin/Reduction.lean) for the
construction, [Correctness](../Complexity/Computability/Complexity/CookLevin/Correctness.lean)
for its mathematical argument, and
[PolyTime](../Complexity/Computability/Complexity/CookLevin/PolyTime.lean) for compositional
certificates. [CookLevinPolyTime tests](../ComplexityTests/CookLevinPolyTime.lean) exercise the
public interface. The source references include Arora–Barak and Papadimitriou.

## Cryptography: efficient constructions and security reductions

[GoldreichLevin.HardCore](../Complexity/Crypto/Computational/GoldreichLevin/HardCore.lean)
proves the hard-core result and `Cslib.Crypto.OneWayPermutation.pseudorandomGenerator`.
[Stretch](../Complexity/Crypto/Computational/Stretch.lean) supplies polynomial stretch.
[GGM.Security](../Complexity/Crypto/Computational/GGM/Security.lean) proves adaptive security and
`Cslib.Crypto.PseudorandomGenerator.exists_pseudorandomFunction` using strict oracle-PPT
adversaries and one uniform reduction with polynomial loss. These are implications from the
stated cryptographic assumptions.

The [GGM evaluator](../Complexity/Crypto/Computational/GGM/Evaluation.lean) is ordinary functional
code. [GGM tests](../ComplexityTests/GGM.lean) exercise efficient evaluation, memoized state,
and adaptive experiments. Efficiency and security have separate contracts; an efficient example
generator need not be pseudorandom.

For general one-way functions,
[OneWay.exists_pseudoentropyPair](../Complexity/Crypto/Computational/Pseudoentropy/OneWay.lean)
is proved, with normalization, sampling, hashing, and prediction reductions. Pseudoentropy
amplification, extraction, and the final general OWF → PRG assembly remain unfinished.
Consequently, the general OWF → PRF implication is also unfinished. Module references credit
Goldreich–Levin, Goldreich–Goldwasser–Micali, and the other sources used in each reduction.

## Circuits: shared models and precise lower bounds

Boolean, monotone, and arithmetic developments use CSLib's `Signature`, `Program`, and `Circuit`
interfaces. [SourceComplexity](../Complexity/Computability/Circuit/SourceComplexity.lean)
allows designated outputs, supplied inputs, and operation weights. Algebraic results belong
in this circuit hierarchy and reuse its wiring and cost rules.

Representative endpoints show why the exact model matters:

* [Quadratic-form correlation](../Complexity/Computability/Circuit/Frontier/Correlation.lean):
  for every fixed coefficient below the stated threshold, approximately `2.78125`, circuits of
  fan-in at most two over any Boolean basis with at most that coefficient times `n` positive-arity
  gates have exponentially small absolute correlation with the chosen family, for sufficiently
  large `n`. The family is selected nonconstructively; no efficient construction is supplied.
  The general endpoint is `exists_eventually_abs_correlation_hardForm_le_of_lt` in
  `Cslib.Circuits.Frontier`.
* [Bilinear pairing](../Complexity/Computability/Circuit/Arithmetic/Pairing.lean):
  `Cslib.Circuits.Circuit.pairing_le_mulCost` gives a lower bound of `n` multiplications over
  every field, including characteristic two. The computation premise is equality of formal
  polynomials. Constants, additions, and wiring are free; scalar multiplications are charged.
* [Waring representations](../Complexity/Computability/Circuit/Arithmetic/Waring.lean):
  binomial term-count bounds for representing a product of distinct variables as sums of powers
  of linear forms over characteristic-zero fields, with finite-sum and circuit endpoints.
  This is a restricted representation model.
* [Cyclic semifilter bounds](../Complexity/Computability/Circuit/Fusion/Cyclic.lean):
  a forward lower bound for finite feedback systems interpreted by their least fixed point.
  The semantics requires monotonicity on a complete lattice. The converse and a finite
  cover-to-circuit construction remain unfinished; no general iteration-time bound is asserted.

Checked clients include [ArithmeticHessian](../ComplexityTests/ArithmeticHessian.lean),
[ArithmeticWaring](../ComplexityTests/ArithmeticWaring.lean), and
[FusionCyclic](../ComplexityTests/FusionCyclic.lean). The theorem modules give the relevant
literature and formalization provenance.

## PCP and expanders: correctness and constructibility

[Dinur's gap construction](../Complexity/Computability/PCP/GapTheorem.lean) has proved
completeness, soundness, a constant gap, and polynomial vertex and edge cardinalities.
The current pipeline uses nonconstructive choices. The encoded polynomial-time reduction and
the resulting full PCP constructibility theorem remain open.

Separately, [arithmeticExpander](../Complexity/Foundations/Combinatorics/Expander/AffineFamily.lean)
is a computable family on exactly `Fin n`, with a proved constant degree and spectral gap.
[ExplicitExpander tests](../ComplexityTests/ExplicitExpanders.lean) exercise concrete rotations.
Uniform machine certificates for the tower and indexing, encoded preprocessing, and the full
PCP pipeline are still needed. Polynomial time in vertex count can suffice for a polynomial-sized
PCP reduction; time polynomial in the bit length of a vertex name is a stronger target. The
construction's enormous constants also leave practical enumeration as a separate concern.

The modules credit Dinur for gap amplification and Reingold–Vadhan–Wigderson for the expander
construction ingredients, with the formalized scope explained beside each result.

Return to the [README](../README.md) or read the [design standards](DESIGN.md).
