# Mission and design

Complexitylib makes complexity-theoretic arguments compositional: from algorithms and
computational models through resource bounds, reductions, lower bounds, and cryptographic
security. It is a unified Lean library built on CSLib and Mathlib.

The intended reader should be able to formalize a complexity argument, implement a construction
with a certified resource bound, or reuse the mathematics supporting either. Clear functional
programs and efficient proof automation are central tools for that work. Nonconstructive
mathematics, counting arguments, and model-specific lower bounds also have a natural place.

These are design commitments to test against real developments. The
[library guide](LIBRARY.md) describes the current implementation and its boundaries.

## What belongs

A development should establish a meaningful complexity result, supply infrastructure used by
such results, or make those results easier to state and prove. Shared mathematics belongs at the
level where its assumptions and consumers fit: for example, a general probability identity in
the probability API, or an arithmetic circuit bound beside other circuit bounds.

Build on the existing computational models and semantic interfaces. Introduce a new model when
its expressive or resource distinction matters, and provide the relevant connections to existing
models. Generic abstractions should simplify concrete clients; specialized proofs can motivate
them before their full generality is clear.

CSLib compatibility is a structural commitment. Modules use their intended upstream paths,
namespaces, and conventions, with `Complexity.` as the local import prefix. Acceptance upstream
remains a separate review decision.

## The program experience

Programs should read as ordinary functional expressions or typed `do` programs. Clients state
what values mean and supply the substantive invariant. Shared certificates handle supported
operations, composition, representation conversion, and routine size arithmetic.

Efficiency claims retain their computational content: the input and output encodings, uniform
machine, clock, storage bounds, and distributional semantics must support the stated theorem.
Simulation must account for computation, copying, queries, replies, and state growth. Stateful
probabilistic transformations preserve the joint output and final private-state distribution.

Use `fun_prop`, `polytime`, `ppt`, and narrowly oriented simplification as public APIs. Ordinary
equivalent expressions should work predictably. Recurring manual work is evidence to examine
the statement or interface before extending tactic syntax. Clients still supply meaningful loop
invariants, growth bounds, and algorithm-specific arguments.

New hand-written machine constructions belong where a shared primitive or new computational
capability requires them. A new reduction should normally compose existing certificates.

## State exactly what is proved

Keep mathematical correctness, an executable definition, a certified resource bound, and
practical performance distinguishable. A development may provide any useful combination, with
its claims stated precisely. Polynomial output size alone does not certify polynomial running
time; efficient evaluation alone does not establish cryptographic security.

For lower bounds, name the model, basis, cost, uniformity, and representation assumptions. For
constructions, say how the family is selected and which parameters the running time depends on.
Place remaining hypotheses and construction gaps beside the headline result. Credit both the
mathematical sources and the formalizations adapted, distinguishing published results from new
arguments and unformalized observations.

## Judge interfaces by their clients

Three representative developments exercise different parts of the design:

* **Cook–Levin:** a recognizable reduction, compositional efficiency proof, and an unconditional
  completeness theorem under the stated model of reduction.
* **Adaptive GGM:** functional sampling and cache operations, preservation of joint state,
  and a complete efficient security reduction.
* **Circuit lower bounds:** shared syntax and costs, useful general lemmas, and theorem
  statements that expose the exact mathematical and model assumptions.

Executable PCP constructions and general OWF → PRG are demanding next clients for these same
interfaces. Existing clients should become easier as the shared APIs improve.

Measure total proof burden, including new helper lemmas and proof fields, alongside elaboration
cost. Small client proofs are useful when their abstractions remain readable, reusable, and
predictable. Report the comparison's scope and retain tests for non-vacuity and important failure
cases. Independent API and correctness reviews complement Lean's checking.

## A consistent documentation pattern

For each major development, explain:

1. What can a reader state or build with it?
2. Which precise results are proved, under which assumptions?
3. Which imports and checked examples show how to use it?
4. Which relevant bridges, constructions, or guarantees remain open?

The [README](../README.md) introduces the purpose and routes readers to tasks. Guides teach
working patterns; the [library guide](LIBRARY.md) selects entry points and theorem statements;
module docstrings provide definitions, assumptions, results, and references. Keep example code
in sync with checked clients and validate it with the imports shown.

[CONTRIBUTING.md](../CONTRIBUTING.md) explains contribution quality and validation.
[ROADMAP.md](../ROADMAP.md) retains implementation plans, measurements, and development history;
[UPSTREAM.md](../UPSTREAM.md) tracks upstream integration. Update the relevant reader-facing
guide when a capability or theorem boundary changes.
