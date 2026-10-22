/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.Classes.IP
public import Complexity.Computability.Complexity.Classes.IP.Shamir
import Complexity.Computability.Probabilistic.Oracle.Composition

/-!
# Multiprover interactive proofs (`MIP₂` and `MIP`)

In a multiprover interactive proof system [Ben-Or, Goldwasser, Kilian and Wigderson][BGKW1988],
[Babai, Fortnow and Lund][BabaiFortnowLund1991], [Arora and Barak, Section 8.10][AroraBarak09],
a probabilistic polynomial-time verifier exchanges messages with $k$ all-powerful provers that
**cannot communicate** with one another during the protocol: when the verifier sends a message $m$
to prover $i$, only prover $i$ sees $m$ and updates its internal state, while every other prover
$j \ne i$ keeps its state unchanged (`Cslib.Complexity.Prover.independent`,
`Cslib.Complexity.Prover.independent_state_eq_of_ne`).

A verifier with prover index type `ι` is a program `α → WordOracleComp ι Bool`, realized with a
strict polynomial clock against every stateful oracle (`Cslib.Probability.IsOraclePPTOn`). Each
external call `ProbOracleComp.query (i, message)` addresses one named prover `i : ι`. The classes
`Cslib.Complexity.MIP₂` (two non-communicating provers, `Fin 2`) and `Cslib.Complexity.MIP`
(finitely many non-communicating provers, `Fin p` for some `p : ℕ`) use completeness `2 / 3` and
soundness `1 / 3` against all independent prover families `P : ι → Prover Unit`.

Embedding a single-prover verifier on one selected channel (`Turing.MultiTapePTM.singleOracle`,
`Cslib.Probability.WordOracleComp.singleOracle`) preserves `IsOraclePPTOn` and acceptance
probabilities against `Prover.independent P`, giving `IP ⊆ MIP₂ ⊆ MIP` and hence
`PSPACE ⊆ MIP₂ ⊆ MIP`, `PH ⊆ MIP`, `NP ⊆ MIP`, `coNP ⊆ MIP`, `BPP ⊆ MIP`, and `P ⊆ MIP`.

## Main definitions

* `Cslib.Complexity.Prover.independent`: combine a family of non-communicating provers
  `ι → Prover Unit` into a `Prover ι` with product state `∀ i, (P i).State`.
* `Cslib.Complexity.IsMultiproverProof`: completeness and soundness against independent prover
  families `ι → Prover Unit`.
* `Cslib.Complexity.MIP₂`: two-prover interactive proofs with completeness `2 / 3` and soundness
  `1 / 3`.
* `Cslib.Complexity.MIP`: multiprover interactive proofs over `Fin p` provers.
* `Cslib.Complexity.MIPHard`, `Cslib.Complexity.MIPComplete`: hardness and completeness under
  polynomial-time many-one reductions.

## Main results

* `Cslib.Complexity.Prover.independent_state_eq_of_ne`: querying prover `i` leaves every other
  prover's state unchanged.
* `Cslib.Complexity.IP_subset_MIP₂`, `Cslib.Complexity.MIP₂_subset_MIP`,
  `Cslib.Complexity.IP_subset_MIP`: single-prover interactive proofs embed into `MIP₂` and `MIP`.
* `Cslib.Complexity.PSPACE_subset_MIP₂`, `Cslib.Complexity.PSPACE_subset_MIP`,
  `Cslib.Complexity.PH_subset_MIP`, `Cslib.Complexity.NP_subset_MIP`,
  `Cslib.Complexity.coNP_subset_MIP`, `Cslib.Complexity.BPP_subset_MIP`,
  `Cslib.Complexity.P_subset_MIP`.
* `Cslib.Complexity.PolyTimeReducible.mem_MIP₂`, `Cslib.Complexity.PolyTimeReducible.mem_MIP`:
  closure under polynomial-time reductions.

## References

* [L. Babai, L. Fortnow, C. Lund, *Non-deterministic exponential time has two-prover interactive
  protocols*][BabaiFortnowLund1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 8.10][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability MultiTapeMachine

variable {k : ℕ} {Symbol State ι OracleState : Type} [DecidableEq ι]

/-- Embed a single-channel fair-coin machine on channel `i₀ : ι`, leaving all other channels
unused. -/
def singleOracle (i₀ : ι) (machine : MultiTapePTM k Symbol State Unit) :
    MultiTapePTM k Symbol State ι where
  initial := machine.initial
  tr state symbol work answer bit :=
    match machine.tr state symbol work (fun _ => answer i₀) bit with
    | .step action qSym aMove =>
      .step action (fun j => if j = i₀ then qSym () else none)
        (fun j => if j = i₀ then aMove () else 0)
    | .query _ next => .query i₀ next

/-- Configuration embedding placing the single channel on `i₀` and empty channels elsewhere. -/
def embedSingleConfig {input : List Symbol} (i₀ : ι)
    (cfg : Config k Symbol State Unit input) : Config k Symbol State ι input where
  tapes := cfg.tapes
  channels j := if j = i₀ then cfg.channels () else {}

@[simp]
theorem embedSingleConfig_tapes {input : List Symbol} (i₀ : ι)
    (cfg : Config k Symbol State Unit input) :
    (embedSingleConfig i₀ cfg).tapes = cfg.tapes := rfl

@[simp]
theorem embedSingleConfig_initial (i₀ : ι) (machine : MultiTapePTM k Symbol State Unit)
    (input : List Symbol) :
    embedSingleConfig i₀ (machine.initialConfig input) =
      (machine.singleOracle i₀).initialConfig input := by
  refine Config.ext rfl (funext fun j => ?_)
  simp only [embedSingleConfig, initialConfig, ite_self]

@[simp]
theorem embedSingleConfig_answerSymbols {input : List Symbol} (i₀ : ι)
    (cfg : Config k Symbol State Unit input) :
    (embedSingleConfig i₀ cfg).answerSymbols i₀ = cfg.answerSymbols () := by
  simp only [Config.answerSymbols, embedSingleConfig, ↓reduceIte]

theorem embedSingleConfig_step {input : List Symbol} (i₀ : ι)
    (cfg : Config k Symbol State Unit input) (action : Turing.Action k Symbol State)
    (qSym : Unit → Option Symbol) (aMove : Unit → SignType) :
    (embedSingleConfig i₀ cfg).step action
      (fun j => if j = i₀ then qSym () else none)
      (fun j => if j = i₀ then aMove () else 0) =
      embedSingleConfig i₀ (cfg.step action qSym aMove) := by
  refine Config.ext rfl (funext fun j => ?_)
  by_cases hj : j = i₀
  · subst hj
    simp only [Config.step, embedSingleConfig, ↓reduceIte]
  · simp only [Config.step, embedSingleConfig, hj, ↓reduceIte, Option.toList_none,
      List.append_nil, SignType.coe_zero, add_zero]

theorem embedSingleConfig_receive {input : List Symbol} (i₀ : ι)
    (cfg : Config k Symbol State Unit input) (next : State) (answer : List Symbol) :
    (embedSingleConfig i₀ cfg).receive i₀ next answer =
      embedSingleConfig i₀ (cfg.receive () next answer) := by
  refine Config.ext rfl (funext fun j => ?_)
  by_cases hj : j = i₀
  · subst hj
    simp only [Config.receive, embedSingleConfig, Function.update_self, ↓reduceIte]
  · simp only [Config.receive, embedSingleConfig, Function.update_of_ne hj, hj, ↓reduceIte]

/-- Running `singleOracle i₀ machine` forwards every query `((), word)` to `(i₀, word)`. -/
theorem runOracle_singleOracle (i₀ : ι) (machine : MultiTapePTM k Symbol State Unit)
    (fuel : ℕ) (input : List Symbol) :
    (machine.singleOracle i₀).runOracle fuel input =
      OracleComp.interpret
        (ProbOracleComp.handler
          (fun n => OracleComp.query
            (spec := probOracleSpec (fun _ : ι × List Symbol => List Symbol)) (Sum.inl n))
          (fun q : Unit × List Symbol =>
            ProbOracleComp.query
              (spec := fun _ : ι × List Symbol => List Symbol) (i₀, q.2)))
        (machine.runOracle fuel input) := by
  have hsim := MultiTapeMachine.runConfigFrom_map machine (machine.singleOracle i₀)
    (fun choices => choices <$> ProbOracleComp.sample
      (spec := fun _ : ι × List Symbol => List Symbol) (ProbComp.uniform Bool))
    (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun _ word => ProbOracleComp.query
      (spec := fun _ : ι × List Symbol => List Symbol) (i₀, word))
    (fun op word => ProbOracleComp.query (op, word))
    (embedSingleConfig i₀)
    (fun cfg => by
      cases hs : cfg.tapes.state with
      | none =>
        simp only [MultiTapeMachine.runConfigFrom, embedSingleConfig, hs, map_pure]
      | some state =>
        have hanswer : (fun _ : Unit => (embedSingleConfig i₀ cfg).answerSymbols i₀) =
            cfg.answerSymbols := by
          funext u
          cases u
          exact embedSingleConfig_answerSymbols i₀ cfg
        have hch : ((embedSingleConfig i₀ cfg).channels i₀).queryBuffer =
            (cfg.channels ()).queryBuffer := by
          simp only [embedSingleConfig, ↓reduceIte]
        simp only [MultiTapeMachine.runConfigFrom, embedSingleConfig_tapes, hs, bind_map_left,
          map_bind]
        congr 1
        funext bit
        simp only [singleOracle, hanswer]
        cases htr : machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
            cfg.answerSymbols bit with
        | step action symbol move =>
          simp only [map_pure, embedSingleConfig_step]
        | query oracle next =>
          cases oracle
          simp only [hch, bind_pure_comp, Functor.map_map, embedSingleConfig_receive])
    fuel (machine.initialConfig input)
  calc (machine.singleOracle i₀).runOracle fuel input
      = (fun final => final.tapes.output) <$> MultiTapeMachine.runConfigFrom
          (machine.singleOracle i₀)
          (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
          (fun op word => ProbOracleComp.query (op, word)) fuel
          (embedSingleConfig i₀ (machine.initialConfig input)) := by
        rw [embedSingleConfig_initial]; rfl
    _ = (fun final => final.tapes.output) <$> MultiTapeMachine.runConfigFrom machine
          (fun choices => choices <$> ProbOracleComp.sample
            (spec := fun _ : ι × List Symbol => List Symbol) (ProbComp.uniform Bool))
          (fun _ word => ProbOracleComp.query (i₀, word)) fuel
          (machine.initialConfig input) := by
        rw [hsim, Functor.map_map]; rfl
    _ = _ := by
        simp only [runOracle, run, runFrom, runConfigFrom,
          OracleComp.interpret_map, MultiTapeMachine.interpret_runConfigFrom,
          ProbOracleComp.interpret_sample, ProbOracleComp.interpret_query]
        rfl

end Turing.MultiTapePTM

namespace Cslib.Probability

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM

variable {ι α β : Type}

/-- Route all word-oracle queries of a single-channel program to channel `i₀ : ι`. -/
def WordOracleComp.singleOracle (i₀ : ι) (p : WordOracleComp Unit α) :
    WordOracleComp ι α :=
  OracleComp.interpret
    (ProbOracleComp.handler
      (fun n => OracleComp.query
        (spec := probOracleSpec (fun _ : ι × List Bool => List Bool)) (Sum.inl n))
      (fun q : Unit × List Bool =>
        ProbOracleComp.query (spec := fun _ : ι × List Bool => List Bool) (i₀, q.2)))
    p

theorem WordOracleComp.singleOracle_map (i₀ : ι) (f : α → β) (p : WordOracleComp Unit α) :
    WordOracleComp.singleOracle i₀ (f <$> p) = f <$> WordOracleComp.singleOracle i₀ p :=
  OracleComp.interpret_map _ _ _

/-- Interpreting `WordOracleComp.singleOracle i₀ p` against `oracle` is equivalent to interpreting
`p` against `fun q => oracle (i₀, q.2)`. -/
theorem WordOracleComp.run_interpret_singleOracle {State : Type} (i₀ : ι)
    (oracle : ι × List Bool → StateT State PMF (List Bool)) (p : WordOracleComp Unit α)
    (s : State) :
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (WordOracleComp.singleOracle i₀ p)).run s =
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n))
        (fun q : Unit × List Bool => oracle (i₀, q.2))) p).run s := by
  rw [WordOracleComp.singleOracle, OracleComp.interpret_interpret]
  congr 2
  funext q
  cases q <;> simp only [ProbOracleComp.handler, ProbOracleComp.query, OracleComp.interpret_query]

/-- Routing a strict oracle-PPT single-channel program to channel `i₀ : ι` preserves
`IsOraclePPTOn`. -/
theorem IsOraclePPTOn.singleOracle [DecidableEq ι] [Finite ι] (i₀ : ι)
    {input : α ↪ List Bool} {output : β ↪ List Bool} {program : α → WordOracleComp Unit β}
    (h : IsOraclePPTOn input output program) :
    IsOraclePPTOn input output (fun a => WordOracleComp.singleOracle i₀ (program a)) := by
  obtain ⟨_, k, Control, hfinite, machine, c, d, h⟩ := h
  refine ⟨inferInstance, k, Control, hfinite, machine.singleOracle i₀, c, d,
    fun a State oracle s => ?_⟩
  rw [← WordOracleComp.singleOracle_map, WordOracleComp.run_interpret_singleOracle,
    MultiTapePTM.runOracle_singleOracle, ← WordOracleComp.singleOracle,
    WordOracleComp.run_interpret_singleOracle]
  exact h a State (fun q => oracle (i₀, q.2)) s

end Cslib.Probability

namespace Cslib.Complexity

open Cslib.Probability Turing.MultiTapeTM
open scoped ENNReal

variable {ι α β : Type} [DecidableEq ι]

/-! ### Non-communicating prover families -/

namespace Prover

/-- Combine a family of individual provers `P : ι → Prover Unit` into a non-communicating
multiprover strategy `Prover ι`: each prover `i` keeps its own private state `(P i).State`, and a
query `(i, msg)` updates only prover `i`'s state while leaving every other prover's state
unchanged. -/
noncomputable abbrev independent (P : ι → Prover Unit) : Prover ι where
  State := ∀ i, (P i).State
  init i := (P i).init
  respond q := StateT.mk fun s =>
    (((P q.1).respond ((), q.2)).run (s q.1)).map fun x =>
      (x.1, Function.update s q.1 x.2)

@[simp]
theorem independent_init (P : ι → Prover Unit) (i : ι) :
    (independent P).init i = (P i).init := rfl

/-- **Non-communication (state isolation)**: when prover `q.1` responds to query `q`, the state of
every other prover `j ≠ q.1` is unchanged in every supported transition. -/
theorem independent_state_eq_of_ne (P : ι → Prover Unit) (q : ι × List Bool)
    (s s' : (independent P).State) (reply : List Bool) {j : ι} (hne : j ≠ q.1)
    (hmem : (reply, s') ∈ (((independent P).respond q).run s).support) :
    s' j = s j := by
  change (reply, s') ∈ ((((P q.1).respond ((), q.2)).run (s q.1)).map fun x =>
    (x.1, Function.update s q.1 x.2)).support at hmem
  obtain ⟨⟨r, si'⟩, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
  have hs' : Function.update s q.1 si' = s' := (Prod.mk.inj heq).2
  exact (congrFun hs' j).symm.trans (Function.update_of_ne hne si' s)

/-- Projecting the joint state of `independent P` onto coordinate `i₀` commutes with running a
program that only queries prover `i₀`. -/
theorem run_singleOracle_independent (P : ι → Prover Unit) (i₀ : ι)
    (p : WordOracleComp Unit α) (s : ∀ i, (P i).State) :
    ((independent P).run (WordOracleComp.singleOracle i₀ p) s).map
      (Prod.map id (fun s' => s' i₀)) =
      (P i₀).run p (s i₀) := by
  rw [Prover.run, WordOracleComp.run_interpret_singleOracle, Prover.run]
  induction p using PFunctor.FreeM.induction generalizing s with
  | pure a =>
    simp only [OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.pure_map, Prod.map_apply, id_eq]
  | lift_bind q cont ih =>
    rw [show (PFunctor.FreeM.lift q).bind cont = OracleComp.query q >>= cont from rfl]
    simp only [OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, PMF.map_bind]
    cases q with
    | inl n =>
      change ((ProbComp.unifOracle n).map (·, s)).bind _ =
        ((ProbComp.unifOracle n).map (·, s i₀)).bind _
      rw [PMF.bind_map, PMF.bind_map]
      congr 1
      funext bit
      exact ih bit s
    | inr q =>
      obtain ⟨⟨⟩, msg⟩ := q
      change (((P i₀).respond ((), msg) (s i₀)).map
          (fun x => (x.1, Function.update s i₀ x.2))).bind _ =
        (((P i₀).respond ((), msg) (s i₀))).bind _
      rw [PMF.bind_map]
      congr 1
      funext x
      simpa only [Function.comp_apply, Function.update_self] using
        ih x.1 (Function.update s i₀ x.2)

/-- A single-channel verifier routed to prover `i₀` has the exact same acceptance probability
against `independent P` as the original verifier against `P i₀`. -/
theorem acceptProb_singleOracle_independent (P : ι → Prover Unit) (i₀ : ι)
    (p : WordOracleComp Unit Bool) :
    acceptProb (WordOracleComp.singleOracle i₀ p) (independent P) =
      acceptProb p (P i₀) := by
  have h := congrArg (PMF.map Prod.fst)
    (run_singleOracle_independent P i₀ p (independent P).init)
  have hcomp : Prod.fst ∘ Prod.map (id : Bool → Bool) (fun s' : (independent P).State => s' i₀) =
      Prod.fst := rfl
  simp only [PMF.map_comp, hcomp] at h
  exact congrFun (congrArg DFunLike.coe h) true

end Prover

/-! ### Multiprover interactive proofs and the classes `MIP₂` and `MIP` -/

/-- `verifier` is a multiprover interactive proof for `A` with completeness `c` and soundness `s`
over prover index type `ι` when on every member of `A` some independent prover family is accepted
with probability at least `c`, and on every non-member no independent prover family is accepted
with probability more than `s` [Babai, Fortnow and Lund][BabaiFortnowLund1991],
[Arora and Barak, Section 8.10][AroraBarak09]. -/
structure IsMultiproverProof (verifier : α → WordOracleComp ι Bool) (A : Set α)
    (completeness soundness : ℝ≥0∞) : Prop where
  /-- On every member of `A`, some family of non-communicating provers is accepted with
  probability at least `completeness`. -/
  complete : ∀ a ∈ A, ∃ P : ι → Prover Unit,
    completeness ≤ acceptProb (verifier a) (Prover.independent P)
  /-- On every non-member of `A`, every family of non-communicating provers is accepted with
  probability at most `soundness`. -/
  sound : ∀ a ∉ A, ∀ P : ι → Prover Unit,
    acceptProb (verifier a) (Prover.independent P) ≤ soundness

namespace IsMultiproverProof

variable {verifier : α → WordOracleComp ι Bool} {A : Set α} {B : Set β} {c c' s s' : ℝ≥0∞}

theorem mono (h : IsMultiproverProof verifier A c s) (hc : c' ≤ c) (hs : s ≤ s') :
    IsMultiproverProof verifier A c' s' where
  complete a ha :=
    let ⟨P, hP⟩ := h.complete a ha
    ⟨P, hc.trans hP⟩
  sound a ha P := (h.sound a ha P).trans hs

/-- Pull a multiprover interactive proof back along a reduction. -/
theorem comp {verifier : β → WordOracleComp ι Bool} (h : IsMultiproverProof verifier B c s)
    {f : α → β} (hf : ∀ a, a ∈ A ↔ f a ∈ B) :
    IsMultiproverProof (fun a => verifier (f a)) A c s where
  complete a ha := h.complete (f a) ((hf a).1 ha)
  sound a ha := h.sound (f a) fun hb => ha ((hf a).2 hb)

end IsMultiproverProof

/-- Embedding a single-prover interactive proof on channel `i₀ : ι` yields a multiprover
interactive proof with the same completeness and soundness. -/
theorem IsInteractiveProof.isMultiproverProof_singleOracle (i₀ : ι)
    {verifier : α → WordOracleComp Unit Bool} {A : Set α} {c s : ℝ≥0∞}
    (h : IsInteractiveProof verifier A c s) :
    IsMultiproverProof (fun a => WordOracleComp.singleOracle i₀ (verifier a)) A c s where
  complete a ha := by
    obtain ⟨P₀, hP₀⟩ := h.complete a ha
    refine ⟨fun _ => P₀, ?_⟩
    rwa [Prover.acceptProb_singleOracle_independent]
  sound a ha P := by
    rw [Prover.acceptProb_singleOracle_independent]
    exact h.sound a ha (P i₀)

/-- **Two-prover interactive proofs (`MIP₂`)**, with respect to the encoding `enc` of instances:
the problems with a two-prover interactive proof (`Fin 2`) whose verifier is strict oracle PPT
(`Cslib.Probability.IsOraclePPTOn`), with completeness `2 / 3` and soundness `1 / 3`
[Babai, Fortnow and Lund][BabaiFortnowLund1991]. -/
def MIP₂ (enc : α ↪ List Bool) : Set (Set α) :=
  {A : Set α | ∃ verifier : α → WordOracleComp (Fin 2) Bool,
    IsOraclePPTOn enc encBool verifier ∧
    IsMultiproverProof verifier A (2 / 3) (1 / 3)}

/-- **Multiprover interactive proofs (`MIP`)**, with respect to the encoding `enc` of instances:
the problems with a `p`-prover interactive proof (`Fin p` for some `p : ℕ`) whose verifier is
strict oracle PPT, with completeness `2 / 3` and soundness `1 / 3`
[Ben-Or, Goldwasser, Kilian and Wigderson][BGKW1988],
[Babai, Fortnow and Lund][BabaiFortnowLund1991],
[Arora and Barak, Section 8.10][AroraBarak09]. -/
def MIP (enc : α ↪ List Bool) : Set (Set α) :=
  {A : Set α | ∃ (p : ℕ) (verifier : α → WordOracleComp (Fin p) Bool),
    IsOraclePPTOn enc encBool verifier ∧
    IsMultiproverProof verifier A (2 / 3) (1 / 3)}

/-- Hardness for `MIP` under polynomial-time many-one reductions. -/
abbrev MIPHard (enc : α ↪ List Bool) (B : Set α) : Prop :=
  PolyTimeHard MIP enc B

/-- Completeness for `MIP` under polynomial-time many-one reductions. -/
abbrev MIPComplete (enc : α ↪ List Bool) (B : Set α) : Prop :=
  PolyTimeComplete MIP enc B

/-! ### Closure under reductions and basic inclusions -/

/-- **`MIP₂` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_MIP₂ {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} (hred : PolyTimeReducible encA encB A B) (hB : B ∈ MIP₂ encB) :
    A ∈ MIP₂ encA := by
  obtain ⟨f, hf, hAB⟩ := hred
  obtain ⟨V, hV, hproof⟩ := hB
  exact ⟨fun a => V (f a), hV.preprocess hf, hproof.comp hAB⟩

/-- **`MIP` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_MIP {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} (hred : PolyTimeReducible encA encB A B) (hB : B ∈ MIP encB) :
    A ∈ MIP encA := by
  obtain ⟨f, hf, hAB⟩ := hred
  obtain ⟨p, V, hV, hproof⟩ := hB
  exact ⟨p, fun a => V (f a), hV.preprocess hf, hproof.comp hAB⟩

/-- **`IP ⊆ MIP₂`**: a single-prover interactive proof uses the first of two provers (`0 : Fin 2`)
and ignores the second. -/
theorem IP_subset_MIP₂ (enc : α ↪ List Bool) : IP enc ⊆ MIP₂ enc := by
  rintro A ⟨V, hV, hA⟩
  exact ⟨fun a => WordOracleComp.singleOracle (0 : Fin 2) (V a),
    hV.singleOracle 0, hA.isMultiproverProof_singleOracle 0⟩

/-- **`MIP₂ ⊆ MIP`**: a two-prover interactive proof is a `p`-prover interactive proof with
`p = 2`. -/
theorem MIP₂_subset_MIP (enc : α ↪ List Bool) : MIP₂ enc ⊆ MIP enc := by
  rintro A ⟨V, hV, hA⟩
  exact ⟨2, V, hV, hA⟩

/-- **`IP ⊆ MIP`**. -/
theorem IP_subset_MIP (enc : α ↪ List Bool) : IP enc ⊆ MIP enc :=
  (IP_subset_MIP₂ enc).trans (MIP₂_subset_MIP enc)

/-- **`PSPACE ⊆ MIP₂`** [Shamir][Shamir1992]. -/
theorem PSPACE_subset_MIP₂ (enc : α ↪ List Bool) : PSPACE enc ⊆ MIP₂ enc :=
  (PSPACE_subset_IP enc).trans (IP_subset_MIP₂ enc)

/-- **`PSPACE ⊆ MIP`** [Shamir][Shamir1992]. -/
theorem PSPACE_subset_MIP (enc : α ↪ List Bool) : PSPACE enc ⊆ MIP enc :=
  (PSPACE_subset_MIP₂ enc).trans (MIP₂_subset_MIP enc)

/-- **`NP ⊆ MIP₂`**. -/
theorem NP_subset_MIP₂ (enc : α ↪ List Bool) : NP enc ⊆ MIP₂ enc :=
  (NP_subset_IP enc).trans (IP_subset_MIP₂ enc)

/-- **`NP ⊆ MIP`**. -/
theorem NP_subset_MIP (enc : α ↪ List Bool) : NP enc ⊆ MIP enc :=
  (NP_subset_MIP₂ enc).trans (MIP₂_subset_MIP enc)

/-- **`BPP ⊆ MIP₂`**. -/
theorem BPP_subset_MIP₂ (enc : α ↪ List Bool) : BPP enc ⊆ MIP₂ enc :=
  (BPP_subset_IP enc).trans (IP_subset_MIP₂ enc)

/-- **`BPP ⊆ MIP`**. -/
theorem BPP_subset_MIP (enc : α ↪ List Bool) : BPP enc ⊆ MIP enc :=
  (BPP_subset_MIP₂ enc).trans (MIP₂_subset_MIP enc)

/-- **`PH ⊆ MIP₂`**. -/
theorem PH_subset_MIP₂ (enc : α ↪ List Bool) : PH enc ⊆ MIP₂ enc :=
  (PH_subset_IP enc).trans (IP_subset_MIP₂ enc)

/-- **`PH ⊆ MIP`**. -/
theorem PH_subset_MIP (enc : α ↪ List Bool) : PH enc ⊆ MIP enc :=
  (PH_subset_MIP₂ enc).trans (MIP₂_subset_MIP enc)

/-- **`coNP ⊆ MIP₂`**. -/
theorem coNP_subset_MIP₂ (enc : α ↪ List Bool) : coNP enc ⊆ MIP₂ enc :=
  (coNP_subset_IP enc).trans (IP_subset_MIP₂ enc)

/-- **`coNP ⊆ MIP`**. -/
theorem coNP_subset_MIP (enc : α ↪ List Bool) : coNP enc ⊆ MIP enc :=
  (coNP_subset_MIP₂ enc).trans (MIP₂_subset_MIP enc)

/-- **`P ⊆ MIP₂`**. -/
theorem P_subset_MIP₂ (enc : α ↪ List Bool) : P enc ⊆ MIP₂ enc :=
  P_subset_NP.trans (NP_subset_MIP₂ enc)

/-- **`P ⊆ MIP`**. -/
theorem P_subset_MIP (enc : α ↪ List Bool) : P enc ⊆ MIP enc :=
  (P_subset_MIP₂ enc).trans (MIP₂_subset_MIP enc)

end Cslib.Complexity
