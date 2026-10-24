/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (design prototype for #643; not for merge)

public import Complexity.Computability.Interactive.Security
public import Complexity.Computability.Probabilistic.Parameter
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Efficiency-certified simulators and extractors (design prototype)

The exact notions of the interactive core (`Reduction.HVZK`, `Verifier.KnowledgeSound`) name
their simulator and extractor but place no efficiency requirement on them. Cryptographic
definitions need efficient ones. This layer pairs the exact notions, for a family of reductions
indexed by the security parameter, with certificates in the library's plain contracts:

* a simulator family is *realized* by one uniform strict PPT program on `(1ⁿ, x)` that outputs
  encoded transcripts, up to an explicit statistical error `δ n`
  (`Interactive.SimulatorRealizedBy`). An exact typed sampler need not be strictly realizable, so
  the realization error is part of the statement rather than identified away;
* a straight-line extractor family is *polynomial-time*: it factors through one plain
  polynomial-time function of `(1ⁿ, x, encoded transcript, output witness)`
  (`Interactive.ExtractorIsPolyTime`).

Every encoding is charged: statements, transcripts and witnesses enter the certificates encoded.

## Main definitions

* `Interactive.SimulatorRealizedBy`, `Interactive.ExtractorIsPolyTime`.
* `Interactive.Reduction.CertifiedHVZK`, `Interactive.Verifier.CertifiedKnowledgeSound`.

## Main results

* `Interactive.Reduction.CertifiedHVZK.exists_ppt_simulator`: one uniform strict PPT simulator
  whose encoded output is `ε n + δ n`-close to honest encoded transcripts.
-/

@[expose] public section

namespace Cslib.Interactive

open scoped ENNReal
open Spec Probability Turing.MultiTapeTM

variable {Stmt Wit StmtOut WitOut : Type} {s : ℕ → Spec}

/-- The program `prog` realizes the simulator family `Sim` on encoded outputs, up to statistical
distance `δ n` at security parameter `n`. -/
def SimulatorRealizedBy {T : ℕ → Type} (encT : ∀ n, T n ↪ List Bool)
    (Sim : ∀ n, Stmt → ProbComp (T n)) (prog : ℕ × Stmt → ProbComp (List Bool))
    (δ : ℕ → ℝ≥0∞) : Prop :=
  ∀ n x, CloseTo ((ProbComp.eval (Sim n x)).map (encT n)) (ProbComp.eval (prog (n, x))) (δ n)

/-- A family of straight-line extractors is polynomial-time: it is one plain polynomial-time
function of the unary security parameter, the statement, the encoded transcript and the output
witness. -/
def ExtractorIsPolyTime {WitIn : Type} {T : ℕ → Type} (encStmt : Stmt ↪ List Bool)
    (encT : ∀ n, T n ↪ List Bool) (encOut : WitOut ↪ List Bool) (encIn : WitIn ↪ List Bool)
    (E : ∀ n, Stmt → T n → WitOut → WitIn) : Prop :=
  ∃ f : ℕ × Stmt × List Bool × WitOut → WitIn,
    ComputableInPolyTime f (encPair encUnary (encPair encStmt (encPair encBits encOut))) encIn ∧
      ∀ n x τ w, E n x τ w = f (n, x, encT n τ, w)

/-- **Efficiency-certified honest-verifier zero knowledge.** At every security parameter the
simulator `Sim n` is an exact `ε n` HVZK simulator, and one uniform strict PPT program on
`(1ⁿ, x)` realizes the whole family on encoded transcripts up to `δ n`. -/
structure Reduction.CertifiedHVZK
    (R : ∀ n, Reduction emptySpec emptySpec (s n) Stmt Wit StmtOut WitOut)
    (rel : Stmt → Wit → Prop) (encStmt : Stmt ↪ List Bool)
    (encT : ∀ n, Transcript (s n) ↪ List Bool) (Sim : ∀ n, Stmt → ProbComp (Transcript (s n)))
    (ε δ : ℕ → ℝ≥0∞) : Prop where
  /-- The exact property at every security parameter. -/
  hvzk : ∀ n, (R n).HVZK World.plain rel (Sim n) (ε n)
  /-- A uniform strict PPT realization of the simulator family. -/
  realized : ∃ prog : ℕ × Stmt → ProbComp (List Bool),
    IsPPTOn (encPair encUnary encStmt) encBits prog ∧ SimulatorRealizedBy encT Sim prog δ

/-- A certified HVZK simulator gives one uniform strict PPT program whose encoded output is
`ε n + δ n`-close to the honest encoded transcript, for every valid statement and witness. -/
theorem Reduction.CertifiedHVZK.exists_ppt_simulator
    {R : ∀ n, Reduction emptySpec emptySpec (s n) Stmt Wit StmtOut WitOut}
    {rel : Stmt → Wit → Prop} {encStmt : Stmt ↪ List Bool}
    {encT : ∀ n, Transcript (s n) ↪ List Bool} {Sim : ∀ n, Stmt → ProbComp (Transcript (s n))}
    {ε δ : ℕ → ℝ≥0∞} (h : Reduction.CertifiedHVZK R rel encStmt encT Sim ε δ) :
    ∃ prog : ℕ × Stmt → ProbComp (List Bool),
      IsPPTOn (encPair encUnary encStmt) encBits prog ∧ ∀ n x w, rel x w →
        CloseTo (((World.plain.eval ((R n).run x w)).map Prod.fst).map (encT n))
          (ProbComp.eval (prog (n, x))) (ε n + δ n) := by
  obtain ⟨prog, hppt, hreal⟩ := h.realized
  exact ⟨prog, hppt, fun n x w hxw => ((h.hvzk n x w hxw).map (encT n)).trans (hreal n x)⟩

/-- **Efficiency-certified straight-line knowledge soundness**: the exact property at every
security parameter, with a polynomial-time extractor family. -/
structure Verifier.CertifiedKnowledgeSound {WitIn : Type}
    (V : ∀ n, Verifier emptySpec (s n) Stmt StmtOut) (relIn : Stmt → WitIn → Prop)
    (relOut : StmtOut → WitOut → Prop) (encStmt : Stmt ↪ List Bool)
    (encT : ∀ n, Transcript (s n) ↪ List Bool) (encOut : WitOut ↪ List Bool)
    (encIn : WitIn ↪ List Bool) (E : ∀ n, Stmt → Transcript (s n) → WitOut → WitIn)
    (ε : ℕ → ℝ≥0∞) : Prop where
  /-- The exact property at every security parameter. -/
  knowledgeSound : ∀ n, (V n).KnowledgeSound (oP := emptySpec) World.plain relIn relOut (E n) (ε n)
  /-- The extractor family is polynomial-time on encoded inputs. -/
  efficient : ExtractorIsPolyTime encStmt encT encOut encIn E

end Cslib.Interactive
