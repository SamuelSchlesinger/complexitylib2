/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (design prototype for #643; not for merge)

public import Complexity.Computability.Interactive.Security
import Complexity.Probability.PMF

/-!
# The plain model (design prototype)

In the plain model a run is an ordinary probabilistic program: `World.plain.eval` is the
interpretation of the program in `PMF` (`plain_eval`). The main result is that round-by-round
soundness implies soundness with the sum of the per-round errors
(`Verifier.RbrSound.sound`), proved by induction on the rounds against arbitrary prover
strategies, without casts.
-/

@[expose] public section

namespace Cslib.Interactive

open scoped ENNReal
open Spec

/-- The law of a program without external oracles. -/
noncomputable def lawOf {α : Type} (p : ProbOracleComp emptySpec α) : PMF α :=
  OracleComp.interpret (ProbOracleComp.handler ProbComp.unifOracle fun e => e.elim) p

/-- The law of a joint program in the plain model. -/
noncomputable def lawOf₂ {α : Type} (p : ProbOracleComp (emptySpec ⊕ₒ emptySpec) α) : PMF α :=
  OracleComp.interpret (ProbOracleComp.handler ProbComp.unifOracle fun q => match q with
    | .inl e => e.elim
    | .inr e => e.elim) p

theorem plain_eval {α : Type} (p : ProbOracleComp (emptySpec ⊕ₒ emptySpec) α) :
    World.plain.eval p = lawOf₂ p := by
  have h := OracleComp.run_interpret_stateless (m := PMF) (State := Unit)
    (ProbOracleComp.handler ProbComp.unifOracle fun q => match q with
      | .inl e => e.elim
      | .inr e => e.elim) p ()
  have hh : (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n))
      World.plain.impl) =
      fun q s => (fun a => (a, s)) <$> ProbOracleComp.handler ProbComp.unifOracle
        (fun q => match q with
          | .inl e => e.elim
          | .inr e => e.elim) q := by
    funext q s
    rcases q with n | e | e
    · rfl
    · exact e.elim
    · exact e.elim
  unfold World.eval ProbOracleComp.runWith
  erw [hh, h]
  exact (PMF.map_comp _ _ _).trans (PMF.map_id _)

theorem lawOf₂_liftProver {α : Type} (p : ProbOracleComp emptySpec α) :
    lawOf₂ (liftProver (oV := emptySpec) p) = lawOf p := by
  rw [lawOf₂, liftProver, OracleComp.interpret_interpret, lawOf]
  congr 1
  funext q
  rcases q with n | e
  · simp [ProbOracleComp.handler]
  · exact e.elim


@[simp] theorem lawOf_pure {α : Type} (a : α) :
    lawOf (pure a : ProbOracleComp emptySpec α) = PMF.pure a := rfl

@[simp] theorem lawOf_bind {α β : Type} (p : ProbOracleComp emptySpec α)
    (f : α → ProbOracleComp emptySpec β) : lawOf (p >>= f) = (lawOf p).bind fun a => lawOf (f a) :=
  OracleComp.interpret_bind _ _ _

@[simp] theorem lawOf_sample {α : Type} (p : ProbComp α) :
    lawOf (ProbOracleComp.sample (spec := emptySpec) p) = ProbComp.eval p :=
  ProbOracleComp.interpret_sample _ _ _

@[simp] theorem lawOf₂_pure {α : Type} (a : α) :
    lawOf₂ (pure a : ProbOracleComp (emptySpec ⊕ₒ emptySpec) α) = PMF.pure a := rfl

@[simp] theorem lawOf₂_bind {α β : Type} (p : ProbOracleComp (emptySpec ⊕ₒ emptySpec) α)
    (f : α → ProbOracleComp (emptySpec ⊕ₒ emptySpec) β) :
    lawOf₂ (p >>= f) = (lawOf₂ p).bind fun a => lawOf₂ (f a) :=
  OracleComp.interpret_bind _ _ _

/-- The law of a mapped program. -/
@[simp] theorem lawOf₂_map {α β : Type} (f : α → β)
    (p : ProbOracleComp (emptySpec ⊕ₒ emptySpec) α) : lawOf₂ (f <$> p) = (lawOf₂ p).map f :=
  OracleComp.interpret_map _ _ _

/-- A program whose queries are answered deterministically has a point law. -/
theorem interpret_pure_handler {ι : Type} {spec : OracleSpec ι} {α : Type}
    (f : (q : ι) → spec q) (p : OracleComp spec α) :
    OracleComp.interpret (m := PMF) (fun q => PMF.pure (f q)) p =
      PMF.pure (OracleComp.interpret (m := Id) f p) := by
  induction p using PFunctor.FreeM.induction with
  | pure a => rfl
  | lift_bind q cont ih =>
    rw [show (PFunctor.FreeM.lift q).bind cont = OracleComp.query q >>= cont from rfl,
      OracleComp.interpret_bind, OracleComp.interpret_bind, OracleComp.interpret_query,
      OracleComp.interpret_query]
    simp only [Probability.PMF.monad_bind_eq_bind, PMF.pure_bind]
    exact ih (f q)

theorem lawOf₂_output {s : Spec} {StmtIn StmtOut : Type}
    (V : Verifier emptySpec s StmtIn StmtOut)
    (x : StmtIn) (τ : Transcript s) :
    lawOf₂ (V.output (oP := emptySpec) x τ) = PMF.pure (V.outputOn x τ) := by
  rw [lawOf₂, Verifier.output, OracleComp.interpret_interpret, Verifier.outputOn]
  rw [← interpret_pure_handler]
  congr 1
  funext q
  rcases q with e | q
  · exact e.elim
  · rfl


theorem toOuterMeasure_bind_le {α β : Type} (p : PMF α) (f : α → PMF β) (t : Set β)
    {K : ℝ≥0∞} (h : ∀ a, (f a).toOuterMeasure t ≤ K) : (p.bind f).toOuterMeasure t ≤ K := by
  rw [PMF.toOuterMeasure_bind_apply]
  calc ∑' a, p a * (f a).toOuterMeasure t ≤ ∑' a, p a * K :=
        ENNReal.tsum_le_tsum fun a => by gcongr; exact h a
    _ = K := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem toOuterMeasure_bind_pure {α β : Type} (p : PMF α) (g : α → β) (t : Set β) :
    (p.bind fun a => PMF.pure (g a)).toOuterMeasure t = p.toOuterMeasure (g ⁻¹' t) := by
  rw [← PMF.toOuterMeasure_map_apply]
  rfl

/-- From a doomed prefix, the rest of a run wins with probability at most the remaining errors. -/
theorem rbrFrom_le : ∀ (s : Spec) (smp : PerChallenge ProbComp s)
    (ε : PerChallenge (fun _ => ℝ≥0∞) s) (S : Prefix s → Prop) (wins : Transcript s → Prop),
    RbrFrom s smp ε S wins → ¬ S (Prefix.empty s) →
    ∀ {α : Type} (st : ProverStrategy (ProbOracleComp emptySpec) s α),
      (lawOf (runStrategy s smp st)).toOuterMeasure {r | wins r.1} ≤ PerChallenge.sum s ε
  | [], _, _, _, wins, h, hS, _, st => by
    have hw : ¬ wins () := h hS
    simp [runStrategy, hw]
  | .prover M I :: s, smp, ε, S, wins, h, hS, _, st => by
    simp only [runStrategy, lawOf_bind]
    refine toOuterMeasure_bind_le _ _ _ fun p => ?_
    rcases p with ⟨msg, st'⟩
    simp only [lawOf_pure]
    rw [toOuterMeasure_bind_pure]
    exact rbrFrom_le s smp ε (fun p => S (some (msg, p))) (fun τ => wins (msg, τ)) (h.2 msg)
      (h.1 hS msg) st'
  | .verifier C :: s, smp, ε, S, wins, h, hS, _, st => by
    simp only [runStrategy, lawOf_bind, lawOf_sample]
    rw [PMF.toOuterMeasure_bind_apply]
    set A : Set C := {c | S (some (c, Prefix.empty s))}
    have hinner : ∀ c, ((lawOf (st c)).bind fun st' => (lawOf (runStrategy s smp.2 st')).bind
        fun r => lawOf (pure ((c, r.1), r.2))).toOuterMeasure {r | wins r.1} ≤
        A.indicator 1 c + PerChallenge.sum s ε.2 := by
      intro c
      by_cases hc : c ∈ A
      · refine le_trans ?_ le_self_add
        rw [Set.indicator_of_mem hc]
        exact Probability.PMF.toOuterMeasure_le_one _ _
      · rw [Set.indicator_of_notMem hc, zero_add]
        refine toOuterMeasure_bind_le _ _ _ fun st' => ?_
        simp only [lawOf_pure]
        rw [toOuterMeasure_bind_pure]
        exact rbrFrom_le s smp.2 ε.2 (fun p => S (some (c, p))) (fun τ => wins (c, τ)) (h.2 c) hc
          st'
    calc ∑' c, ProbComp.eval smp.1 c * _ ≤
          ∑' c, ProbComp.eval smp.1 c * (A.indicator 1 c + PerChallenge.sum s ε.2) :=
          ENNReal.tsum_le_tsum fun c => by gcongr; exact hinner c
      _ = (ProbComp.eval smp.1).toOuterMeasure A + PerChallenge.sum s ε.2 := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
            PMF.toOuterMeasure_apply]
          congr 1
          refine tsum_congr fun c => ?_
          by_cases hc : c ∈ A <;> simp [hc]
      _ ≤ ε.1 + PerChallenge.sum s ε.2 := by gcongr; exact h.1 hS


/-- **Round-by-round soundness implies soundness**, with the sum of the per-round errors. -/
theorem Verifier.RbrSound.sound {s : Spec} {StmtIn StmtOut : Type}
    {V : Verifier emptySpec s StmtIn StmtOut} {langIn : Set StmtIn}
    {langOut : Set StmtOut} {ε : PerChallenge (fun _ => ℝ≥0∞) s}
    (h : V.RbrSound langIn langOut ε) :
    V.Sound (oP := emptySpec) World.plain langIn langOut (PerChallenge.sum s ε) := by
  obtain ⟨S, hinit, hround⟩ := h
  intro x hx α P
  rw [plain_eval]
  simp only [Verifier.execute, lawOf₂_bind, lawOf₂_liftProver]
  refine toOuterMeasure_bind_le _ _ _ fun st => ?_
  simp only [lawOf₂_output, lawOf₂_pure, PMF.pure_bind]
  rw [toOuterMeasure_bind_pure (g := fun r : Transcript s × α => (r.1, V.outputOn x r.1, r.2))]
  exact rbrFrom_le s V.samplers ε (S x) _ (hround x) (hinit x hx) st

end Cslib.Interactive
