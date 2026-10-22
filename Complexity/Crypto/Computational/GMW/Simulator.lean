/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.GMW.PolyTime
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Tactic.PPT

/-!
# Zero-knowledge simulation for the 3-copy GMW protocol

This module proves that for any uniform strict oracle PPT malicious verifier `Vstar` and any
deterministic polynomial-time families of instances `a : ℕ → α`, valid `ThreeSAT` witnesses
`w : ℕ → List Bool` (`∀ n, ThreeSAT.verifier (f (a n), w n) = true`), and auxiliary inputs
`z : ℕ → List Bool`, the output ensemble of `Vstar` interacting with the honest prover `gmwProver`
is computationally indistinguishable from the output ensemble of the witness-free simulator
`gmwSimulator` (`gmwView_indistinguishable_gmwSimulator`).

The proof proceeds through four hybrids on `n + 1` independent challenge-guessing attempts:

1. **Challenge guessing and repetition (`firstSuccess_replicate_game0_indistinguishable`).**
   Each attempt of `game0` guesses a uniform 3-bit challenge `ch_guess` in advance, answers the
   second round using `ch_guess`, and outputs `true :: out` if the verifier's actual challenge
   equals `ch_guess` (occurring with probability `1 / 8` independent of `out`), or `[]` otherwise.
   Repeating `n + 1` times and taking `gmwFirstSuccess` differs from the real view with statistical
   distance at most `(7 / 8) ^ (n + 1)`, which is negligible.
2. **Factoring unopened commitments (`eval_game0Pads_eq_eval_game0`).**
   Using `eval_replicate_naorSelectPads`, we factor the `totalLen (f (a n))` commitment seeds into
   independent active seeds and pseudorandom unopened pads without changing the distribution of each
   attempt.
3. **Replacing pseudorandom unopened pads with uniform pads (`game0_indistinguishable_game1`).**
   By `ComputationallyIndistinguishable.replicate_bind` applied to the shifted PRG ensemble
   `hG.indistinguishable.shift 7`, replacing the `totalLen (f (a n))` pseudorandom unopened pads in
   `game0Pads` by uniform `(length (n + 7))`-bit strings in `game1` is computationally
   indistinguishable.
4. **Eliminating the witness (`eval_game1_eq_eval_gmwSimAttempt`).**
   Once unopened commitment positions use uniform pads (`eval_replicate_map_naorCommitSplit`), the
   commitment transcript depends on the committed bits only through `naorMaskBits openFlags bits`,
   and for any satisfying witness `w n` (`naorMaskBits_realBits`) and uniform masks `m₀, m₁, m₂`
   (`uniformList_bind_ite_listXor_three`), each attempt of `game1` is identically distributed to the
   witness-free `gmwSimAttempt`.

## Main results

* `Cslib.Crypto.GMW.gmwView_indistinguishable_gmwSimulator`: computational indistinguishability
  between the real interaction view of `Vstar` with `gmwProver` and `gmwSimulator`.

## References

* [O. Goldreich, S. Micali, A. Wigderson, *Proofs that Yield Nothing But Their Validity, or All
  Languages in NP Have Zero-Knowledge Proof Systems*][GoldreichMicaliWigderson1991]
* [M. Naor, *Bit Commitment Using Pseudorandomness*][Naor1991]
* [O. Goldreich, *Foundations of Cryptography: Volume 1, Basic Tools*][Goldreich2001], Chapter 4.
-/

@[expose] public section

namespace Cslib.Crypto.GMW

open Probability Complexity Logic.PL Turing.MultiTapeTM ComputableTidilyInPolyTime
open scoped NNReal ENNReal

/-! ### Step 1: Replacing the verifier's challenge in `runTwoRound` by a random guess -/

private theorem runTwoRound_query_inl {α β : Type} (reply1 reply2 : List Bool → List Bool)
    (n : ℕ) (k : Fin (n + 1) → WordOracleComp Unit α) (s : ℕ × List Bool)
    (f : α × (ℕ × List Bool) → β) :
    f <$> runTwoRound reply1 reply2 (OracleComp.query (Sum.inl n) >>= k) s =
      (ProbComp.unifFin n >>= fun u => f <$> runTwoRound reply1 reply2 (k u) s) := by
  simp only [runTwoRound, OracleComp.interpret_bind, OracleComp.interpret_query,
    ProbOracleComp.handler, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]

private theorem runTwoRound_query_inr {α β : Type} (reply1 reply2 : List Bool → List Bool)
    (q : Unit × List Bool) (k : List Bool → WordOracleComp Unit α) (s : ℕ × List Bool)
    (f : α × (ℕ × List Bool) → β) :
    f <$> runTwoRound reply1 reply2 (OracleComp.query (Sum.inr q) >>= k) s =
      let step := twoRoundStep reply1 reply2 q.2 s
      f <$> runTwoRound reply1 reply2 (k step.1) step.2 := by
  simp only [runTwoRound, OracleComp.interpret_bind, OracleComp.interpret_query,
    ProbOracleComp.handler, StateT.run_bind]
  rfl

private theorem length_snd_mem_support_runTwoRound {α : Type} (r1 r2 : List Bool → List Bool)
    (prog : WordOracleComp Unit α) {s : ℕ × List Bool} (hs : s.2.length = 3)
    {p : α × (ℕ × List Bool)}
    (hp : p ∈ (ProbComp.eval (runTwoRound r1 r2 prog s)).support) :
    p.2.2.length = 3 := by
  induction prog using PFunctor.FreeM.induction generalizing s with
  | pure x =>
    simp only [runTwoRound_pure, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hp
    rw [hp]; exact hs
  | lift_bind q k ih =>
    cases q with
    | inl n =>
      have hq := runTwoRound_query_inl r1 r2 n k s id
      simp only [id_map] at hq
      change p ∈ (ProbComp.eval (runTwoRound r1 r2 (OracleComp.query (Sum.inl n) >>= k) s)).support
        at hp
      rw [hq, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hp
      obtain ⟨u, _, hu⟩ := hp
      exact ih u hs hu
    | inr q =>
      have hq := runTwoRound_query_inr r1 r2 q k s id
      simp only [id_map] at hq
      change p ∈ (ProbComp.eval (runTwoRound r1 r2 (OracleComp.query (Sum.inr q) >>= k) s)).support
        at hp
      rw [hq] at hp
      have hstep : (twoRoundStep r1 r2 q.2 s).2.2.length = 3 := by
        dsimp only [twoRoundStep]; split_ifs <;> simp [hs]
      exact ih _ hstep hp

private theorem runTwoRound_congr_reply1_of_one_le {α : Type} (r1 r1' r2 : List Bool → List Bool)
    (prog : WordOracleComp Unit α) {s : ℕ × List Bool} (hs : 1 ≤ s.1) :
    runTwoRound r1 r2 prog s = runTwoRound r1' r2 prog s := by
  induction prog using PFunctor.FreeM.induction generalizing s with
  | pure x => rfl
  | lift_bind q k ih =>
    cases q with
    | inl n =>
      have h1 := runTwoRound_query_inl r1 r2 n k s id
      have h2 := runTwoRound_query_inl r1' r2 n k s id
      simp only [id_map] at h1 h2
      change runTwoRound r1 r2 (OracleComp.query (Sum.inl n) >>= k) s =
        runTwoRound r1' r2 (OracleComp.query (Sum.inl n) >>= k) s
      rw [h1, h2]; congr 1; funext u; exact ih u hs
    | inr q =>
      have h1 := runTwoRound_query_inr r1 r2 q k s id
      have h2 := runTwoRound_query_inr r1' r2 q k s id
      simp only [id_map] at h1 h2
      change runTwoRound r1 r2 (OracleComp.query (Sum.inr q) >>= k) s =
        runTwoRound r1' r2 (OracleComp.query (Sum.inr q) >>= k) s
      rw [h1, h2]
      have h0 : (s.1 == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
      have hstep : twoRoundStep r1 r2 q.2 s = twoRoundStep r1' r2 q.2 s := by
        simp [twoRoundStep, h0]
      have hs' : 1 ≤ (twoRoundStep r1' r2 q.2 s).2.1 := by
        dsimp only [twoRoundStep]; split_ifs <;> simp [hs]
      rw [hstep]; exact ih _ hs'

private theorem eval_bind_runTwoRound_reply1 {α β : Type} (μ : ProbComp β)
    (f₁ f₂ : β → List Bool → List Bool) (r2 : List Bool → List Bool)
    (hf : ∀ r, ProbComp.eval ((fun b => f₁ b r) <$> μ) =
      ProbComp.eval ((fun b => f₂ b r) <$> μ))
    (prog : WordOracleComp Unit α) (ch₀ : List Bool) :
    ProbComp.eval (μ >>= fun b => runTwoRound (f₁ b) r2 prog (0, ch₀)) =
      ProbComp.eval (μ >>= fun b => runTwoRound (f₂ b) r2 prog (0, ch₀)) := by
  induction prog using PFunctor.FreeM.induction with
  | pure x => rfl
  | lift_bind q k ih =>
    cases q with
    | inl n =>
      have h1 (b : β) := runTwoRound_query_inl (f₁ b) r2 n k (0, ch₀) id
      have h2 (b : β) := runTwoRound_query_inl (f₂ b) r2 n k (0, ch₀) id
      simp only [id_map] at h1 h2
      change ProbComp.eval (μ >>= fun b =>
          runTwoRound (f₁ b) r2 (OracleComp.query (Sum.inl n) >>= k) (0, ch₀)) =
        ProbComp.eval (μ >>= fun b =>
          runTwoRound (f₂ b) r2 (OracleComp.query (Sum.inl n) >>= k) (0, ch₀))
      simp only [h1, h2, ProbComp.eval_bind]
      rw [PMF.bind_comm (ProbComp.eval μ), PMF.bind_comm (ProbComp.eval μ)]
      congr 1; funext u
      simpa only [ProbComp.eval_bind] using ih u
    | inr q =>
      have h1 (b : β) := runTwoRound_query_inr (f₁ b) r2 q k (0, ch₀) id
      have h2 (b : β) := runTwoRound_query_inr (f₂ b) r2 q k (0, ch₀) id
      simp only [id_map, twoRoundStep, beq_self_eq_true, ↓reduceIte] at h1 h2
      have hcongr1 (b : β) :
          runTwoRound (f₁ b) r2 (k (f₁ b q.2)) (1, ch₀) =
            runTwoRound (fun _ => []) r2 (k (f₁ b q.2)) (1, ch₀) :=
        runTwoRound_congr_reply1_of_one_le _ _ r2 _ (le_refl 1)
      have hcongr2 (b : β) :
          runTwoRound (f₂ b) r2 (k (f₂ b q.2)) (1, ch₀) =
            runTwoRound (fun _ => []) r2 (k (f₂ b q.2)) (1, ch₀) :=
        runTwoRound_congr_reply1_of_one_le _ _ r2 _ (le_refl 1)
      change ProbComp.eval (μ >>= fun b =>
          runTwoRound (f₁ b) r2 (OracleComp.query (Sum.inr q) >>= k) (0, ch₀)) =
        ProbComp.eval (μ >>= fun b =>
          runTwoRound (f₂ b) r2 (OracleComp.query (Sum.inr q) >>= k) (0, ch₀))
      simp only [h1, h2, hcongr1, hcongr2]
      have hmap := congrArg
        (fun d => d.bind (fun ans => ProbComp.eval (runTwoRound (fun _ => []) r2 (k ans) (1, ch₀))))
        (hf q.2)
      simpa only [ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_map, Function.comp_def]
        using hmap

private theorem eval_runTwoRound_of_two_le (r1 r2 : List Bool → List Bool) (ch_guess : List Bool)
    (prog : WordOracleComp Unit (List Bool)) {s : ℕ × List Bool}
    (hs1 : 2 ≤ s.1) (hs2 : (s.2 == ch_guess) = false) :
    ProbComp.eval ((fun p => if p.2.2 == ch_guess then true :: p.1 else []) <$>
      runTwoRound r1 r2 prog s) = PMF.pure [] := by
  induction prog using PFunctor.FreeM.induction generalizing s with
  | pure x =>
    simp [beq_eq_false_iff_ne.mp hs2]
  | lift_bind q k ih =>
    cases q with
    | inl n =>
      change ProbComp.eval (_ <$> runTwoRound r1 r2 (OracleComp.query (Sum.inl n) >>= k) s) = _
      rw [runTwoRound_query_inl, ProbComp.eval_bind]
      have hconst : (fun u => ProbComp.eval
          ((fun p => if p.2.2 == ch_guess then true :: p.1 else []) <$>
            runTwoRound r1 r2 (k u) s)) = fun _ => PMF.pure [] := by
        funext u
        exact ih u hs1 hs2
      rw [hconst, PMF.bind_const]
    | inr q =>
      change ProbComp.eval (_ <$> runTwoRound r1 r2 (OracleComp.query (Sum.inr q) >>= k) s) = _
      rw [runTwoRound_query_inr]
      have h0 : (s.1 == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
      have h1 : (s.1 == 1) = false := beq_eq_false_iff_ne.mpr (by omega)
      have hstep : twoRoundStep r1 r2 q.2 s = ([], s) := by
        simp [twoRoundStep, h0, h1]
      rw [hstep]
      exact ih [] hs1 hs2

private theorem eval_runTwoRound_guess (r1 r2 : List Bool → List Bool) (ch_guess : List Bool)
    (prog : WordOracleComp Unit (List Bool)) (s : ℕ × List Bool) :
    ProbComp.eval ((fun p => if p.2.2 == ch_guess then true :: p.1 else []) <$>
      runTwoRound r1 r2 prog s) =
    ProbComp.eval ((fun p => if p.2.2 == ch_guess then true :: p.1 else []) <$>
      runTwoRound r1 (fun _ => r2 ch_guess) prog s) := by
  induction prog using PFunctor.FreeM.induction generalizing s with
  | pure x => rfl
  | lift_bind q k ih =>
    cases q with
    | inl n =>
      change ProbComp.eval (_ <$> runTwoRound r1 r2 (OracleComp.query (Sum.inl n) >>= k) s) =
        ProbComp.eval (_ <$> runTwoRound r1 _ (OracleComp.query (Sum.inl n) >>= k) s)
      rw [runTwoRound_query_inl, runTwoRound_query_inl, ProbComp.eval_bind, ProbComp.eval_bind]
      congr 1
      funext u
      exact ih u s
    | inr q =>
      change ProbComp.eval (_ <$> runTwoRound r1 r2 (OracleComp.query (Sum.inr q) >>= k) s) =
        ProbComp.eval (_ <$> runTwoRound r1 _ (OracleComp.query (Sum.inr q) >>= k) s)
      rw [runTwoRound_query_inr, runTwoRound_query_inr]
      dsimp only [twoRoundStep]
      split_ifs with h0 h1
      · exact ih (r1 q.2) (1, s.2)
      · by_cases hch : (BitString.listRow 3 0 q.2 == ch_guess) = true
        · have heq : BitString.listRow 3 0 q.2 = ch_guess := beq_iff_eq.mp hch
          rw [heq]
          exact ih (r2 ch_guess) (2, ch_guess)
        · have hfalse : (BitString.listRow 3 0 q.2 == ch_guess) = false :=
            Bool.eq_false_iff.mpr hch
          rw [eval_runTwoRound_of_two_le r1 r2 ch_guess (k (r2 (BitString.listRow 3 0 q.2)))
              (le_refl 2) hfalse,
            eval_runTwoRound_of_two_le r1 (fun _ => r2 ch_guess) ch_guess (k (r2 ch_guess))
              (le_refl 2) hfalse]
      · exact ih [] s

private theorem uniformList_map_guess_eq {ch₀ : List Bool} (hch₀ : ch₀.length = 3)
    (out : List Bool) :
    (BitString.uniformList 3).map (fun ch_guess => if ch₀ == ch_guess then true :: out else []) =
      (BitString.uniformList 3).map
        (fun ch_guess => if [false, false, false] == ch_guess then true :: out else []) := by
  conv_lhs => rw [← BitString.uniformList_map_listXor 3 ch₀]
  rw [PMF.map_comp]
  simp only [PMF.map]
  refine Probability.PMF.bind_congr_on_support (BitString.uniformList 3) _ _ fun u hu => ?_
  have hu_len : u.length = 3 := BitString.length_of_mem_support_uniformList hu
  have hzero : BitString.ofList 3 [false, false, false] = 0 := by
    funext i
    fin_cases i <;> rfl
  have hiff : (ch₀ = BitString.listXor 3 [u, ch₀]) ↔ ([false, false, false] = u) := by
    constructor
    · intro h
      have h1 := congrArg (fun l => BitString.ofList 3 l + BitString.ofList 3 ch₀) h
      simp only [BitString.ofList_listXor_pair 3 u ch₀, add_assoc, BitString.add_self,
        add_zero] at h1
      have h2 := congrArg List.ofFn h1
      rw [← hzero, BitString.ofFn_ofList (by simp), BitString.ofFn_ofList hu_len] at h2
      exact h2
    · rintro rfl
      have h1 : BitString.ofList 3 (BitString.listXor 3 [[false, false, false], ch₀]) =
          BitString.ofList 3 ch₀ := by
        rw [BitString.ofList_listXor_pair, hzero, zero_add]
      have h2 := congrArg List.ofFn h1
      rw [BitString.ofFn_ofList (by simp), BitString.ofFn_ofList hch₀] at h2
      exact h2.symm
  simp [Function.comp_def, hiff]

private theorem gmwFirstSuccess_nil : gmwFirstSuccess [] = [] := rfl

private theorem gmwFirstSuccess_cons (x : List Bool) (xs : List (List Bool)) :
    gmwFirstSuccess (x :: xs) = if x.headD false then x.tail else gmwFirstSuccess xs := by
  simp only [gmwFirstSuccess, List.filter_cons]
  cases x.headD false <;> rfl

/-- Single-attempt hybrid 0: guess a 3-bit challenge `ch_guess`, sample honest prover coins
`(bits, seeds)`, run `prog` against `honestReply1` and `fun _ => honestReply2 ... ch_guess`, and
return `true :: out` when the verifier's challenge equals `ch_guess`, or `[]` otherwise. -/
private noncomputable def game0 (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (w : List Bool) (prog : WordOracleComp Unit (List Bool)) : ProbComp (List Bool) := do
  let ch_guess ← BitString.sampleList 3
  let coins ← sampleHonestCoins s φ w
  let p ← runTwoRound
    (honestReply1 generator m φ coins)
    (fun _ => honestReply2 s φ coins ch_guess)
    prog (0, [false, false, false])
  return if p.2.2 == ch_guess then true :: p.1 else []

/-- Tag `out` with `true :: out` when a uniform 3-bit challenge equals `[false, false, false]`,
and return `[]` otherwise. -/
private noncomputable def bernoulliAttempt (out : List Bool) : PMF (List Bool) :=
  (BitString.uniformList 3).map
    (fun ch_guess => if [false, false, false] == ch_guess then true :: out else [])

/-- Choose `p` when a uniform 3-bit challenge equals `[false, false, false]`, and `q` otherwise. -/
private noncomputable def mixThree {α : Type} (p q : PMF α) : PMF α :=
  (BitString.uniformList 3).bind
    (fun ch_guess => if [false, false, false] == ch_guess then p else q)

/-- Distribution of `gmwFirstSuccess` after `k` independent attempts from
`μ.bind bernoulliAttempt`. -/
private noncomputable def repeatAttempt (μ : PMF (List Bool)) : ℕ → PMF (List Bool)
  | 0 => PMF.pure []
  | k + 1 => mixThree μ (repeatAttempt μ k)

private theorem eval_game0_eq_bind_bernoulliAttempt (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (w : List Bool) (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval (game0 generator s m φ w prog) =
      (((gmwProver generator s m φ w).run prog
        (gmwProver generator s m φ w).init).map Prod.fst).bind bernoulliAttempt := by
  rw [run_gmwProver_fst]
  have hguess (ch_guess : List Bool) (coins : List Bool × List (List Bool)) :
      ProbComp.eval (do
        let p ← runTwoRound
          (honestReply1 generator m φ coins)
          (fun _ => honestReply2 s φ coins ch_guess)
          prog (0, [false, false, false])
        return if p.2.2 == ch_guess then true :: p.1 else []) =
      ProbComp.eval (do
        let p ← runTwoRound
          (honestReply1 generator m φ coins)
          (honestReply2 s φ coins)
          prog (0, [false, false, false])
        return if p.2.2 == ch_guess then true :: p.1 else []) := by
    simpa only [bind_pure_comp] using
      (eval_runTwoRound_guess
        (honestReply1 generator m φ coins)
        (honestReply2 s φ coins)
        ch_guess prog (0, [false, false, false])).symm
  simp only [game0, ProbComp.eval_bind, BitString.eval_sampleList, hguess]
  simp only [ProbComp.eval_map, ProbComp.eval_pure, PMF.bind_bind,
    PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun coins _ => ?_
  rw [PMF.bind_comm]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun p hp => ?_
  have hlen : p.2.2.length = 3 := length_snd_mem_support_runTwoRound _ _ prog rfl hp
  simpa only [bernoulliAttempt, PMF.map, Function.comp_def] using
    uniformList_map_guess_eq hlen p.1

private theorem bind_bernoulliAttempt_ite (μ ν : PMF (List Bool)) :
    (μ.bind bernoulliAttempt).bind
      (fun x => if x.headD false then PMF.pure x.tail else ν) = mixThree μ ν := by
  simp only [bernoulliAttempt, mixThree, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm]
  congr 1
  funext ch_guess
  by_cases h : ([false, false, false] == ch_guess) = true
  · simp [h]
  · have hfalse : ([false, false, false] == ch_guess) = false := Bool.eq_false_iff.mpr h
    simp [hfalse, PMF.bind_const]

private theorem eval_gmwFirstSuccess_replicate_eq_repeatAttempt {g : ProbComp (List Bool)}
    {μ : PMF (List Bool)} (hg : ProbComp.eval g = μ.bind bernoulliAttempt) (k : ℕ) :
    ProbComp.eval (gmwFirstSuccess <$> OracleComp.replicate k g) = repeatAttempt μ k := by
  induction k with
  | zero =>
    simp [repeatAttempt, gmwFirstSuccess_nil]
  | succ k ih =>
    simp only [OracleComp.replicate_succ, map_bind, ProbComp.eval_bind, ProbComp.eval_map,
      PMF.map_comp, Function.comp_def, gmwFirstSuccess_cons, repeatAttempt]
    have hstep (x : List Bool) :
        (ProbComp.eval (OracleComp.replicate k g)).map
          (fun xs => if x.headD false then x.tail else gmwFirstSuccess xs) =
        if x.headD false then PMF.pure x.tail else repeatAttempt μ k := by
      cases x.headD false
      · simpa only [Bool.false_eq_true, ↓reduceIte, ProbComp.eval_map] using ih
      · simp only [↓reduceIte]
        exact PMF.map_const _ _
    simp only [hstep, hg]
    exact bind_bernoulliAttempt_ite μ (repeatAttempt μ k)

private theorem distinguishingGame_mixThree (p q : PMF (List Bool))
    (adv : List Bool → ProbComp Bool) :
    distinguishingGame (mixThree p q) adv =
      mixThree (distinguishingGame p adv) (distinguishingGame q adv) := by
  simp only [distinguishingGame, mixThree, PMF.bind_bind]
  congr 1
  funext ch_guess
  split_ifs <;> rfl

private theorem advantage_mixThree (g1 g2 : Game) :
    Game.advantage (mixThree g1 g2) g1 = (7 / 8 : ℝ≥0) * Game.advantage g2 g1 := by
  have hunif : mixThree g1 g2 =
      (PMF.uniformOfFintype (BitString 3)).bind
        (fun v => if v = 0 then g1 else g2) := by
    simp only [mixThree, BitString.uniformList, PMF.bind_map, Function.comp_def]
    congr 1
    funext v
    by_cases hv : v = 0
    · subst hv; rfl
    · simp only [hv, ↓reduceIte, beq_iff_eq, ite_eq_right_iff]
      intro h
      refine False.elim (hv (funext fun i => ?_))
      have hi := congrArg (fun l => l.getD i.val false) h.symm
      fin_cases i <;> exact hi
  have hsucc : (Game.succProbability (mixThree g1 g2) : ℝ) - Game.succProbability g1 =
      (7 / 8 : ℝ) * ((Game.succProbability g2 : ℝ) - Game.succProbability g1) := by
    rw [hunif, Game.succProbability_uniform]
    simp only [NNReal.coe_div, NNReal.coe_sum, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
    have hterm (v : BitString 3) :
        (Game.succProbability (if v = 0 then g1 else g2) : ℝ) =
          (Game.succProbability g2 : ℝ) +
            if v = 0 then (Game.succProbability g1 : ℝ) - Game.succProbability g2 else 0 := by
      split_ifs <;> ring
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, Nat.cast_pow,
      Nat.cast_ofNat, Fintype.sum_ite_eq']
    norm_num
    ring
  apply NNReal.eq
  rw [NNReal.coe_mul, Game.coe_advantage, Game.coe_advantage, hsucc, abs_mul]
  norm_num

private theorem advantage_repeatAttempt_le (μ : PMF (List Bool)) (adv : List Bool → ProbComp Bool)
    (k : ℕ) :
    Game.advantage (distinguishingGame (repeatAttempt μ k) adv) (distinguishingGame μ adv) ≤
      (7 / 8 : ℝ≥0) ^ k := by
  induction k with
  | zero =>
    simpa [repeatAttempt] using Game.advantage_le_one _ _
  | succ k ih =>
    rw [repeatAttempt, distinguishingGame_mixThree, advantage_mixThree, pow_succ']
    gcongr

private theorem firstSuccess_replicate_game0_indistinguishable (generator : List Bool → List Bool)
    (s m : ℕ → ℕ) (φ : ℕ → CNF ℕ) (w : ℕ → List Bool)
    (prog : ℕ → WordOracleComp Unit (List Bool)) :
    ComputationallyIndistinguishable
      (fun n => ((gmwProver generator (s n) (m n) (φ n) (w n)).run (prog n)
        (gmwProver generator (s n) (m n) (φ n) (w n)).init).map Prod.fst)
      (fun n => ProbComp.eval
        (gmwFirstSuccess <$> OracleComp.replicate (n + 1)
          (game0 generator (s n) (m n) (φ n) (w n) (prog n)))) := by
  refine ComputationallyIndistinguishable.symm fun adv _ => ?_
  refine negligible_of_le
    ((negligible_geometric (by norm_num : (7 / 8 : ℝ≥0) < 1)).shift 1) fun n => ?_
  dsimp only
  rw [eval_gmwFirstSuccess_replicate_eq_repeatAttempt
    (eval_game0_eq_bind_bernoulliAttempt generator (s n) (m n) (φ n) (w n) (prog n)) (n + 1)]
  exact advantage_repeatAttempt_le _ (adv n) (n + 1)

/-! ### Step 2: Introducing unopened pads via `naorSelectPads` -/

/-- Run one attempt with pre-sampled unopened pads `pads` and active flags
`allOpenFlags φ ch_guess bits`. -/
private noncomputable def gameWithPads (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (w : List Bool) (prog : WordOracleComp Unit (List Bool)) (pads : List (List Bool)) :
    ProbComp (List Bool) := do
  let ch_guess ← BitString.sampleList 3
  let m₀ ← BitString.sampleList φ.vars.length
  let m₁ ← BitString.sampleList φ.vars.length
  let m₂ ← BitString.sampleList φ.vars.length
  let bits := realBits φ w m₀ m₁ m₂
  let openFlags := allOpenFlags φ ch_guess bits
  let seeds ← OracleComp.replicate (totalLen φ) (BitString.sampleList s)
  let p ← runTwoRound
    (fun r => proverReply1 generator m r openFlags bits seeds pads)
    (fun _ => proverReply2 s φ ch_guess bits seeds)
    prog (0, [false, false, false])
  return if p.2.2 == ch_guess then true :: p.1 else []

/-- Single-attempt hybrid with pseudorandom unopened pads. -/
private noncomputable def game0Pads (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (w : List Bool) (prog : WordOracleComp Unit (List Bool)) : ProbComp (List Bool) :=
  OracleComp.replicate (totalLen φ) (generator <$> BitString.sampleList s) >>=
    gameWithPads generator s m φ w prog

/-- Single-attempt hybrid with uniform unopened pads. -/
private noncomputable def game1 (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (w : List Bool) (prog : WordOracleComp Unit (List Bool)) : ProbComp (List Bool) :=
  OracleComp.replicate (totalLen φ) (BitString.sampleList m) >>=
    gameWithPads generator s m φ w prog

private theorem eval_bind_gameWithPads (d_pads : ProbComp (List (List Bool)))
    (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ) (w : List Bool)
    (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval (d_pads >>= gameWithPads generator s m φ w prog) =
      ProbComp.eval (do
        let ch_guess ← BitString.sampleList 3
        let m₀ ← BitString.sampleList φ.vars.length
        let m₁ ← BitString.sampleList φ.vars.length
        let m₂ ← BitString.sampleList φ.vars.length
        let bits := realBits φ w m₀ m₁ m₂
        let openFlags := allOpenFlags φ ch_guess bits
        let seeds ← OracleComp.replicate (totalLen φ) (BitString.sampleList s)
        let pads ← d_pads
        let p ← runTwoRound
          (fun r => proverReply1 generator m r openFlags bits seeds pads)
          (fun _ => proverReply2 s φ ch_guess bits seeds)
          prog (0, [false, false, false])
        return if p.2.2 == ch_guess then true :: p.1 else []) := by
  simp only [gameWithPads, ProbComp.eval_bind, BitString.eval_sampleList]
  rw [PMF.bind_comm]
  congr 1; funext ch_guess
  rw [PMF.bind_comm]
  congr 1; funext m₀
  rw [PMF.bind_comm]
  congr 1; funext m₁
  rw [PMF.bind_comm]
  congr 1; funext m₂
  rw [PMF.bind_comm]

private theorem proverReply1_eq_naorSelectPads (generator : List Bool → List Bool) (m : ℕ)
    (r openFlags bits : List Bool) (seeds pads : List (List Bool)) :
    proverReply1 generator m r openFlags bits seeds pads =
      proverReply1 id m r (List.replicate bits.length false) bits []
        (naorSelectPads generator openFlags bits seeds pads) := by
  unfold proverReply1
  rw [naorCommitSplit_eq_naorSelectPads]

private theorem eval_game0Pads_eq_eval_game0 (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (w : List Bool) (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval (game0Pads generator s m φ w prog) =
      ProbComp.eval (game0 generator s m φ w prog) := by
  rw [game0Pads, eval_bind_gameWithPads]
  simp only [game0, sampleHonestCoins, bind_assoc, pure_bind, ProbComp.eval_bind]
  congr 1; funext ch_guess
  congr 1; funext m₀
  congr 1; funext m₁
  congr 1; funext m₂
  let bits := realBits φ w m₀ m₁ m₂
  have hbits : bits.length = totalLen φ := length_realBits φ w m₀ m₁ m₂
  let openFlags := allOpenFlags φ ch_guess bits
  let cont (q : List (List Bool) × List (List Bool)) : PMF (List Bool) :=
    ProbComp.eval (do
      let p ← runTwoRound
        (fun r => proverReply1 id m r (List.replicate bits.length false) bits [] q.1)
        (fun _ => naorMaskBits openFlags bits ++ q.2.flatten)
        prog (0, [false, false, false])
      return if p.2.2 == ch_guess then true :: p.1 else [])
  have hselect := congrArg (fun d => d.bind cont)
    (eval_replicate_naorSelectPads s generator openFlags bits)
  simp only [hbits, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.bind_bind,
    PMF.bind_map, PMF.pure_bind, Function.comp_def, cont] at hselect
  have hhon1 (seeds : List (List Bool)) :
      honestReply1 generator m φ (realBits φ w m₀ m₁ m₂, seeds) =
        fun r => proverReply1 generator m r (List.replicate (totalLen φ) true)
          (realBits φ w m₀ m₁ m₂) seeds [] := rfl
  simp only [hhon1, honestReply2, proverReply2, ProbComp.eval_pure,
    proverReply1_eq_naorSelectPads generator m, length_realBits]
  exact hselect

/-! ### Step 3: Pseudorandom unopened pads to uniform unopened pads -/

private theorem isPPTOn_gameWithPads {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {a : ℕ → α} {w z : ℕ → List Bool}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableTidilyInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2))
    (ha : ComputableTidilyInPolyTime a encUnary enc)
    (hw : ComputableTidilyInPolyTime w encUnary encBits)
    (hz : ComputableTidilyInPolyTime z encUnary encBits) :
    IsPPTOn (encPair encUnary (encList encBits)) encBits
      (fun p : ℕ × List (List Bool) =>
        gameWithPads generator (p.1 + 7) (length (p.1 + 7))
          (f (a p.1)) (w p.1) (Vstar p.1 (a p.1) (z p.1)) p.2) := by
  have hlength := PRG.polyTime_length hg hlen
  dsimp only [gameWithPads]
  ppt

private theorem isPPTOn_game0 {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {a : ℕ → α} {w z : ℕ → List Bool}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableTidilyInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2))
    (ha : ComputableTidilyInPolyTime a encUnary enc)
    (hw : ComputableTidilyInPolyTime w encUnary encBits)
    (hz : ComputableTidilyInPolyTime z encUnary encBits) :
    IsPPTOn encUnary encBits
      (fun n => game0 generator (n + 7) (length (n + 7))
        (f (a n)) (w n) (Vstar n (a n) (z n))) := by
  have hlength := PRG.polyTime_length hg hlen
  dsimp only [game0, sampleHonestCoins, honestReply1, honestReply2]
  ppt

private theorem isPPTOn_game1 {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {a : ℕ → α} {w z : ℕ → List Bool}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableTidilyInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2))
    (ha : ComputableTidilyInPolyTime a encUnary enc)
    (hw : ComputableTidilyInPolyTime w encUnary encBits)
    (hz : ComputableTidilyInPolyTime z encUnary encBits) :
    IsPPTOn encUnary encBits
      (fun n => game1 generator (n + 7) (length (n + 7))
        (f (a n)) (w n) (Vstar n (a n) (z n))) := by
  have hlength := PRG.polyTime_length hg hlen
  have hpad := isPPTOn_gameWithPads hg hlen hf hV ha hw hz
  dsimp only [game1]
  ppt

private theorem game0_indistinguishable_game1 {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    {f : α → CNF ℕ} (hf : ComputableTidilyInPolyTime f enc encCNF)
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2))
    {a : ℕ → α} {w z : ℕ → List Bool}
    (ha : ComputableTidilyInPolyTime a encUnary enc)
    (hw : ComputableTidilyInPolyTime w encUnary encBits)
    (hz : ComputableTidilyInPolyTime z encUnary encBits) :
    ComputationallyIndistinguishable
      (fun n => ProbComp.eval
        (game0 generator (n + 7) (length (n + 7)) (f (a n)) (w n) (Vstar n (a n) (z n))))
      (fun n => ProbComp.eval
        (game1 generator (n + 7) (length (n + 7)) (f (a n)) (w n) (Vstar n (a n) (z n)))) := by
  have hlength := hG.polyTime_length
  have hg := hG.polyTime
  have horig : IsPPTOn encUnary encBits (fun n => generator <$> BitString.sampleList (n + 7)) := by
    ppt
  have hrepl : IsPPTOn encUnary encBits (fun n => BitString.sampleList (length (n + 7))) := by
    ppt
  have hind_pad : ComputationallyIndistinguishable
      (fun n => ProbComp.eval (generator <$> BitString.sampleList (n + 7)))
      (fun n => ProbComp.eval (BitString.sampleList (length (n + 7)))) := by
    simpa only [ProbComp.eval_map, BitString.eval_sampleList, generatorEnsemble] using
      hG.indistinguishable.shift 7
  have hrep := ComputationallyIndistinguishable.replicate_bind horig hrepl hind_pad
    (count := fun n => totalLen (f (a n)))
    (process := fun n pads =>
      gameWithPads generator (n + 7) (length (n + 7))
        (f (a n)) (w n) (Vstar n (a n) (z n)) pads)
    (by fun_prop)
    (isPPTOn_gameWithPads hg hG.length_eq hf hV ha hw hz)
  change ComputationallyIndistinguishable
    (fun n => ProbComp.eval (game0Pads generator (n + 7) (length (n + 7))
      (f (a n)) (w n) (Vstar n (a n) (z n))))
    (fun n => ProbComp.eval (game1 generator (n + 7) (length (n + 7))
      (f (a n)) (w n) (Vstar n (a n) (z n)))) at hrep
  simpa only [eval_game0Pads_eq_eval_game0] using hrep

/-! ### Step 4: Masking unopened committed bits and eliminating the witness -/

private theorem uniformList_bind_ite_listXor {α : Type} (d : ℕ) (b : Bool) (w : List Bool)
    (k : List Bool → PMF α) :
    ((BitString.uniformList d).bind
      fun m => k (if b then BitString.listXor d [w, m] else m)) =
      (BitString.uniformList d).bind k := by
  have hmap : (BitString.uniformList d).map
      (fun m => if b then BitString.listXor d [w, m] else m) = BitString.uniformList d := by
    cases b
    · exact PMF.map_id _
    · simp only [↓reduceIte, BitString.listXor_pair_comm d w]
      exact BitString.uniformList_map_listXor d w
  conv_rhs => rw [← hmap]
  simp only [PMF.bind_map, Function.comp_def]

private theorem uniformList_bind_ite_listXor_three {α : Type} (d : ℕ) (b₀ b₁ b₂ : Bool)
    (w : List Bool) (f : List Bool → List Bool → List Bool → PMF α) :
    ((BitString.uniformList d).bind fun m₀ =>
      (BitString.uniformList d).bind fun m₁ =>
        (BitString.uniformList d).bind fun m₂ =>
          f (if b₀ then BitString.listXor d [w, m₀] else m₀)
            (if b₁ then BitString.listXor d [w, m₁] else m₁)
            (if b₂ then BitString.listXor d [w, m₂] else m₂)) =
    ((BitString.uniformList d).bind fun r₀ =>
      (BitString.uniformList d).bind fun r₁ =>
        (BitString.uniformList d).bind fun r₂ =>
          f r₀ r₁ r₂) := by
  rw [uniformList_bind_ite_listXor d b₀ w (fun r₀ =>
    (BitString.uniformList d).bind fun m₁ =>
      (BitString.uniformList d).bind fun m₂ =>
        f r₀ (if b₁ then BitString.listXor d [w, m₁] else m₁)
          (if b₂ then BitString.listXor d [w, m₂] else m₂))]
  congr 1; funext r₀
  rw [uniformList_bind_ite_listXor d b₁ w (fun r₁ =>
    (BitString.uniformList d).bind fun m₂ =>
      f r₀ r₁ (if b₂ then BitString.listXor d [w, m₂] else m₂))]
  congr 1; funext r₁
  exact uniformList_bind_ite_listXor d b₂ w (fun r₂ => f r₀ r₁ r₂)

private theorem naorSelectSeeds_congr_length (s : ℕ) (openFlags bits₁ bits₂ : List Bool)
    (seeds : List (List Bool)) (hlen : bits₁.length = bits₂.length) :
    naorSelectSeeds s openFlags bits₁ seeds = naorSelectSeeds s openFlags bits₂ seeds := by
  rw [naorSelectSeeds_eq_map, naorSelectSeeds_eq_map, hlen]

private theorem eval_bind_gmwSimWithPads (d_pads : ProbComp (List (List Bool)))
    (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval (d_pads >>= gmwSimWithPads generator s m φ prog) =
      ProbComp.eval (do
        let ch_guess ← BitString.sampleList 3
        let r₀ ← BitString.sampleList φ.vars.length
        let r₁ ← BitString.sampleList φ.vars.length
        let r₂ ← BitString.sampleList φ.vars.length
        let bits := simBits φ ch_guess r₀ r₁ r₂; let openFlags := allOpenFlags φ ch_guess bits
        let seeds ← OracleComp.replicate (totalLen φ) (BitString.sampleList s); let pads ← d_pads
        let p ← runTwoRound (fun r => proverReply1 generator m r openFlags bits seeds pads)
          (fun _ => proverReply2 s φ ch_guess bits seeds) prog (0, [false, false, false])
        return if p.2.2 == ch_guess then true :: p.1 else []) := by
  simp only [gmwSimWithPads, gmwSampleSimCoins, bind_assoc, pure_bind,
    ProbComp.eval_bind, BitString.eval_sampleList]
  rw [PMF.bind_comm]; congr 1; funext ch_guess
  rw [PMF.bind_comm]; congr 1; funext r₀
  rw [PMF.bind_comm]; congr 1; funext r₁
  rw [PMF.bind_comm]; congr 1; funext r₂
  rw [PMF.bind_comm]

private theorem eval_pads_runTwoRound_mask (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (ch_guess openFlags bits : List Bool) (seeds : List (List Bool))
    (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval (do
      let pads ← OracleComp.replicate bits.length (BitString.sampleList m)
      let p ← runTwoRound (fun r => proverReply1 generator m r openFlags bits seeds pads)
        (fun _ => proverReply2 s φ ch_guess bits seeds) prog (0, [false, false, false])
      return if p.2.2 == ch_guess then true :: p.1 else []) =
    ProbComp.eval (do
      let pads ← OracleComp.replicate bits.length (BitString.sampleList m)
      let p ← runTwoRound
        (fun r => proverReply1 generator m r openFlags (naorMaskBits openFlags bits) seeds pads)
        (fun _ => proverReply2 s φ ch_guess bits seeds) prog (0, [false, false, false])
      return if p.2.2 == ch_guess then true :: p.1 else []) := by
  have h1 := eval_bind_runTwoRound_reply1
    (OracleComp.replicate bits.length (BitString.sampleList m))
    (fun pads r => proverReply1 generator m r openFlags bits seeds pads)
    (fun pads r => proverReply1 generator m r openFlags (naorMaskBits openFlags bits) seeds pads)
    (fun _ => proverReply2 s φ ch_guess bits seeds)
    (fun r => by
      have hsplit := congrArg
        (PMF.map fun xs : List (List Bool) => xs.flatten.take (bits.length * m))
        (eval_replicate_map_naorCommitSplit m generator (BitString.listRow m 0 r)
          openFlags bits seeds)
      simpa only [ProbComp.eval_map, PMF.map_comp, Function.comp_def,
        proverReply1, length_naorMaskBits] using hsplit) prog [false, false, false]
  have hmap := congrArg (PMF.map (fun p : List Bool × (ℕ × List Bool) =>
      if p.2.2 == ch_guess then true :: p.1 else [])) h1
  simpa only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, PMF.pure_map,
    PMF.map, PMF.bind_bind, Function.comp_def] using hmap

private theorem eval_game1_eq_eval_gmwSimAttempt (generator : List Bool → List Bool) {s m : ℕ}
    {φ : CNF ℕ} {w : List Bool} (hw : ThreeSAT.verifier (φ, w) = true)
    (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval (game1 generator s m φ w prog) =
      ProbComp.eval (gmwSimAttempt generator s m φ prog) := by
  rw [game1, eval_bind_gameWithPads, gmwSimAttempt, eval_bind_gmwSimWithPads]
  let simCont (ch_guess r₀ r₁ r₂ : List Bool) : PMF (List Bool) :=
    let sbits := simBits φ ch_guess r₀ r₁ r₂; let sflags := allOpenFlags φ ch_guess sbits
    ProbComp.eval (do
      let seeds ← OracleComp.replicate (totalLen φ) (BitString.sampleList s)
      let pads ← OracleComp.replicate (totalLen φ) (BitString.sampleList m)
      let p ← runTwoRound (fun r => proverReply1 generator m r sflags sbits seeds pads)
        (fun _ => proverReply2 s φ ch_guess sbits seeds) prog (0, [false, false, false])
      return if p.2.2 == ch_guess then true :: p.1 else [])
  have hinner (ch_guess m₀ m₁ m₂ : List Bool) :
      ProbComp.eval (do
        let bits := realBits φ w m₀ m₁ m₂; let openFlags := allOpenFlags φ ch_guess bits
        let seeds ← OracleComp.replicate (totalLen φ) (BitString.sampleList s)
        let pads ← OracleComp.replicate (totalLen φ) (BitString.sampleList m)
        let p ← runTwoRound (fun r => proverReply1 generator m r openFlags bits seeds pads)
          (fun _ => proverReply2 s φ ch_guess bits seeds) prog (0, [false, false, false])
        return if p.2.2 == ch_guess then true :: p.1 else []) =
      simCont ch_guess
        (if ch_guess.getD 0 false then BitString.listXor φ.vars.length [w, m₀] else m₀)
        (if ch_guess.getD 1 false then BitString.listXor φ.vars.length [w, m₁] else m₁)
        (if ch_guess.getD 2 false then BitString.listXor φ.vars.length [w, m₂] else m₂) := by
    let bits := realBits φ w m₀ m₁ m₂; let openFlags := allOpenFlags φ ch_guess bits
    let r₀ := if ch_guess.getD 0 false then BitString.listXor φ.vars.length [w, m₀] else m₀
    let r₁ := if ch_guess.getD 1 false then BitString.listXor φ.vars.length [w, m₁] else m₁
    let r₂ := if ch_guess.getD 2 false then BitString.listXor φ.vars.length [w, m₂] else m₂
    let sbits := simBits φ ch_guess r₀ r₁ r₂
    have hbits_len : bits.length = totalLen φ := length_realBits φ w m₀ m₁ m₂
    have hsbits_len : sbits.length = totalLen φ := length_simBits φ ch_guess r₀ r₁ r₂
    have hmask : naorMaskBits openFlags bits = sbits := naorMaskBits_realBits ch_guess hw
    have hflags : openFlags = allOpenFlags φ ch_guess sbits :=
      allOpenFlags_realBits φ ch_guess w m₀ m₁ m₂
    have hrep2 (seeds : List (List Bool)) :
        proverReply2 s φ ch_guess bits seeds = proverReply2 s φ ch_guess sbits seeds := by
      simp only [proverReply2]
      change naorMaskBits openFlags bits ++ (naorSelectSeeds s openFlags bits seeds).flatten =
        naorMaskBits (allOpenFlags φ ch_guess sbits) sbits ++
          (naorSelectSeeds s (allOpenFlags φ ch_guess sbits) sbits seeds).flatten
      rw [hmask, naorMaskBits_simBits, hflags,
        naorSelectSeeds_congr_length s _ bits sbits seeds (hbits_len.trans hsbits_len.symm)]
    dsimp only [simCont]; simp only [ProbComp.eval_bind]; congr 1; funext seeds
    have hpad := eval_pads_runTwoRound_mask generator s m φ ch_guess openFlags bits seeds prog
    rw [hbits_len] at hpad
    have hpad_rhs :
        ProbComp.eval (do
          let pads ← OracleComp.replicate (totalLen φ) (BitString.sampleList m)
          let p ← runTwoRound
            (fun r => proverReply1 generator m r openFlags (naorMaskBits openFlags bits) seeds pads)
            (fun _ => proverReply2 s φ ch_guess bits seeds) prog (0, [false, false, false])
          return if p.2.2 == ch_guess then true :: p.1 else []) =
        ProbComp.eval (do
          let pads ← OracleComp.replicate (totalLen φ) (BitString.sampleList m)
          let p ← runTwoRound
            (fun r => proverReply1 generator m r (allOpenFlags φ ch_guess sbits) sbits seeds pads)
            (fun _ => proverReply2 s φ ch_guess sbits seeds) prog (0, [false, false, false])
          return if p.2.2 == ch_guess then true :: p.1 else []) := by
      rw [hmask, hflags, hrep2 seeds]
    simpa only [ProbComp.eval_bind] using hpad.trans hpad_rhs
  simp only [ProbComp.eval_bind, BitString.eval_sampleList, hinner]; congr 1; funext ch_guess
  simpa only [simCont, ProbComp.eval_bind] using
    uniformList_bind_ite_listXor_three φ.vars.length
      (ch_guess.getD 0 false) (ch_guess.getD 1 false) (ch_guess.getD 2 false) w (simCont ch_guess)

/-- **Zero-knowledge simulation of the 3-copy GMW protocol.** For any uniform strict oracle PPT
malicious verifier `Vstar` and any deterministic polynomial-time families of instances `a`, valid
`ThreeSAT` witnesses `w`, and auxiliary inputs `z`, the real interaction view of `Vstar` with
`gmwProver` is computationally indistinguishable from `gmwSimulator`. -/
theorem gmwView_indistinguishable_gmwSimulator {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    {f : α → CNF ℕ} (hf : ComputableTidilyInPolyTime f enc encCNF)
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2))
    {a : ℕ → α} {w z : ℕ → List Bool}
    (ha : ComputableTidilyInPolyTime a encUnary enc)
    (hw_comp : ComputableTidilyInPolyTime w encUnary encBits)
    (hz : ComputableTidilyInPolyTime z encUnary encBits)
    (hw_sat : ∀ n, ThreeSAT.verifier (f (a n), w n) = true) :
    ComputationallyIndistinguishable
      (fun n => ((gmwProver generator (n + 7) (length (n + 7)) (f (a n)) (w n)).run
        (Vstar n (a n) (z n))
        (gmwProver generator (n + 7) (length (n + 7)) (f (a n)) (w n)).init).map Prod.fst)
      (fun n => ProbComp.eval (gmwSimulator generator length f Vstar n (a n) (z n))) := by
  have hstep1 := firstSuccess_replicate_game0_indistinguishable generator
    (fun n => n + 7) (fun n => length (n + 7)) (fun n => f (a n)) w
    (fun n => Vstar n (a n) (z n))
  have hg := hG.polyTime
  have hstep23 := ComputationallyIndistinguishable.replicate_bind
    (isPPTOn_game0 hg hG.length_eq hf hV ha hw_comp hz)
    (isPPTOn_game1 hg hG.length_eq hf hV ha hw_comp hz)
    (game0_indistinguishable_game1 hG hf hV ha hw_comp hz)
    (count := fun n => n + 1)
    (process := fun _ xs => pure (gmwFirstSuccess xs))
    (by fun_prop)
    (by ppt)
  have hstep23' :
      ComputationallyIndistinguishable
        (fun n => ProbComp.eval
          (gmwFirstSuccess <$> OracleComp.replicate (n + 1)
            (game0 generator (n + 7) (length (n + 7)) (f (a n)) (w n) (Vstar n (a n) (z n)))))
        (fun n => ProbComp.eval
          (gmwFirstSuccess <$> OracleComp.replicate (n + 1)
            (game1 generator (n + 7) (length (n + 7)) (f (a n)) (w n) (Vstar n (a n) (z n))))) := by
    simpa only [bind_pure_comp] using hstep23
  have hstep4 :
      (fun n => ProbComp.eval
        (gmwFirstSuccess <$> OracleComp.replicate (n + 1)
          (game1 generator (n + 7) (length (n + 7)) (f (a n)) (w n) (Vstar n (a n) (z n))))) =
      (fun n => ProbComp.eval (gmwSimulator generator length f Vstar n (a n) (z n))) := by
    funext n
    have h1 := eval_game1_eq_eval_gmwSimAttempt generator (s := n + 7) (m := length (n + 7))
      (hw_sat n) (Vstar n (a n) (z n))
    simp only [gmwSimulator, ProbComp.eval_map, ProbComp.eval_replicate_congr h1]
  rw [← hstep4]
  exact hstep1.trans hstep23'

end Cslib.Crypto.GMW
