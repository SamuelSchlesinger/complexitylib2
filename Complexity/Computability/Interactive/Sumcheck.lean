/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (design prototype for #643; not for merge)

public import Complexity.Computability.Interactive.Sequential
import Complexity.Probability.PMF
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Worked example: sumcheck followed by a final evaluation check (design prototype)

The index is a polynomial `P` in `n` variables over a finite field `F` with every individual
degree at most `d`. A claim `(r, c)` at round `i` states that the sum of `P` over the Boolean
hypercube in the coordinates `i, …, n - 1`, with the coordinates below `i` fixed to `r`, is `c`
(`Sumcheck.rel P i`). At round `0` this is the sumcheck claim `∑_{b ∈ {0,1}ⁿ} P b = c`, and at
round `n` it is the evaluation claim `P r = c`.

* `Sumcheck.round d P i` reduces `rel P i` to `rel P (i + 1)` in one prover message (a univariate
  polynomial) and one uniform challenge.
* `Sumcheck.finalCheck P` reduces `rel P n` to acceptance by evaluating `P` without interaction.
* `Sumcheck.proof d P` is `round 0`, …, `round (n - 1)` followed by `finalCheck`.

The end-to-end theorems `Sumcheck.proof_complete` and `Sumcheck.proof_sound` are corollaries of
the component theorems through the composition theorems: the soundness error `n * (d / |F|)` is the
sum of the per-round errors, and no step of the composed protocol is reasoned about directly.
-/

@[expose] public section

namespace Cslib.Interactive.Sumcheck

open scoped ENNReal
open Spec

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (d : ℕ)
  (P : MvPolynomial (Fin n) F)

/-- A claim: a point, of which only the coordinates below the current round matter, and a value. -/
abbrev Claim (F : Type) (n : ℕ) : Type := (Fin n → F) × F

/-- The point `r` with the coordinates from `i` on read from the Boolean point `b`. -/
def splice (i : ℕ) (r : Fin n → F) (b : Fin n → Bool) : Fin n → F :=
  fun j => if j.val < i then r j else if b j then 1 else 0

/-- The sum of `P` over the Boolean hypercube in the coordinates from `i` on, with the coordinates
below `i` fixed to `r`. Each assignment of those coordinates is counted once, by the Boolean point
that is `false` below `i`. -/
noncomputable def partialSum (i : ℕ) (r : Fin n → F) : F :=
  ∑ b : Fin n → Bool,
    if ∀ j : Fin n, j.val < i → b j = false then MvPolynomial.eval (splice i r b) P else 0

/-- The relation of round `i`: the claimed value is the partial sum. There is no witness. -/
def rel (i : ℕ) : Claim F n → Unit → Prop := fun c _ => partialSum P i c.1 = c.2

/-- The honest message of round `i`: the partial sum as a polynomial in coordinate `i`. -/
noncomputable def roundPoly (i : ℕ) (r : Fin n → F) : Polynomial F :=
  ∑ b : Fin n → Bool,
    if ∀ j : Fin n, j.val ≤ i → b j = false then
      MvPolynomial.aeval (fun j => if j.val < i then Polynomial.C (r j)
        else if j.val = i then Polynomial.X
        else Polynomial.C (if b j then 1 else 0)) P
    else 0

/-- Set coordinate `i` of `r` to `z`. -/
def setCoord (i : ℕ) (r : Fin n → F) (z : F) : Fin n → F := fun j => if j.val = i then z else r j

/-- One round: the prover sends a polynomial, read in full; the verifier sends a field element. -/
abbrev roundSpec (F : Type) [Semiring F] : Spec :=
  [.prover (Polynomial F) (OracleInterface.full _), .verifier F]

/-- The verifier's test of a round polynomial `g` against the claimed value `c`. -/
abbrev accepts (c : F) (g : Polynomial F) : Prop := g.natDegree ≤ d ∧ g.eval 0 + g.eval 1 = c

/-- Round `i` of sumcheck. -/
noncomputable def round (i : ℕ) :
    Reduction emptySpec emptySpec (roundSpec F) (Claim F n) Unit (Claim F n) Unit where
  prover x _ :=
    let g := roundPoly P i x.1
    pure (show ProbOracleComp emptySpec (Polynomial F × (F → ProbOracleComp emptySpec _)) from
      pure (g, fun z => pure ((setCoord i x.1 z, g.eval z), ())))
  verifier :=
    { samplers := (ProbComp.uniform F, ())
      decide := fun x c => do
        let g ← OracleComp.query (spec := emptySpec ⊕ₒ msgSpec (roundSpec F)) (.inr (.inl ()))
        return if accepts d x.2 g then some (setCoord i x.1 c.1, g.eval c.1) else none }

/-- The final check: evaluate `P` at the claimed point, without interaction. -/
noncomputable def finalCheck :
    Reduction emptySpec emptySpec [] (Claim F n) Unit Unit Unit where
  prover _ _ := pure ((), ())
  verifier :=
    { samplers := ()
      decide := fun x _ => pure (if MvPolynomial.eval x.1 P = x.2 then some () else none) }

/-- **Sumcheck followed by the final check**: a proof system for the claim `∑_{b ∈ {0,1}ⁿ} P b = c`
(`rel P 0`). -/
noncomputable def proof :
    Reduction emptySpec emptySpec (iterSpec (roundSpec F) n ++ []) (Claim F n) Unit Unit Unit :=
  (Reduction.iterate (round d P) n).append (finalCheck P)

/-! ### The round polynomial -/

omit [Fintype F] [DecidableEq F] in
/-- Substituting the variable at coordinate `k` and constants elsewhere gives a polynomial of
degree at most the degree of `P` in `k`. -/
private theorem natDegree_aeval_le (k : Fin n) (φ : Fin n → Polynomial F)
    (hφ : ∀ j, j ≠ k → (φ j).natDegree = 0) (hk : (φ k).natDegree ≤ 1) :
    (MvPolynomial.aeval φ P).natDegree ≤ P.degreeOf k := by
  conv_lhs => rw [P.as_sum, map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  rw [MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.monomial_le_degreeOf k hm)
  calc ∑ j ∈ m.support, ((φ j) ^ m j).natDegree
      ≤ ∑ j ∈ m.support, if k = j then m j else 0 := by
        refine Finset.sum_le_sum fun j _ => Polynomial.natDegree_pow_le.trans ?_
        by_cases hj : k = j
        · subst hj
          simpa only [ite_true, mul_one] using Nat.mul_le_mul_left (m k) hk
        · rw [hφ j (Ne.symm hj), mul_zero]
          exact Nat.zero_le _
    _ ≤ m k := by
        rw [Finset.sum_ite_eq]
        split_ifs <;> simp

omit [Fintype F] [DecidableEq F] in
/-- The round polynomial has degree at most `d`. -/
private theorem natDegree_roundPoly_le (hP : ∀ j, P.degreeOf j ≤ d) {i : ℕ} (hi : i < n)
    (r : Fin n → F) : (roundPoly P i r).natDegree ≤ d := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
  split_ifs
  · refine (natDegree_aeval_le P ⟨i, hi⟩ _ (fun j hj => ?_) ?_).trans (hP _)
    · have : j.val ≠ i := fun h => hj (Fin.ext h)
      simp only [this, ite_false]
      split_ifs <;> exact Polynomial.natDegree_C _
    · simp
  · simp

omit [Fintype F] [DecidableEq F] in
/-- The round polynomial evaluated at `t`. -/
private theorem eval_roundPoly (i : ℕ) (r : Fin n → F) (t : F) :
    (roundPoly P i r).eval t = ∑ b : Fin n → Bool,
      if ∀ j : Fin n, j.val ≤ i → b j = false then
        MvPolynomial.eval (fun j => if j.val < i then r j else if j.val = i then t
          else if b j then 1 else 0) P
      else 0 := by
  rw [roundPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs
  · rw [← Polynomial.coe_aeval_eq_eval, MvPolynomial.comp_aeval_apply,
      MvPolynomial.aeval_eq_eval]
    congr 2
    funext j
    split_ifs <;> simp
  · simp

omit [Fintype F] [DecidableEq F] in
/-- The round polynomial at `z` is the partial sum of the next round at `r` with `z` at `i`. -/
private theorem eval_roundPoly_eq (i : ℕ) (r : Fin n → F) (z : F) :
    (roundPoly P i r).eval z = partialSum P (i + 1) (setCoord i r z) := by
  rw [eval_roundPoly, partialSum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Nat.lt_succ_iff]
  congr 3
  funext j
  simp only [splice, setCoord]
  split_ifs <;> first | rfl | omega

omit [Fintype F] [DecidableEq F] in
/-- The verifier's test passes on the honest round polynomial: its values at `0` and `1` sum to
the partial sum. -/
private theorem roundPoly_eval_zero_add_one {i : ℕ} (hi : i < n) (r : Fin n → F) :
    (roundPoly P i r).eval 0 + (roundPoly P i r).eval 1 = partialSum P i r := by
  obtain ⟨k, hk⟩ : ∃ k : Fin n, k.val = i := ⟨⟨i, hi⟩, rfl⟩
  have hne {j : Fin n} (hj : j.val ≠ i) : j ≠ k := fun h => hj (h ▸ hk)
  set G : (Fin n → Bool) → F := fun b =>
    if ∀ j : Fin n, j.val < i → b j = false then MvPolynomial.eval (splice i r b) P else 0
  -- `σ` flips the Boolean coordinate `k`.
  set σ : (Fin n → Bool) → Fin n → Bool := fun b => Function.update b k (!b k)
  have hσk (b) : σ b k = !b k := Function.update_self _ _ _
  have hσj (b) (j : Fin n) (hj : j ≠ k) : σ b j = b j := Function.update_of_ne hj _ _
  have hσσ : Function.Involutive σ := fun b => by
    funext j
    by_cases hj : j = k
    · subst hj
      rw [hσk, hσk, Bool.not_not]
    · rw [hσj _ _ hj, hσj _ _ hj]
  have hcond (b : Fin n → Bool) (hb : b k = false) :
      (∀ j : Fin n, j.val ≤ i → b j = false) ↔ ∀ j : Fin n, j.val < i → b j = false := by
    refine ⟨fun h j hj => h j hj.le, fun h j hj => ?_⟩
    rcases hj.lt_or_eq with hj | hj
    · exact h j hj
    · obtain rfl : j = k := Fin.ext (hj.trans hk.symm)
      exact hb
  have hflip : ∑ b, (if b k then 0 else G (σ b)) = ∑ b, (if b k then G b else 0) := by
    rw [← Equiv.sum_comp (hσσ.toPerm σ) (fun b => if b k then G b else 0)]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Function.Involutive.coe_toPerm, hσk]
    cases b k <;> rfl
  have hsplit : partialSum P i r =
      ∑ b, (if b k then 0 else G b) + ∑ b, (if b k then G b else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    cases b k <;> simp [G]
  rw [hsplit, ← hflip, eval_roundPoly, eval_roundPoly]
  congr 1 <;> refine Finset.sum_congr rfl fun b _ => ?_ <;> cases hb : b k
  · simp only [Bool.false_eq_true, ite_false, G]
    refine if_congr (hcond b hb) (congrArg (MvPolynomial.eval · P) (funext fun j => ?_)) rfl
    by_cases hj : j.val = i
    · obtain rfl : j = k := Fin.ext (hj.trans hk.symm)
      simp [splice, hk, hb]
    · simp [splice, hj]
  · rw [ite_eq_left rfl, ite_eq_right fun h => by simpa [hb] using h k hk.le]
  · simp only [Bool.false_eq_true, ite_false, G]
    refine if_congr ((hcond b hb).trans (forall_congr' fun j => imp_congr_right fun hj => ?_))
      (congrArg (MvPolynomial.eval · P) (funext fun j => ?_)) rfl
    · rw [hσj b j (hne hj.ne)]
    · by_cases hj : j.val = i
      · obtain rfl : j = k := Fin.ext (hj.trans hk.symm)
        simp [splice, hk, hσk, hb]
      · simp [splice, hj, hσj b j (hne hj)]
  · rw [ite_eq_left rfl, ite_eq_right fun h => by simpa [hb] using h k hk.le]

omit [Fintype F] [DecidableEq F] in
/-- At round `n` all coordinates are fixed: the partial sum is the evaluation. -/
theorem partialSum_self (r : Fin n → F) : partialSum P n r = MvPolynomial.eval r P := by
  rw [partialSum, Finset.sum_eq_single (fun _ => false)]
  · have : splice n r (fun _ => false) = r := funext fun j => by simp [splice, j.isLt]
    simp [this]
  · intro b _ hb
    have : ¬ ∀ j : Fin n, j.val < n → b j = false :=
      fun h => hb (funext fun j => h j j.isLt)
    simp only [this, ite_false]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- The verifier of round `i` outputs the claim at the challenge if it accepts the message. -/
private theorem round_outputOn (i : ℕ) (x : Claim F n) (τ : Transcript (roundSpec F)) :
    (round d P i).verifier.outputOn x τ =
      if accepts d x.2 τ.1 then some (setCoord i x.1 τ.2.1, τ.1.eval τ.2.1) else none :=
  rfl

/-! ### Component theorems (milestone 2) -/

/-- Each round is perfectly complete. -/
theorem round_complete (hP : ∀ j, P.degreeOf j ≤ d) {i : ℕ} (hi : i < n) :
    (round d P i).Complete World.plain (rel P i) (rel P (i + 1)) 0 := by
  intro x w hxw
  rw [plain_eval]
  simp only [Reduction.run, Verifier.execute, lawOf₂_bind, lawOf₂_liftProver, lawOf_pure,
    PMF.pure_bind, runStrategy, lawOf_bind, lawOf_sample, lawOf₂_output, lawOf₂_pure,
    PMF.bind_bind, round_outputOn]
  simp only [round, lawOf_pure, PMF.pure_bind]
  have hacc : accepts d x.2 (roundPoly P i x.1) :=
    ⟨natDegree_roundPoly_le d P hP hi x.1, (roundPoly_eval_zero_add_one P hi x.1).trans hxw⟩
  refine toOuterMeasure_bind_le _ _ _ fun z => le_of_eq ?_
  refine (PMF.toOuterMeasure_pure_apply _ _).trans (ite_eq_right fun h => h ⟨?_, ?_⟩)
  · exact ite_eq_left hacc
  · exact (eval_roundPoly_eq P i x.1 z).symm

/-- Each round is round-by-round sound with error `d / |F|` (Schwartz–Zippel for one variable). -/
theorem round_rbrSound (hP : ∀ j, P.degreeOf j ≤ d) {i : ℕ} (hi : i < n) :
    (round d P i).verifier.RbrSound (language (rel P i)) (language (rel P (i + 1)))
      ((d : ℝ≥0∞) / Fintype.card F, ()) := by
  refine ⟨fun x p => match p with
    | none => partialSum P i x.1 = x.2
    | some (g, none) => accepts d x.2 g ∧ g = roundPoly P i x.1
    | some (g, some (z, _)) => accepts d x.2 g ∧ g.eval z = (roundPoly P i x.1).eval z,
    fun x hx h => hx ⟨(), h⟩, fun x => ⟨?_, fun g => ⟨?_, fun z => ?_⟩⟩⟩
  · rintro hS m ⟨hacc, rfl⟩
    exact hS ((roundPoly_eval_zero_add_one P hi x.1).symm.trans hacc.2)
  · intro hS
    change (ProbComp.eval (ProbComp.uniform F)).toOuterMeasure
      {c | accepts d x.2 g ∧ g.eval c = (roundPoly P i x.1).eval c} ≤ (d : ℝ≥0∞) / Fintype.card F
    by_cases hacc : accepts d x.2 g
    · have hne : g - roundPoly P i x.1 ≠ 0 := sub_ne_zero.mpr fun h => hS ⟨hacc, h⟩
      classical
      rw [ProbComp.eval_uniform, Probability.PMF.toOuterMeasure_uniformOfFintype, div_eq_mul_inv]
      gcongr
      have hsub : Finset.univ.filter
          (· ∈ {c | accepts d x.2 g ∧ g.eval c = (roundPoly P i x.1).eval c}) ⊆
          (g - roundPoly P i x.1).roots.toFinset := by
        intro c hc
        simp only [Finset.mem_filter, Set.mem_ofPred_eq] at hc
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot,
          Polynomial.eval_sub, hc.2.2, sub_self]
      exact_mod_cast (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans
        ((Polynomial.card_roots' _).trans ((Polynomial.natDegree_sub_le _ _).trans
          (max_le hacc.1 (natDegree_roundPoly_le d P hP hi x.1)))))
    · simp [hacc]
  · rintro hS ⟨x', ⟨_, hx'⟩, hout⟩
    rw [round_outputOn] at hout
    split_ifs at hout with hacc
    obtain rfl := Option.some.inj hout
    exact hS ⟨hacc, hx'.symm.trans (eval_roundPoly_eq P i x.1 z).symm⟩

omit [Fintype F] in
/-- The final check is perfectly complete. -/
theorem finalCheck_complete :
    (finalCheck P).Complete World.plain (rel P n) Accept 0 := by
  intro x w hxw
  rw [rel, partialSum_self] at hxw
  rw [plain_eval]
  simp only [Reduction.run, Verifier.execute, lawOf₂_bind, lawOf₂_liftProver, lawOf_pure,
    PMF.pure_bind, runStrategy, lawOf₂_output, lawOf₂_pure, finalCheck]
  refine le_of_eq ((PMF.toOuterMeasure_pure_apply _ _).trans
    (ite_eq_right fun h => h ⟨ite_eq_left hxw, trivial⟩))

omit [Fintype F] in
/-- The final check is round-by-round sound without error. -/
theorem finalCheck_rbrSound :
    (finalCheck P).verifier.RbrSound (language (rel P n)) Set.univ () := by
  refine ⟨fun x _ => MvPolynomial.eval x.1 P = x.2,
    fun x hx h => hx ⟨(), by rw [rel, partialSum_self]; exact h⟩,
    fun x hS ⟨x', _, hout⟩ => hS ?_⟩
  by_contra h
  simp [Verifier.outputOn, finalCheck, h] at hout

/-! ### End-to-end theorems, by composition -/

/-- **Completeness of sumcheck with the final check.** -/
theorem proof_complete (hP : ∀ j, P.degreeOf j ≤ d) :
    (proof d P).Complete World.plain (rel P 0) Accept 0 := by
  have h := (Reduction.Complete.iterate (rel := rel P) n fun i hi =>
    round_complete d P hP hi).append (finalCheck_complete P)
  simp only [Finset.sum_const_zero, add_zero] at h
  exact h

/-- **Soundness of sumcheck with the final check**: a false claim is accepted with probability at
most `n * (d / |F|)`. -/
theorem proof_sound (hP : ∀ j, P.degreeOf j ≤ d) :
    (proof d P).verifier.Sound (oP := emptySpec) World.plain (language (rel P 0)) Set.univ
      (n * ((d : ℝ≥0∞) / Fintype.card F)) := by
  have h := ((Verifier.RbrSound.iterate (R := round d P) (L := fun i => language (rel P i)) n
    fun i hi => round_rbrSound d P hP hi).append (finalCheck_rbrSound P)).sound
  simp only [PerChallenge.sum_append, PerChallenge.sum_iterate] at h
  simp only [PerChallenge.sum, add_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  exact h

end Cslib.Interactive.Sumcheck
