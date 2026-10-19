/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.TQBF
public import Complexity.Languages.Probabilistic.Oracle
public import Complexity.Logics.Propositional.QBF.Arithmetization
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.List.GetD

/-!
# The interactive proof for quantified Boolean formulas

The protocol of Shamir with Shen's linearization [Shamir][Shamir1992], [Shen][Shen1992],
[Arora and Barak, Section 8.5][AroraBarak09], built on the sum-check protocol of Lund, Fortnow,
Karloff and Nisan [LundFortnowKarloffNisan1992], for an arithmetic formula `e` with operators
`∃`, `∀` and linearization (`Cslib.Logic.PL.ArithQBF`) over a commutative ring `F`. The verifier
(`Cslib.Complexity.QBFProtocol.verify`) checks a claim `e.eval r = c` about the value of `e` at a
point `r`, by recursion on `e`:

* at a variable or a constant it checks the claim directly, and a negation `not e` reduces the
  claim to `e.eval r = 1 - c`;
* at a binary connective it asks the prover for the values `c₁` and `c₂` of the two arguments,
  checks that they combine to `c`, and checks the claims `c₁` and `c₂` in turn;
* at an operator binding `x` it asks the prover for the polynomial `s` that the restriction of the
  body to `x` (`Cslib.Logic.PL.ArithQBF.restrict`) should be, as a list of coefficients of which
  it keeps the first `deg x + 1`; it checks that the values `s 0` and `s 1` combine to `c`, draws
  `z` from the sampler, and checks the claim that the body has value `s z` at `r` with `x` set to
  `z`.

The verifier is a program with typed calls to the prover (`Cslib.ProbOracleComp`): each query
sends the current subformula and point, each reply is a list of ring elements, and the field
elements are drawn from an arbitrary closed probabilistic program `sampler`. A prover is any
stateful probabilistic strategy `respond` answering the queries, with an arbitrary type of states,
interpreted as in `Cslib.Complexity.Prover.run`.

**Completeness.** The honest prover (`Cslib.Complexity.QBFProtocol.honest`) answers with the true
values and restrictions, and is accepted with probability `1` on every true claim
(`Cslib.Complexity.QBFProtocol.acceptProb_honest_verify`).

**Soundness.** If the sampler gives every element probability at most `ε` and `F` is an integral
domain, every prover is accepted on a false claim with probability at most
`e.roundDegree * ε` (`Cslib.Complexity.QBFProtocol.acceptProb_verify_le`): at an operator, a
wrong polynomial agrees with the true restriction, both of degree at most `deg x`, on at most
`deg x` points, and otherwise the claim passed on is false again. For the uniform distribution on
a finite field this is `e.roundDegree / |F|`.

For a closed formula `φ`, the arithmetization `φ.arithmetize xs` has value `1` at the origin when
`φ` is true and `0` when it is false (`Cslib.Logic.PL.QBF.eval_arithmetize_zero`), and its round
degrees sum to at most `(2 * |xs| + 1) * size φ ^ 2` when `xs` contains the variables of `φ`. The
claim that it has value `1` at the origin is therefore accepted with probability `1` from a true
formula, and with probability at most `3 * size φ ^ 3 / |F|` from a false one
(`Cslib.Complexity.QBFProtocol.acceptProb_honest_of_mem_TQBF`,
`Cslib.Complexity.QBFProtocol.acceptProb_le_of_notMem_TQBF`). Realizing the verifier as an
efficient machine in the model of `Cslib.Complexity.IP`, with a field of polynomial size and field
elements drawn from fair coins, is not done here.

## Main definitions

* `Cslib.Complexity.QBFProtocol.verify`: the verifier.
* `Cslib.Complexity.QBFProtocol.run`, `Cslib.Complexity.QBFProtocol.acceptProb`: an interaction
  with a stateful prover and its acceptance probability.
* `Cslib.Complexity.QBFProtocol.honest`: the honest prover.
* `Cslib.Complexity.QBFProtocol.ofCoeffs`, `Cslib.Complexity.QBFProtocol.evalCoeffs`: polynomials
  given by coefficient lists, and their Horner evaluation.

## Main results

* `Cslib.Complexity.QBFProtocol.acceptProb_honest_verify`: perfect completeness.
* `Cslib.Complexity.QBFProtocol.acceptProb_verify_le`,
  `Cslib.Complexity.QBFProtocol.acceptProb_verify_uniform_le`: soundness against every prover.
* `Cslib.Complexity.QBFProtocol.acceptProb_honest_arithmetize`,
  `Cslib.Complexity.QBFProtocol.acceptProb_arithmetize_le`: the protocol for closed quantified
  Boolean formulas.
* `Cslib.Complexity.QBFProtocol.acceptProb_honest_of_mem_TQBF`,
  `Cslib.Complexity.QBFProtocol.acceptProb_le_of_notMem_TQBF`: the protocol for `TQBF` over a
  finite field.

## References

* [C. Lund, L. Fortnow, H. Karloff, N. Nisan, *Algebraic methods for interactive proof
  systems*][LundFortnowKarloffNisan1992]
* [A. Shamir, *IP = PSPACE*][Shamir1992]
* [A. Shen, *IP = SPACE: simplified proof*][Shen1992]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.QBFProtocol

open Cslib.Logic.PL Polynomial
open scoped ENNReal

variable {V F : Type}

/-! ### Coefficient lists -/

section Coeffs

variable [CommRing F]

/-- The polynomial with coefficient list `l`, the constant coefficient first. -/
noncomputable def ofCoeffs : List F → F[X]
  | [] => 0
  | a :: l => C a + X * ofCoeffs l

/-- The value at `z` of the polynomial with coefficient list `l`, by Horner's rule. -/
def evalCoeffs (z : F) : List F → F
  | [] => 0
  | a :: l => a + z * evalCoeffs z l

/-- The first `n` coefficients of a polynomial. -/
noncomputable def coeffList (g : F[X]) (n : ℕ) : List F := (List.range n).map g.coeff

theorem eval_ofCoeffs (z : F) (l : List F) : (ofCoeffs l).eval z = evalCoeffs z l := by
  induction l with
  | nil => simp only [ofCoeffs, evalCoeffs, eval_zero]
  | cons a l ih => simp only [ofCoeffs, evalCoeffs, eval_add, eval_C, eval_mul, eval_X, ih]

theorem coeff_ofCoeffs (l : List F) (i : ℕ) : (ofCoeffs l).coeff i = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp only [ofCoeffs, coeff_zero, List.getD_nil]
  | cons a l ih =>
    cases i with
    | zero => simp only [ofCoeffs, coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero,
        List.getD_cons_zero]
    | succ i => simp only [ofCoeffs, coeff_add, coeff_C_succ, coeff_X_mul, ih, zero_add,
        List.getD_cons_succ]

theorem natDegree_ofCoeffs_le (l : List F) : (ofCoeffs l).natDegree ≤ l.length - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_ofCoeffs, List.getD_eq_default _ _ (by omega)]

/-- The first `n` coefficients of a polynomial of degree less than `n` give the polynomial back. -/
theorem ofCoeffs_coeffList {g : F[X]} {n : ℕ} (hg : g.natDegree < n) :
    ofCoeffs (coeffList g n) = g := by
  ext i
  rw [coeff_ofCoeffs, coeffList]
  by_cases hi : i < n
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
      Option.getD_some]
  · rw [List.getD_eq_default _ _ (by simp only [List.length_map, List.length_range]; omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

@[simp] theorem length_coeffList (g : F[X]) (n : ℕ) : (coeffList g n).length = n := by
  simp only [coeffList, List.length_map, List.length_range]

end Coeffs

/-! ### Queries and interaction with a prover -/

/-- A query of the verifier: the subformula whose claim it is checking, and the current point. -/
abbrev Query (V F : Type) := ArithQBF V × (V → F)

/-- Every reply of the prover is a list of ring elements. -/
abbrev Spec (V F : Type) : Query V F → Type := fun _ => List F

section Run

variable {S α β : Type} (respond : Query V F → StateT S PMF (List F))

/-- The joint law of the result of `program` and the final state of the prover answering its
queries with `respond`, starting from the state `s`. Samples are fresh. -/
noncomputable def run (program : ProbOracleComp (Spec V F) α) (s : S) : PMF (α × S) :=
  (OracleComp.interpret
    (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) respond) program).run s

/-- The probability that `program` accepts against the prover `respond` from the state `s`. -/
noncomputable def acceptProb (program : ProbOracleComp (Spec V F) Bool) (s : S) : ℝ≥0∞ :=
  (run respond program s).map Prod.fst true

theorem run_pure (a : α) (s : S) : run respond (pure a) s = PMF.pure (a, s) := rfl

theorem run_bind (program : ProbOracleComp (Spec V F) α)
    (next : α → ProbOracleComp (Spec V F) β) (s : S) :
    run respond (program >>= next) s =
      (run respond program s).bind fun x => run respond (next x.1) x.2 := by
  simp only [run, OracleComp.interpret_bind, StateT.run_bind]
  rfl

theorem run_query (q : Query V F) (s : S) :
    run respond (ProbOracleComp.query (spec := Spec V F) q) s = respond q s := by
  simp only [run, ProbOracleComp.interpret_query]
  rfl

theorem run_sample (program : ProbComp α) (s : S) :
    run respond (ProbOracleComp.sample (spec := Spec V F) program) s =
      (ProbComp.eval program).map (·, s) :=
  ProbOracleComp.run_interpret_sample _ _ _

theorem acceptProb_pure (b : Bool) (s : S) :
    acceptProb respond (pure b) s = if b then 1 else 0 := by
  rw [acceptProb, run_pure, PMF.pure_map, PMF.pure_apply]
  cases b <;> simp

theorem acceptProb_le_one (program : ProbOracleComp (Spec V F) Bool) (s : S) :
    acceptProb respond program s ≤ 1 :=
  PMF.coe_le_one _ _

theorem acceptProb_bind (program : ProbOracleComp (Spec V F) α)
    (next : α → ProbOracleComp (Spec V F) Bool) (s : S) :
    acceptProb respond (program >>= next) s =
      ∑' x, run respond program s x * acceptProb respond (next x.1) x.2 := by
  rw [acceptProb, run_bind, PMF.map_bind, PMF.bind_apply]
  rfl

theorem acceptProb_query_bind (q : Query V F) (next : List F → ProbOracleComp (Spec V F) Bool)
    (s : S) :
    acceptProb respond (ProbOracleComp.query (spec := Spec V F) q >>= next) s =
      ∑' x, respond q s x * acceptProb respond (next x.1) x.2 := by
  rw [acceptProb_bind, run_query]

theorem acceptProb_sample_bind (program : ProbComp α) (next : α → ProbOracleComp (Spec V F) Bool)
    (s : S) :
    acceptProb respond (ProbOracleComp.sample program >>= next) s =
      ∑' a, ProbComp.eval program a * acceptProb respond (next a) s := by
  rw [acceptProb, run_bind, run_sample, PMF.bind_map, PMF.map_bind, PMF.bind_apply]
  rfl

/-- Running a second check only after a first one accepted accepts at most as often as the first
check. -/
theorem acceptProb_bind_ite_le (program : ProbOracleComp (Spec V F) Bool)
    (next : ProbOracleComp (Spec V F) Bool) (s : S) :
    acceptProb respond (program >>= fun b => if b then next else pure false) s ≤
      acceptProb respond program s := by
  conv_rhs => rw [← bind_pure program, acceptProb_bind]
  rw [acceptProb_bind]
  refine ENNReal.tsum_le_tsum fun x => mul_le_mul_right ?_ _
  cases x.1
  · simp only [Bool.false_eq_true, ↓reduceIte, le_refl]
  · simp only [↓reduceIte, acceptProb_pure]
    exact acceptProb_le_one _ _ _

end Run

/-! ### The verifier -/

variable [DecidableEq V] [CommRing F] [DecidableEq F] (sampler : ProbComp F)

/-- **The verifier** checking the claim that `e` has value `c` at `r`, drawing ring elements from
`sampler`. At a binary connective the reply `[c₁, c₂, …]` gives the claimed values of the
arguments, and at an operator binding `x` the first `deg x + 1` elements of the reply are the
coefficients of the claimed restriction of the body to `x`; missing entries count as `0`. -/
def verify : ArithQBF V → (V → F) → F → ProbOracleComp (Spec V F) Bool
  | .var v, r, c => pure (decide (r v = c))
  | .top, _, c => pure (decide (c = 1))
  | .bot, _, c => pure (decide (c = 0))
  | .not e, r, c => verify e r (1 - c)
  | .bin o e₁ e₂, r, c => do
    let l ← ProbOracleComp.query (spec := Spec V F) (.bin o e₁ e₂, r)
    if o.apply (l.getD 0 0) (l.getD 1 0) = c then
      let b ← verify e₁ r (l.getD 0 0)
      if b then verify e₂ r (l.getD 1 0) else pure false
    else pure false
  | .op o v e, r, c => do
    let l ← ProbOracleComp.query (spec := Spec V F) (.op o v e, r)
    let s := l.take (e.deg v + 1)
    if o.apply (r v) (evalCoeffs 0 s) (evalCoeffs 1 s) = c then
      let z ← ProbOracleComp.sample sampler
      verify e (Function.update r v z) (evalCoeffs z s)
    else pure false

/-! ### Averages -/

/-- An average of values at most `B` is at most `B`. -/
private theorem tsum_mul_le {α : Type} (μ : PMF α) {f : α → ℝ≥0∞} {B : ℝ≥0∞}
    (h : ∀ a, f a ≤ B) : ∑' a, μ a * f a ≤ B :=
  calc ∑' a, μ a * f a ≤ ∑' a, μ a * B := ENNReal.tsum_le_tsum fun a => mul_le_mul_right (h a) _
    _ = B := by rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

/-- Values at most `1` on a finite set `T` and at most `B` elsewhere average to at most
`|T| * ε + B` under a distribution giving every point probability at most `ε`. -/
private theorem tsum_mul_le_card_mul_add {α : Type} [DecidableEq α] (μ : PMF α) {ε : ℝ≥0∞}
    (hμ : ∀ a, μ a ≤ ε) (T : Finset α) {f : α → ℝ≥0∞} {B : ℝ≥0∞}
    (h : ∀ a, f a ≤ (if a ∈ T then 1 else 0) + B) : ∑' a, μ a * f a ≤ T.card * ε + B := by
  calc ∑' a, μ a * f a ≤ ∑' a, (μ a * (if a ∈ T then 1 else 0) + μ a * B) :=
        ENNReal.tsum_le_tsum fun a => (mul_le_mul_right (h a) _).trans_eq (mul_add _ _ _)
    _ = ∑ a ∈ T, μ a + B := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, μ.tsum_coe, one_mul,
          tsum_eq_sum (s := T) fun a ha => by simp only [ha, ↓reduceIte, mul_zero]]
        congr 1
        exact Finset.sum_congr rfl fun a ha => by simp only [ha, ↓reduceIte, mul_one]
    _ ≤ T.card * ε + B := by
        gcongr
        calc ∑ a ∈ T, μ a ≤ ∑ _a ∈ T, ε := Finset.sum_le_sum fun a _ => hμ a
          _ = T.card * ε := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ### Completeness -/

/-- The reply of the honest prover: the values of the two arguments of a binary connective, and
the `deg x + 1` coefficients of the restriction of the body of an operator binding `x`. -/
noncomputable def honestReply : Query V F → List F
  | (.bin _ e₁ e₂, r) => [e₁.eval r, e₂.eval r]
  | (.op _ v e, r) => coeffList (e.restrict r v) (e.deg v + 1)
  | _ => []

/-- The honest prover, which keeps no state. -/
noncomputable def honest : Query V F → StateT Unit PMF (List F) :=
  fun q s => PMF.pure (honestReply q, s)

/-- Against the honest prover, the verifier accepts every true claim with certainty. -/
theorem run_honest_verify (e : ArithQBF V) (r : V → F) (s : Unit) :
    run honest (verify sampler e r (e.eval r)) s = PMF.pure (true, s) := by
  induction e generalizing r with
  | var v => simp only [verify, ArithQBF.eval_var, decide_true, run_pure]
  | top => simp only [verify, ArithQBF.eval_top, decide_true, run_pure]
  | bot => simp only [verify, ArithQBF.eval_bot, decide_true, run_pure]
  | not e ih => rw [verify, ArithQBF.eval_not, sub_sub_cancel, ih]
  | bin o e₁ e₂ ih₁ ih₂ =>
    rw [verify, run_bind, run_query]
    simp only [honest, honestReply, PMF.pure_bind, List.getD_cons_zero, List.getD_cons_succ,
      ArithQBF.eval_bin, ↓reduceIte]
    rw [run_bind, ih₁, PMF.pure_bind]
    exact ih₂ r
  | op o v e ih =>
    rw [verify, run_bind, run_query]
    have hlist : (coeffList (e.restrict r v) (e.deg v + 1)).take (e.deg v + 1) =
        coeffList (e.restrict r v) (e.deg v + 1) :=
      List.take_of_length_le (by rw [length_coeffList])
    have hval (z : F) : evalCoeffs z (coeffList (e.restrict r v) (e.deg v + 1)) =
        e.eval (Function.update r v z) := by
      rw [← eval_ofCoeffs, ofCoeffs_coeffList (Nat.lt_succ_of_le (e.natDegree_restrict_le r v)),
        ArithQBF.eval_restrict]
    simp only [honest, honestReply, PMF.pure_bind, hlist, hval, ArithQBF.eval_op, ↓reduceIte]
    rw [run_bind, run_sample, PMF.bind_map]
    simp only [Function.comp_def, ih]
    exact PMF.bind_const _ _

/-- **Perfect completeness**: the honest prover is accepted on every true claim with
probability `1`. -/
theorem acceptProb_honest_verify (e : ArithQBF V) (r : V → F) :
    acceptProb honest (verify sampler e r (e.eval r)) () = 1 := by
  rw [acceptProb, run_honest_verify, PMF.pure_map, PMF.pure_apply]
  exact ite_eq_left rfl

/-! ### Soundness -/

/-- **Soundness**: if the sampler gives every element probability at most `ε`, every prover is
accepted on a false claim with probability at most `e.roundDegree * ε`. -/
theorem acceptProb_verify_le [IsDomain F] {ε : ℝ≥0∞}
    (hsampler : ∀ z, ProbComp.eval sampler z ≤ ε) {S : Type}
    (respond : Query V F → StateT S PMF (List F)) (e : ArithQBF V) {r : V → F} {c : F}
    (hc : e.eval r ≠ c) (s : S) :
    acceptProb respond (verify sampler e r c) s ≤ e.roundDegree * ε := by
  induction e generalizing r c s with
  | var v =>
    rw [verify, decide_eq_false (show r v ≠ c from hc), acceptProb_pure]
    exact zero_le
  | top =>
    rw [verify, decide_eq_false (show c ≠ 1 from Ne.symm hc), acceptProb_pure]
    exact zero_le
  | bot =>
    rw [verify, decide_eq_false (show c ≠ 0 from Ne.symm hc), acceptProb_pure]
    exact zero_le
  | not e ih =>
    rw [verify, ArithQBF.roundDegree]
    exact ih (fun h => hc (by rw [ArithQBF.eval_not, h, sub_sub_cancel])) s
  | bin o e₁ e₂ ih₁ ih₂ =>
    rw [verify, acceptProb_query_bind]
    refine tsum_mul_le _ fun x => ?_
    split_ifs with hcheck
    · by_cases h₁ : e₁.eval r = x.1.getD 0 0
      · have h₂ : e₂.eval r ≠ x.1.getD 1 0 := fun h₂ =>
          hc (by rw [ArithQBF.eval_bin, h₁, h₂, hcheck])
        rw [acceptProb_bind]
        refine (tsum_mul_le (B := (e₂.roundDegree : ℝ≥0∞) * ε) _ fun y => ?_).trans ?_
        · cases y.1
          · simp only [Bool.false_eq_true, ↓reduceIte, acceptProb_pure]
            exact zero_le
          · simp only [↓reduceIte]
            exact ih₂ h₂ _
        · rw [ArithQBF.roundDegree, Nat.cast_add, add_mul]
          exact le_add_self
      · refine (acceptProb_bind_ite_le respond _ _ _).trans ((ih₁ h₁ _).trans ?_)
        rw [ArithQBF.roundDegree, Nat.cast_add, add_mul]
        exact le_self_add
    · rw [acceptProb_pure]
      exact zero_le
  | op o v e ih =>
    rw [verify, acceptProb_query_bind]
    refine tsum_mul_le _ fun x => ?_
    simp only
    split_ifs with hcheck
    · rw [acceptProb_sample_bind]
      set g := e.restrict r v
      set p := ofCoeffs (x.1.take (e.deg v + 1))
      have hp (z : F) : evalCoeffs z (x.1.take (e.deg v + 1)) = p.eval z := (eval_ofCoeffs z _).symm
      have hg (z : F) : g.eval z = e.eval (Function.update r v z) := e.eval_restrict r v z
      have hne : p - g ≠ 0 := by
        intro h
        rw [sub_eq_zero] at h
        apply hc
        rw [ArithQBF.eval_op, ← hg, ← hg, ← h, ← hp, ← hp, hcheck]
      have hdeg : (p - g).natDegree ≤ e.deg v :=
        (natDegree_sub_le _ _).trans (max_le ((natDegree_ofCoeffs_le _).trans (by
          rw [List.length_take]; omega)) (e.natDegree_restrict_le r v))
      classical
      have hcard : ((p - g).roots.toFinset.card : ℝ≥0∞) ≤ e.deg v := by
        exact_mod_cast (Multiset.toFinset_card_le _).trans ((card_roots' _).trans hdeg)
      refine (tsum_mul_le_card_mul_add _ hsampler (p - g).roots.toFinset
        (B := e.roundDegree * ε) fun z => ?_).trans ?_
      · by_cases hz : p.eval z = g.eval z
        · have : z ∈ (p - g).roots.toFinset := by
            rw [Multiset.mem_toFinset, mem_roots hne, IsRoot, eval_sub, hz, sub_self]
          simp only [this, ↓reduceIte]
          exact (acceptProb_le_one _ _ _).trans le_self_add
        · rw [hp]
          refine (ih (fun h => hz ?_) _).trans le_add_self
          rw [hg, h]
      · rw [ArithQBF.roundDegree, Nat.cast_add, add_mul]
        gcongr
    · rw [acceptProb_pure]
      exact zero_le

/-- **Soundness for uniform samples**: with ring elements drawn uniformly from a finite integral
domain, every prover is accepted on a false claim with probability at most
`e.roundDegree / |F|`. -/
theorem acceptProb_verify_uniform_le [IsDomain F] [Fintype F] {S : Type}
    (respond : Query V F → StateT S PMF (List F)) (e : ArithQBF V) {r : V → F} {c : F}
    (hc : e.eval r ≠ c) (s : S) :
    acceptProb respond (verify (ProbComp.uniform F) e r c) s ≤ e.roundDegree / Fintype.card F := by
  rw [div_eq_mul_inv]
  exact acceptProb_verify_le _
    (fun z => by rw [ProbComp.eval_uniform, Probability.PMF.uniformOfFintype_apply]) respond e hc s

/-! ### Quantified Boolean formulas -/

/-- **Completeness for quantified Boolean formulas**: on a true closed formula, the honest prover
is accepted with probability `1` on the claim that the arithmetization has value `1` at the
origin. -/
theorem acceptProb_honest_arithmetize (xs : List V) {φ : QBF V} (hφ : φ.Closed)
    (htrue : φ.eval (fun _ => false) = true) :
    acceptProb honest (verify sampler (φ.arithmetize xs) 0 1) () = 1 := by
  have h := QBF.eval_arithmetize_zero (R := F) xs hφ (fun _ => false)
  simp only [htrue, ↓reduceIte] at h
  have hacc := acceptProb_honest_verify sampler (φ.arithmetize xs) 0
  rwa [h] at hacc

/-- **Soundness for quantified Boolean formulas**: on a false closed formula whose variables are
all in `xs`, every prover is accepted on the claim that the arithmetization has value `1` at the
origin with probability at most `(2 * |xs| + 1) * size φ ^ 2 * ε`, if the sampler gives every
element probability at most `ε`. -/
theorem acceptProb_arithmetize_le [IsDomain F] {ε : ℝ≥0∞}
    (hsampler : ∀ z, ProbComp.eval sampler z ≤ ε) {xs : List V} {φ : QBF V} (hφ : φ.Closed)
    (hxs : ∀ v ∈ φ.vars, v ∈ xs) (hfalse : φ.eval (fun _ => false) = false) {S : Type}
    (respond : Query V F → StateT S PMF (List F)) (s : S) :
    acceptProb respond (verify sampler (φ.arithmetize xs) 0 1) s ≤
      ((2 * xs.length + 1) * φ.size ^ 2 : ℕ) * ε := by
  have h := QBF.eval_arithmetize_zero (R := F) xs hφ (fun _ => false)
  simp only [hfalse, Bool.false_eq_true, ↓reduceIte] at h
  refine (acceptProb_verify_le sampler hsampler respond _ (by rw [h]; exact zero_ne_one) s).trans ?_
  gcongr
  exact QBF.roundDegree_arithmetize_le hxs

/-- **Completeness for `TQBF`**: on a true closed formula, the honest prover is accepted with
probability `1`. -/
theorem acceptProb_honest_of_mem_TQBF {φ : QBF ℕ} (hφ : φ ∈ TQBF) :
    acceptProb honest (verify sampler (φ.arithmetize φ.vars) 0 1) () = 1 :=
  acceptProb_honest_arithmetize sampler _ hφ.1 hφ.2

/-- **Soundness for `TQBF`**: on a false closed formula `φ`, with field elements drawn uniformly
from a finite field `F`, every prover is accepted with probability at most
`3 * size φ ^ 3 / |F|`. -/
theorem acceptProb_le_of_notMem_TQBF [IsDomain F] [Fintype F] {φ : QBF ℕ} (hφ : φ.Closed)
    (hφ' : φ ∉ TQBF) {S : Type} (respond : Query ℕ F → StateT S PMF (List F)) (s : S) :
    acceptProb respond (verify (ProbComp.uniform F) (φ.arithmetize φ.vars) 0 1) s ≤
      ((3 * φ.size ^ 3 : ℕ) : ℝ≥0∞) / Fintype.card F := by
  have hfalse : φ.eval (fun _ => false) = false := Bool.eq_false_iff.2 fun h => hφ' ⟨hφ, h⟩
  have h := QBF.eval_arithmetize_zero (R := F) φ.vars hφ (fun _ => false)
  simp only [hfalse, Bool.false_eq_true, ↓reduceIte] at h
  refine (acceptProb_verify_uniform_le respond _ (by rw [h]; exact zero_ne_one) s).trans ?_
  gcongr
  have hrd := QBF.roundDegree_arithmetize_le (xs := φ.vars) (φ := φ) fun _ hv => hv
  have hlen := QBF.length_vars_le_size φ
  have hs := QBF.one_le_size φ
  refine hrd.trans ?_
  calc (2 * φ.vars.length + 1) * φ.size ^ 2 ≤ (3 * φ.size) * φ.size ^ 2 :=
        Nat.mul_le_mul_right _ (by omega)
    _ = 3 * φ.size ^ 3 := by ring

end Cslib.Complexity.QBFProtocol
