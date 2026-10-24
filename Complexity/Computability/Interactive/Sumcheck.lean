/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (design prototype for #643; not for merge)

public import Complexity.Computability.Interactive.Sequential
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

/-! ### Component theorems (milestone 2) -/

/-- Each round is perfectly complete. -/
theorem round_complete (hP : ∀ j, P.degreeOf j ≤ d) {i : ℕ} (hi : i < n) :
    (round d P i).Complete World.plain (rel P i) (rel P (i + 1)) 0 := by
  sorry

/-- Each round is round-by-round sound with error `d / |F|` (Schwartz–Zippel for one variable). -/
theorem round_rbrSound (hP : ∀ j, P.degreeOf j ≤ d) {i : ℕ} (hi : i < n) :
    (round d P i).verifier.RbrSound (language (rel P i)) (language (rel P (i + 1)))
      ((d : ℝ≥0∞) / Fintype.card F, ()) := by
  sorry

omit [Fintype F] in
/-- The final check is perfectly complete. -/
theorem finalCheck_complete :
    (finalCheck P).Complete World.plain (rel P n) Accept 0 := by
  sorry

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
