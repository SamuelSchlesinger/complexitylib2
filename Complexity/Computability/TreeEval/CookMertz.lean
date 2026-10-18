/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Basic
public import Complexity.Foundations.BooleanAnalysis.MultilinearExtension
public import Complexity.Foundations.FieldTheory.Finite.UnitSum

/-!
# The Cook–Mertz procedure for Tree Evaluation

The procedure keeps three registers, each holding `ℓ` elements of a finite field `K`, as global
storage shared by all levels of the recursion. Called on a subtree, a coefficient `c` and a target
register `t`, it adds `c` times the value of the subtree (read as `0`/`1` field elements) to
register `t` and leaves the other two registers unchanged, whatever their contents.

At an internal node with gate `f`, the procedure runs one round for every unit `u` of `K`. A
round scales the two other registers `a` and `b` by `u`, adds the children's values `v₀` and `v₁`
to them by recursive calls, subtracts `c` times the multilinear extension of `f` at the masked
values `u • a + v₀` and `u • b + v₁` from register `t`, and then undoes the recursive calls and the
scaling. Summed over all units, the masks cancel (`FiniteField.sum_units_eval_mul_add`), because
the extension has degree at most `2ℓ < |K| - 1`, and register `t` has gained `c • f v₀ v₁`.

Only the recursion depth, the round counter and the stage within a round are local to a level;
this is what makes the procedure space-efficient. This file proves its correctness; space bounds
are separate.

## Main definitions

* `Cslib.TreeEval.gatePoly`: the multilinear extension of an output bit of a gate.
* `Cslib.TreeEval.proc`: the procedure, parametrized by an enumeration of the units of `K`.

## Main results

* `Cslib.TreeEval.proc_eq`: the procedure adds `c` times the value of the tree to the target
  register and leaves the other registers unchanged.
* `Cslib.TreeEval.proc_zero`: started from zero registers, it leaves the value of the tree in the
  target register.
* `Cslib.TreeEval.embed_eval_eq_proc`: the same, for the canonical enumeration of the units.

## References

* [J. Cook and I. Mertz, *Tree Evaluation is in Space O(log n · log log n)*][CookMertz2024],
  Lemma 13 and Theorem 10.
* [O. Goldreich, *On the Cook–Mertz Tree Evaluation procedure*][Goldreich2024TreeEval],
  Algorithm 1, whose signed recursive calls are followed here.
-/

@[expose] public section

open MvPolynomial Cslib.BitString

namespace Cslib.TreeEval

variable {K : Type*} [Field K] {ℓ : ℕ}

/-- The global storage: three registers of `ℓ` field elements. -/
abbrev State (K : Type*) (ℓ : ℕ) := Fin 3 → Fin ℓ → K

/-- An `ℓ`-bit value read as `0`/`1` field elements. -/
def embed (v : Fin ℓ → Bool) : Fin ℓ → K := fun i => bitVal K (v i)

/-- The multilinear extension of output bit `i` of a gate, in the bits of both inputs. -/
noncomputable def gatePoly (f : (Fin ℓ → Bool) → (Fin ℓ → Bool) → Fin ℓ → Bool) (i : Fin ℓ) :
    MvPolynomial (Fin ℓ ⊕ Fin ℓ) K :=
  multilinearExtension fun z => bitVal K (f (z ∘ Sum.inl) (z ∘ Sum.inr) i)

/-- Multiply register `r` by `a`. -/
def scale (r : Fin 3) (a : K) (S : State K ℓ) : State K ℓ :=
  Function.update S r (a • S r)

/-- One round of the procedure at a gate `f`, for the unit `u`, given procedures `pl` and `pr`
for the two subtrees. The target is `t`, and the registers `t + 1` and `t + 2` hold the masks. -/
noncomputable def gateRound (pl pr : K → Fin 3 → State K ℓ → State K ℓ)
    (f : (Fin ℓ → Bool) → (Fin ℓ → Bool) → Fin ℓ → Bool) (c : K) (t : Fin 3) (u : Kˣ)
    (S : State K ℓ) : State K ℓ :=
  let S := pl 1 (t + 1) (scale (t + 1) (u : K) S)
  let S := pr 1 (t + 2) (scale (t + 2) (u : K) S)
  let S := Function.update S t fun i =>
    S t i - c * eval (Sum.elim (S (t + 1)) (S (t + 2))) (gatePoly f i)
  let S := scale (t + 1) ((u⁻¹ : Kˣ) : K) (pl (-1) (t + 1) S)
  scale (t + 2) ((u⁻¹ : Kˣ) : K) (pr (-1) (t + 2) S)

/-- The Cook–Mertz procedure: add `c` times the value of the tree to register `t`. At a gate it
runs one `gateRound` for every unit in the enumeration `us`. -/
noncomputable def proc (us : List Kˣ) :
    {h : ℕ} → Tree ℓ h → K → Fin 3 → State K ℓ → State K ℓ
  | _, .leaf v, c, t, S => Function.update S t (S t + c • embed v)
  | _, .node f l r, c, t, S => us.foldl (fun S u => gateRound (proc us l) (proc us r) f c t u S) S

private theorem add_one_ne (t : Fin 3) : t + 1 ≠ t := by revert t; decide
private theorem add_two_ne (t : Fin 3) : t + 2 ≠ t := by revert t; decide
private theorem add_two_ne_add_one (t : Fin 3) : t + 2 ≠ t + 1 := by revert t; decide

/-- A round, when both subtree procedures meet their specification, changes only the target
register, by `c` times the gate's extension at the masked children's values. -/
theorem gateRound_eq {pl pr : K → Fin 3 → State K ℓ → State K ℓ} {vl vr : Fin ℓ → K}
    (hl : ∀ c t S, pl c t S = Function.update S t (S t + c • vl))
    (hr : ∀ c t S, pr c t S = Function.update S t (S t + c • vr))
    (f : (Fin ℓ → Bool) → (Fin ℓ → Bool) → Fin ℓ → Bool) (c : K) (t : Fin 3) (u : Kˣ)
    (S : State K ℓ) :
    gateRound pl pr f c t u S = Function.update S t fun i =>
      S t i - c * eval (Sum.elim ((u : K) • S (t + 1) + vl) ((u : K) • S (t + 2) + vr))
        (gatePoly f i) := by
  have h1 := add_one_ne t
  have h2 := add_two_ne t
  have h21 := add_two_ne_add_one t
  funext r i
  simp only [gateRound, hl, hr, scale, Function.update_apply]
  by_cases hrt : r = t
  · subst hrt
    simp [h1.symm, h2.symm, h21, h21.symm]
  by_cases hr1 : r = t + 1
  · subst hr1
    simp [h1, h21.symm]
  by_cases hr2 : r = t + 2
  · subst hr2
    simp [h2, h21]
  simp [hrt, hr1, hr2]

/-- The rounds for all units in `us` change only the target register, by `c` times the sum of
the gate's extension at the masked children's values. -/
theorem foldl_gateRound_eq {pl pr : K → Fin 3 → State K ℓ → State K ℓ} {vl vr : Fin ℓ → K}
    (hl : ∀ c t S, pl c t S = Function.update S t (S t + c • vl))
    (hr : ∀ c t S, pr c t S = Function.update S t (S t + c • vr))
    (f : (Fin ℓ → Bool) → (Fin ℓ → Bool) → Fin ℓ → Bool) (c : K) (t : Fin 3) (us : List Kˣ)
    (S : State K ℓ) :
    us.foldl (fun S u => gateRound pl pr f c t u S) S = Function.update S t fun i =>
      S t i - c * (us.map fun u : Kˣ =>
        eval (Sum.elim ((u : K) • S (t + 1) + vl) ((u : K) • S (t + 2) + vr))
          (gatePoly f i)).sum := by
  induction us generalizing S with
  | nil => simp
  | cons u us ih =>
    rw [List.foldl_cons, gateRound_eq hl hr, ih, Function.update_of_ne (add_one_ne t),
      Function.update_of_ne (add_two_ne t), Function.update_idem, Function.update_self]
    congr 1
    funext i
    simp only [List.map_cons, List.sum_cons]
    ring

variable [Fintype K]

/-- **Correctness of the Cook–Mertz procedure.** If `us` enumerates the units of `K` without
repetition and `2ℓ < |K| - 1`, then the procedure adds `c` times the value of the tree to the
target register and leaves the other registers unchanged, whatever their initial contents. -/
theorem proc_eq {us : List Kˣ} (hnd : us.Nodup) (hmem : ∀ u, u ∈ us)
    (hK : 2 * ℓ < Fintype.card K - 1) {h : ℕ} (T : Tree ℓ h) (c : K) (t : Fin 3)
    (S : State K ℓ) : proc us T c t S = Function.update S t (S t + c • embed T.eval) := by
  classical
  induction T generalizing c t S with
  | leaf v => rfl
  | node f l r ihl ihr =>
    rw [proc, foldl_gateRound_eq ihl ihr]
    congr 1
    funext i
    have huniv : us.toFinset = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr fun u => List.mem_toFinset.mpr (hmem u)
    have hdeg : (gatePoly (K := K) f i).totalDegree < Fintype.card K - 1 :=
      (totalDegree_multilinearExtension_le _).trans_lt <| by simpa [two_mul] using hK
    rw [← List.sum_toFinset _ hnd, huniv]
    have hsum := FiniteField.sum_units_eval_mul_add hdeg
      (Sum.elim (S (t + 1)) (S (t + 2))) (Sum.elim (embed l.eval) (embed r.eval))
    have hpt (u : Kˣ) :
        (Sum.elim ((u : K) • S (t + 1) + embed l.eval) ((u : K) • S (t + 2) + embed r.eval)) =
          fun j => (u : K) * Sum.elim (S (t + 1)) (S (t + 2)) j +
            Sum.elim (embed l.eval) (embed r.eval) j := by
      funext j; cases j <;> rfl
    have hbits : Sum.elim (embed (K := K) l.eval) (embed r.eval) =
        fun j => bitVal K (Sum.elim l.eval r.eval j) := by
      funext j; cases j <;> rfl
    have hunmask : ∑ u : Kˣ, eval (Sum.elim ((u : K) • S (t + 1) + embed l.eval)
        ((u : K) • S (t + 2) + embed r.eval)) (gatePoly f i) =
          -eval (Sum.elim (embed l.eval) (embed r.eval)) (gatePoly f i) := by
      simp only [hpt]
      exact hsum
    rw [hunmask, hbits, gatePoly, eval_multilinearExtension]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Tree.eval_node, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, embed]
    ring

/-- Started from zero registers, the procedure leaves the value of the tree in the target
register. -/
theorem proc_zero {us : List Kˣ} (hnd : us.Nodup) (hmem : ∀ u, u ∈ us)
    (hK : 2 * ℓ < Fintype.card K - 1) {h : ℕ} (T : Tree ℓ h) (t : Fin 3) :
    proc us T 1 t 0 t = embed T.eval := by
  simp [proc_eq hnd hmem hK]

/-- **Tree Evaluation by the Cook–Mertz procedure.** Run over the units of `K` in any order with
`2ℓ < |K| - 1`, from zero registers, the procedure computes the value of the tree into the
target register. -/
theorem embed_eval_eq_proc [DecidableEq K] (hK : 2 * ℓ < Fintype.card K - 1) {h : ℕ} (T : Tree ℓ h)
    (t : Fin 3) : embed T.eval = proc (Finset.univ : Finset Kˣ).toList T 1 t 0 t :=
  (proc_zero (Finset.nodup_toList _) (fun _ => Finset.mem_toList.mpr (Finset.mem_univ _)) hK T
    t).symm

end Cslib.TreeEval
