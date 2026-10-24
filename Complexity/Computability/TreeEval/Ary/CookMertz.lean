/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Basic
public import Complexity.Foundations.BooleanAnalysis.MultilinearExtension
public import Complexity.Foundations.FieldTheory.Finite.UnitSum

/-!
# The Cook–Mertz procedure for Tree Evaluation with fan-in `d`

This generalizes the binary procedure `Cslib.TreeEval.proc` to fan-in `d`; at `d = 2` it is that
procedure step for step (`Cslib.TreeEval.Ary.proc_ofBinary`, proved beside the binary procedure,
which derives its correctness from this file). The procedure keeps `d + 1` registers, each
holding `ℓ` elements of a finite field `K`, as global storage shared by all levels of the
recursion. Called on a subtree, a coefficient `c` and a target register `t`, it adds `c` times the
value of the subtree (read as `0`/`1` field elements) to register `t` and leaves the other `d`
registers unchanged, whatever their contents.

The child `j` of a target `t` uses the register `reg t j = t + (j + 1)`, so the `d` children use
exactly the registers other than `t`; for `d = 2` these are the registers `t + 1` and `t + 2` of
the binary procedure. At an internal node with gate `f`, the procedure runs one round for every
unit `u` of `K`. A round scales the child registers by `u`, adds the children's values to them by
recursive calls, subtracts `c` times the multilinear extension of `f` at the masked values from
register `t`, and then undoes the recursive calls and the scaling. Summed over all units, the masks
cancel (`FiniteField.sum_units_eval_mul_add`), because the extension has degree at most
`d * ℓ < |K| - 1`, and register `t` has gained `c • f (v₀, …, v_{d-1})`.

This file proves correctness only; space bounds are separate.

## Main definitions

* `Cslib.TreeEval.embed`: an `ℓ`-bit value read as `0`/`1` field elements, for any fan-in.
* `Cslib.TreeEval.Ary.reg`: the register of a child.
* `Cslib.TreeEval.Ary.gatePoly`: the multilinear extension of an output bit of a gate.
* `Cslib.TreeEval.Ary.proc`: the procedure, parametrized by an enumeration of the units of `K`.

## Main results

* `Cslib.TreeEval.Ary.proc_eq`: the procedure adds `c` times the value of the tree to the target
  register and leaves the other registers unchanged.
* `Cslib.TreeEval.Ary.proc_zero`: started from zero registers, it leaves the value of the tree in
  the target register.
* `Cslib.TreeEval.Ary.embed_eval_eq_proc`: the same, for the canonical enumeration of the units.

## References

* [J. Cook and I. Mertz, *Tree Evaluation is in Space O(log n · log log n)*][CookMertz2024],
  Lemma 13 and Theorem 10, for fan-in `d`.
* [O. Goldreich, *On the Cook–Mertz Tree Evaluation procedure*][Goldreich2024TreeEval],
  Algorithm 1, whose signed recursive calls are followed here.
-/

@[expose] public section

open MvPolynomial Cslib.BitString

namespace Cslib.TreeEval

variable {K : Type*} [Field K] {d ℓ : ℕ}

/-- An `ℓ`-bit value read as `0`/`1` field elements. -/
def embed (v : Fin ℓ → Bool) : Fin ℓ → K := fun i => bitVal K (v i)

namespace Ary

/-- The global storage: `d + 1` registers of `ℓ` field elements. -/
abbrev State (K : Type*) (d ℓ : ℕ) := Fin (d + 1) → Fin ℓ → K

/-- The register of child `j` when the target register is `t`. -/
def reg (t : Fin (d + 1)) (j : Fin d) : Fin (d + 1) := t + j.succ

private theorem reg_ne (t : Fin (d + 1)) (j : Fin d) : reg t j ≠ t := by
  simp [reg, Fin.succ_ne_zero]

theorem reg_injective (t : Fin (d + 1)) : Function.Injective (reg t) := by
  intro a b h
  simpa [reg] using h

/-- The children's registers are exactly the registers other than the target. -/
private theorem mem_map_reg_finRange {t r : Fin (d + 1)} :
    r ∈ (List.finRange d).map (reg t) ↔ r ≠ t := by
  refine ⟨?_, fun hr => ?_⟩
  · simp only [List.mem_map, List.mem_finRange, true_and]
    rintro ⟨j, rfl⟩
    exact reg_ne t j
  · have h0 : r - t ≠ 0 := sub_ne_zero.mpr hr
    refine List.mem_map.mpr ⟨(r - t).pred h0, List.mem_finRange _, ?_⟩
    simp [reg]

/-- The value of the child whose register is `r`, and `0` at the target register. -/
def childVal (t : Fin (d + 1)) (v : Fin d → Fin ℓ → K) (r : Fin (d + 1)) : Fin ℓ → K :=
  if h : r - t = 0 then 0 else v ((r - t).pred h)

@[simp] theorem childVal_reg (t : Fin (d + 1)) (v : Fin d → Fin ℓ → K) (j : Fin d) :
    childVal t v (reg t j) = v j := by
  simp [childVal, reg, Fin.succ_ne_zero]

/-- The multilinear extension of output bit `i` of a gate, in the bits of all its inputs. -/
noncomputable def gatePoly (f : Gate d ℓ) (i : Fin ℓ) : MvPolynomial (Fin d × Fin ℓ) K :=
  multilinearExtension fun z => bitVal K (f (fun j k => z (j, k)) i)

/-- Multiply register `r` by `a`. -/
def scale (r : Fin (d + 1)) (a : K) (S : State K d ℓ) : State K d ℓ :=
  Function.update S r (a • S r)

/-- The update of a round at a gate `f`: subtract `c` times the gate's extension at the child
registers from register `t`. -/
noncomputable def gateUpdate (f : Gate d ℓ) (c : K) (t : Fin (d + 1)) (S : State K d ℓ) :
    State K d ℓ :=
  Function.update S t fun i => S t i - c * eval (fun q => S (reg t q.1) q.2) (gatePoly f i)

/-- One round of the procedure at a gate `f`, for the unit `u`, given procedures `p j` for the
subtrees. The target is `t`, and the child registers `reg t j` hold the masks. -/
noncomputable def gateRound (p : Fin d → K → Fin (d + 1) → State K d ℓ → State K d ℓ)
    (f : Gate d ℓ) (c : K) (t : Fin (d + 1)) (u : Kˣ) (S : State K d ℓ) : State K d ℓ :=
  let S := (List.finRange d).foldl (fun S j => p j 1 (reg t j) (scale (reg t j) (u : K) S)) S
  let S := gateUpdate f c t S
  (List.finRange d).foldl
    (fun S j => scale (reg t j) ((u⁻¹ : Kˣ) : K) (p j (-1) (reg t j) S)) S

/-- The Cook–Mertz procedure: add `c` times the value of the tree to register `t`. At a gate it
runs one `gateRound` for every unit in the enumeration `us`. -/
noncomputable def proc (us : List Kˣ) :
    {h : ℕ} → Tree d ℓ h → K → Fin (d + 1) → State K d ℓ → State K d ℓ
  | _, .leaf v, c, t, S => Function.update S t (S t + c • embed v)
  | _, .node f ch, c, t, S =>
      us.foldl (fun S u => gateRound (fun j => proc us (ch j)) f c t u S) S

omit [Field K] in
/-- Updating each child register in turn, as a function of its previous content, updates all
registers other than the target. -/
private theorem foldl_update_reg (t : Fin (d + 1)) (g : Fin (d + 1) → (Fin ℓ → K) → Fin ℓ → K)
    (l : List (Fin d)) (hl : l.Nodup) (S : State K d ℓ) :
    l.foldl (fun S j => Function.update S (reg t j) (g (reg t j) (S (reg t j)))) S =
      fun r => if r ∈ l.map (reg t) then g r (S r) else S r := by
  induction l generalizing S with
  | nil => simp
  | cons j l ih =>
    obtain ⟨hj, hl⟩ := List.nodup_cons.mp hl
    rw [List.foldl_cons, ih hl]
    funext r
    by_cases hr : r = reg t j
    · subst hr
      have hn : reg t j ∉ l.map (reg t) := by
        rw [List.mem_map]
        rintro ⟨k, hk, hkj⟩
        exact hj (reg_injective t hkj ▸ hk)
      simp [hn]
    · simp [List.mem_cons, hr]

/-- A round, when all subtree procedures meet their specification, changes only the target
register, subtracting `c` times the gate's extension at the masked children's values. -/
private theorem gateRound_eq {p : Fin d → K → Fin (d + 1) → State K d ℓ → State K d ℓ}
    {v : Fin d → Fin ℓ → K} (hp : ∀ j c t S, p j c t S = Function.update S t (S t + c • v j))
    (f : Gate d ℓ) (c : K) (t : Fin (d + 1)) (u : Kˣ) (S : State K d ℓ) :
    gateRound p f c t u S = Function.update S t fun i =>
      S t i - c * eval (fun q => (u : K) * S (reg t q.1) q.2 + v q.1 q.2) (gatePoly f i) := by
  have hnd := List.nodup_finRange d
  have e1 (S : State K d ℓ) :
      (List.finRange d).foldl (fun S j => p j 1 (reg t j) (scale (reg t j) (u : K) S)) S =
        fun r => if r ≠ t then (u : K) • S r + childVal t v r else S r := by
    have h1 : (fun S j => p j 1 (reg t j) (scale (reg t j) (u : K) S)) =
        fun (S : State K d ℓ) j => Function.update S (reg t j)
          ((fun r x => (u : K) • x + childVal t v r) (reg t j) (S (reg t j))) := by
      funext S j
      simp [hp, scale]
    rw [h1, foldl_update_reg t (fun r x => (u : K) • x + childVal t v r) _ hnd]
    simp only [mem_map_reg_finRange]
  have e3 (S : State K d ℓ) :
      (List.finRange d).foldl
          (fun S j => scale (reg t j) ((u⁻¹ : Kˣ) : K) (p j (-1) (reg t j) S)) S =
        fun r => if r ≠ t then ((u⁻¹ : Kˣ) : K) • (S r - childVal t v r) else S r := by
    have h3 : (fun S j => scale (reg t j) ((u⁻¹ : Kˣ) : K) (p j (-1) (reg t j) S)) =
        fun (S : State K d ℓ) j => Function.update S (reg t j)
          ((fun r x => ((u⁻¹ : Kˣ) : K) • (x - childVal t v r)) (reg t j) (S (reg t j))) := by
      funext S j
      simp [hp, scale, sub_eq_add_neg]
    rw [h3, foldl_update_reg t (fun r x => ((u⁻¹ : Kˣ) : K) • (x - childVal t v r)) _ hnd]
    simp only [mem_map_reg_finRange]
  dsimp only [gateRound]
  rw [e1, e3]
  funext r i
  by_cases hr : r = t
  · subst hr
    simp [gateUpdate, reg_ne]
  · simp [gateUpdate, hr]

/-- The rounds for all units in `us` change only the target register, subtracting `c` times the
sum of the gate's extension at the masked children's values. -/
private theorem foldl_gateRound_eq {p : Fin d → K → Fin (d + 1) → State K d ℓ → State K d ℓ}
    {v : Fin d → Fin ℓ → K} (hp : ∀ j c t S, p j c t S = Function.update S t (S t + c • v j))
    (f : Gate d ℓ) (c : K) (t : Fin (d + 1)) (us : List Kˣ) (S : State K d ℓ) :
    us.foldl (fun S u => gateRound p f c t u S) S = Function.update S t fun i =>
      S t i - c * (us.map fun u : Kˣ =>
        eval (fun q => (u : K) * S (reg t q.1) q.2 + v q.1 q.2) (gatePoly f i)).sum := by
  induction us generalizing S with
  | nil => simp
  | cons u us ih =>
    rw [List.foldl_cons, gateRound_eq hp, ih, Function.update_idem, Function.update_self]
    congr 1
    funext i
    have hreg (j : Fin d) : Function.update S t (fun i =>
        S t i - c * eval (fun q => (u : K) * S (reg t q.1) q.2 + v q.1 q.2) (gatePoly f i))
          (reg t j) = S (reg t j) := Function.update_of_ne (reg_ne t j) _ _
    simp only [hreg, List.map_cons, List.sum_cons]
    ring

variable [Fintype K]

/-- **Correctness of the Cook–Mertz procedure for fan-in `d`.** If `us` enumerates the units of
`K` without repetition and `d * ℓ < |K| - 1`, then the procedure adds `c` times the value of the
tree to the target register and leaves the other registers unchanged, whatever their initial
contents. -/
theorem proc_eq {us : List Kˣ} (hnd : us.Nodup) (hmem : ∀ u, u ∈ us)
    (hK : d * ℓ < Fintype.card K - 1) {h : ℕ} (T : Tree d ℓ h) (c : K) (t : Fin (d + 1))
    (S : State K d ℓ) : proc us T c t S = Function.update S t (S t + c • embed T.eval) := by
  classical
  induction T generalizing c t S with
  | leaf v => rfl
  | node f ch ih =>
    rw [proc, foldl_gateRound_eq (v := fun j => embed (ch j).eval) fun j => ih j]
    congr 1
    funext i
    have hdeg : (gatePoly (K := K) f i).totalDegree < Fintype.card K - 1 :=
      (totalDegree_multilinearExtension_le _).trans_lt <| by simpa using hK
    rw [← List.sum_toFinset _ hnd, show us.toFinset = Finset.univ by ext; simp [hmem]]
    have hsum := FiniteField.sum_units_eval_mul_add hdeg
      (fun q => S (reg t q.1) q.2) (fun q => bitVal K ((ch q.1).eval q.2))
    simp only [embed] at hsum ⊢
    rw [hsum, gatePoly, eval_multilinearExtension]
    simp [embed]

/-- Started from zero registers, the procedure leaves the value of the tree in the target
register. -/
theorem proc_zero {us : List Kˣ} (hnd : us.Nodup) (hmem : ∀ u, u ∈ us)
    (hK : d * ℓ < Fintype.card K - 1) {h : ℕ} (T : Tree d ℓ h) (t : Fin (d + 1)) :
    proc us T 1 t 0 t = embed T.eval := by
  simp [proc_eq hnd hmem hK]

/-- **Tree Evaluation with fan-in `d` by the Cook–Mertz procedure.** Run over the units of `K` in
any order with `d * ℓ < |K| - 1`, from zero registers, the procedure computes the value of the
tree into the target register. -/
theorem embed_eval_eq_proc [DecidableEq K] (hK : d * ℓ < Fintype.card K - 1) {h : ℕ}
    (T : Tree d ℓ h) (t : Fin (d + 1)) :
    embed T.eval = proc (Finset.univ : Finset Kˣ).toList T 1 t 0 t :=
  (proc_zero (Finset.nodup_toList _) (fun _ => Finset.mem_toList.mpr (Finset.mem_univ _)) hK T
    t).symm

end Ary

end Cslib.TreeEval
